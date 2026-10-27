module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionShape
public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers
import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LocalAnalysis.ABGTheoremB.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_le_normalizer_map_subtype {H : Subgroup G} {X K : Subgroup H}
    (hXK : X ≤ normalizer (K : Set H)) :
    X.map H.subtype ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_normalizer_iff]
  intro g
  have hxK := mem_normalizer_iff.mp (hXK hx)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨x * k * x⁻¹, (hxK k).1 hk, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨x⁻¹ * k * x, (hxK (x⁻¹ * k * x)).2 ?_, ?_⟩
    · rwa [show x * (x⁻¹ * k * x) * x⁻¹ = k by group]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

theorem card_le_of_isCyclic_of_centralizer_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P R A : Subgroup G} (hP : IsPGroup p P) (hRP : R ≤ P)
    (hPR : P ≤ normalizer (R : Set G)) (hC : P ⊓ centralizer (R : Set G) ≤ R) (hR : IsCyclic R)
    (hAP : A ≤ P) (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  classical
  have hprime : p.Prime := Fact.out
  have hRn : (R.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hRP).2 hPR
  have hRc : IsCyclic (R.subgroupOf P) :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hRP).symm.toMonoidHom
      (subgroupOfEquivOfLe hRP).symm.surjective
  have hRcomm : ∀ x y : R.subgroupOf P, x * y = y * x := by
    intro x y
    let _ : CommGroup (R.subgroupOf P) := IsCyclic.commGroup
    exact mul_comm x y
  have hAut : IsCyclic (MulAut (R.subgroupOf P)) := by
    obtain ⟨m, hm⟩ := (hP.to_subgroup (R.subgroupOf P)).exists_card_eq
    have h := ZMod.isCyclic_units_of_prime_pow p hprime hp2 m
    rw [← hm] at h
    exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv (R.subgroupOf P)).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv (R.subgroupOf P)).symm.surjective
  let φ : P →* MulAut (R.subgroupOf P) := MulAut.conjNormal
  have hker : φ.ker = R.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [mem_subgroupOf]
      refine hC ⟨x.2, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have h1 := congrArg (fun f : MulAut (R.subgroupOf P) =>
        (((f ⟨⟨r, hRP hr⟩, hr⟩ : R.subgroupOf P) : P) : G)) hx
      change (x : G) * r * (x : G)⁻¹ = r at h1
      calc r * x = ((x : G) * r * (x : G)⁻¹) * x := by rw [h1]
        _ = x * r := by group
    · intro hx
      refine MulEquiv.ext fun r => Subtype.ext ?_
      change x * (r : P) * x⁻¹ = r
      have h := congrArg Subtype.val (hRcomm ⟨x, hx⟩ r)
      change x * (r : P) = (r : P) * x at h
      rw [h, mul_inv_cancel_right]
  have hquot : IsCyclic (P ⧸ R.subgroupOf P) := by
    have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨hT, -⟩ := CFSG.GroupTheory.SteinbergBK.odd_metacyclic_torsion_counts
    (hprime.odd_of_ne_two hp2) hP (R.subgroupOf P) hRc hquot
  have h1 := hT 1
  simp only [pow_one, mul_one] at h1
  have hsub : ((A.subgroupOf P : Subgroup P) : Set P) ⊆ {x : P | x ^ p = 1} := by
    intro x hx
    apply Subtype.ext
    simpa using hA.2 x hx
  have hcard : Nat.card A = ((A.subgroupOf P : Subgroup P) : Set P).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).symm
  rw [hcard]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h1

omit [Finite G] in
theorem le_normalizer_inf_Op_p'p {p : ℕ} {P : Sylow p G} {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) :
    (P : Subgroup G) ≤ normalizer
      ((((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G) := by
  have hL₀n : (CFSG.Op_p'p p H).Normal := CFSG.Op_p'p_normal p H
  have hmemPH : ∀ g (hg : g ∈ H), (⟨g, hg⟩ : H) ∈ (P.subtype hPH : Subgroup H) ↔
      g ∈ (P : Subgroup G) := by
    intro g hg
    rw [Sylow.coe_subtype, mem_subgroupOf]
  have hPQ : (P.subtype hPH : Subgroup H) ≤
      normalizer (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H : Subgroup H) : Set H) := by
    refine le_trans (le_inf le_normalizer ?_) inf_normalizer_le_normalizer_inf
    rw [normalizer_eq_top_iff.mpr hL₀n]
    exact le_top
  intro g hg
  exact map_subtype_le_normalizer_map_subtype hPQ ⟨⟨g, hPH hg⟩, (hmemPH g (hPH hg)).2 hg, rfl⟩

omit [Finite G] in
theorem map_inf_Op_p'p_le {p : ℕ} {P : Sylow p G} {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) :
    ((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype ≤ P := by
  rintro _ ⟨q, hq, rfl⟩
  have h := (mem_inf.mp hq).1
  rwa [Sylow.coe_subtype, mem_subgroupOf] at h

theorem le_of_normalizer_inf_Op_p'p_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M)
    (hNR : normalizer ((((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype :
      Subgroup G) : Set G) ≤ M) : H ≤ M := by
  classical
  have hprime : p.Prime := Fact.out
  have hK₀n : (CFSG.pPrimeCore p H).Normal := CFSG.pPrimeCore_normal
  have hK₀L₀ : CFSG.pPrimeCore p H ≤ CFSG.Op_p'p p H := CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
  obtain ⟨R₁, hR₁⟩ := CFSG.Glauberman.sylow_inf_normal (P.subtype hPH) (N := CFSG.Op_p'p p H)
  have hR₁map : (R₁ : Subgroup (CFSG.Op_p'p p H)).map (CFSG.Op_p'p p H).subtype =
      ((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H) := by
    rw [hR₁, map_subgroupOf_eq_of_le inf_le_right]
  set Q₀ : Subgroup H := (P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H with hQ₀
  have hL₀eq : Q₀ ⊔ CFSG.pPrimeCore p H = CFSG.Op_p'p p H := by
    have hquot : IsPGroup p (CFSG.Op_p'p p H ⧸ (CFSG.pPrimeCore p H).subgroupOf
        (CFSG.Op_p'p p H)) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx : QuotientGroup.mk' (CFSG.pPrimeCore p H) (x : H) ∈
          CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H) := x.2
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup ⟨_, hx⟩
      refine ⟨n, ?_⟩
      have hn' : (QuotientGroup.mk' (CFSG.pPrimeCore p H) (x : H)) ^ p ^ n = 1 :=
        congrArg Subtype.val hn
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn'
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      simpa using hn'
    have hsup := normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient p hprime
      ((CFSG.pPrimeCore p H).subgroupOf (CFSG.Op_p'p p H)) inferInstance hquot R₁
    have himage := congrArg (fun S : Subgroup (CFSG.Op_p'p p H) =>
      S.map (CFSG.Op_p'p p H).subtype) hsup
    rw [Subgroup.map_sup, hR₁map, map_subgroupOf_eq_of_le hK₀L₀, ← MonoidHom.range_eq_map,
      range_subtype] at himage
    exact himage
  have hfrat := Sylow.normalizer_sup_eq_top R₁
  rw [hR₁map] at hfrat
  have htop : (⊤ : Subgroup H) ≤ normalizer (Q₀ : Set H) ⊔ CFSG.pPrimeCore p H := by
    rw [← hfrat]
    refine sup_le le_sup_left ?_
    rw [← hL₀eq]
    exact sup_le (le_sup_of_le_left le_normalizer) le_sup_right
  intro h hh
  have himage : h ∈ (normalizer (Q₀ : Set H) ⊔ CFSG.pPrimeCore p H).map H.subtype :=
    ⟨⟨h, hh⟩, htop (mem_top _), rfl⟩
  rw [Subgroup.map_sup] at himage
  exact (sup_le ((map_subtype_le_normalizer_map_subtype le_rfl).trans hNR) hKM) himage

theorem ExtremalObstruction.le_of_two_le_pRank_inf_Op_p'p (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hR2 : 2 ≤ CFSG.Open.pRank p
      (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype)) : H ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hM := hext.obstruction.1
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  have hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M := by
    have hcop : ¬ p ∣ Nat.card ((CFSG.pPrimeCore p H).map H.subtype) := by
      rw [card_map_of_injective H.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hprime).1 CFSG.pPrimeCore_coprime_card
    exact le_of_elemAbelian_normalizes hS hp hM hAP hA hAc hcop
      ((hAP.trans hPH).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype H _))
  exact le_of_normalizer_inf_Op_p'p_le hPH hKM
    (hext.normalizer_le_of_normal hPD (map_inf_Op_p'p_le hPH) (le_normalizer_inf_Op_p'p hPH) hR2)

theorem inf_centralizer_le_of_isPConstrained {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) (hH : CFSG.ABGLocalTools.IsPConstrained p H) :
    (P : Subgroup G) ⊓ centralizer
        ((((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G) ≤
      ((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype := by
  classical
  obtain ⟨R₁, hR₁⟩ := CFSG.Glauberman.sylow_inf_normal (P.subtype hPH) (N := CFSG.Op_p'p p H)
  have hR₁map : (R₁ : Subgroup (CFSG.Op_p'p p H)).map (CFSG.Op_p'p p H).subtype =
      ((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H) := by
    rw [hR₁, map_subgroupOf_eq_of_le inf_le_right]
  have hcent := hH _ ⟨R₁, hR₁map⟩
  have hmemPH : ∀ g (hg : g ∈ H), (⟨g, hg⟩ : H) ∈ (P.subtype hPH : Subgroup H) ↔
      g ∈ (P : Subgroup G) := by
    intro g hg
    rw [Sylow.coe_subtype, mem_subgroupOf]
  rintro g ⟨hgP, hgC⟩
  have hg' : (⟨g, hPH hgP⟩ : H) ∈
      centralizer (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H : Subgroup H) : Set H) := by
    rw [mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    exact mem_centralizer_iff.mp hgC q ⟨q, hq, rfl⟩
  exact ⟨⟨g, hPH hgP⟩, ⟨(hmemPH g (hPH hgP)).2 hgP, hcent hg'⟩, rfl⟩

theorem two_le_pRank_inf_Op_p'p_of_not_isCyclic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Sylow p G} {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hRc : ¬ IsCyclic (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype)) :
    2 ≤ CFSG.Open.pRank p (((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype) := by
  have hprime : p.Prime := Fact.out
  set R : Subgroup G := ((P.subtype hPH : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype
  have hRp : IsPGroup p R := P.isPGroup'.to_le (map_inf_Op_p'p_le hPH)
  obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hprime.odd_of_ne_two hp2) hRp hRc
  have hBe : CFSG.IsElementaryAbelian p (B.map R.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨B.map R.subtype, map_subtype_le B,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hBe, ?_⟩
  rw [card_map_of_injective R.subtype_injective, hBc]

theorem ExtremalObstruction.le_of_isPConstrained (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hH : CFSG.ABGLocalTools.IsPConstrained p H) : H ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hext.obstruction.1).2
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  refine hext.le_of_two_le_pRank_inf_Op_p'p hS hp hPD hPH
    (two_le_pRank_inf_Op_p'p_of_not_isCyclic hodd hPH fun hRc => ?_)
  have hle := card_le_of_isCyclic_of_centralizer_le hodd P.isPGroup' (map_inf_Op_p'p_le hPH)
    (le_normalizer_inf_Op_p'p hPH) (inf_centralizer_le_of_isPConstrained hPH hH) hRc hAP hA
  rw [hAc] at hle
  have := (Nat.pow_le_pow_iff_right hprime.one_lt).1 hle
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
