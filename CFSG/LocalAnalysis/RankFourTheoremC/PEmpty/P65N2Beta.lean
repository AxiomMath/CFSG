module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Alpha
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiCoord
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BTransport
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

theorem plane63_of_plane65' {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A}
    {X : Subgroup A} {x z : A} (h : Plane65 p P X x z) (hx : x ∈ X) (hz : z ∈ X) :
    Plane63 p ↥X (P.subtype h.sylow_le) ⟨x, hx⟩ ⟨z, hz⟩ := by
  have hprime := h.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  refine ⟨hprime, h.five_le, h.catalog, ?_, ?_, ?_, ?_, ?_, h.perfect⟩
  · exact smallRankPlane_subgroupOf h.sylow_le hx hz h.plane
  · rw [mem_centralizer_iff]
    intro g hg
    exact Subtype.ext (mem_centralizer_iff.mp h.z_central (g : A) hg)
  · have h4 := h.four_le
    change 4 ≤ Open.pRank p ((P : Subgroup A).subgroupOf X)
    rwa [pRank_subgroupOf hprime.one_lt h.sylow_le]
  · calc Open.pRank p (centralizer ({(⟨x, hx⟩ : X)} : Set X))
        = Open.pRank p ((centralizer ({(⟨x, hx⟩ : X)} : Set X)).map X.subtype) :=
          (pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank p (centralizer ({x} : Set A)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := h.rank_centralizer
  · set x' : X := ⟨x, hx⟩ with hx'
    have hPM := h.sylow_le
    have hB : (centralizer ({x'} : Set X)).map X.subtype = X ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPM : Subgroup X) ⊓ centralizer ({x'} : Set X)).map X.subtype =
        (P : Subgroup A) ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPM hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le h.sylow_centralizer (inf_le_inf_right _ hPM)
      inf_le_right

section TypeLevel

variable {p f : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Sylow p Y} {x z : Y}

theorem p_le_pRank_normalizer_of_beta (hβ : KFactBetaStructure) (hf : f.Prime) (hfp : f ≠ p)
    (hpl : Plane63 p Y P x z)
    (hcomp : ∃ L K : Subgroup (Y ⧸ primeComplementCore (G := Y) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K)
    {T : Subgroup Y} (hT : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) ⊤ T) :
    p ≤ Open.pRank p (normalizer (T : Set Y)) := by
  have hβs := hβ p Y P x z hpl hcomp
  have hp := hpl.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup Y := primeComplementCore (G := Y) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup Y) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hxB : x ∈ (zpowers x ⊔ zpowers z : Subgroup Y) := Subgroup.mem_sup_left (mem_zpowers x)
  have hzB : z ∈ (zpowers x ⊔ zpowers z : Subgroup Y) := Subgroup.mem_sup_right (mem_zpowers z)
  have hxp : x ^ p = 1 := hpl.plane.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hpl.plane.isElemAbelian.2 z hzB
  have hxz : x * z = z * x := by
    have := hpl.plane.isElemAbelian.1.is_comm.comm (⟨x, hxB⟩ : ↥(zpowers x ⊔ zpowers z))
      ⟨z, hzB⟩
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (zpowers x ⊔ zpowers z : Subgroup Y) = zpowers x := by
      rw [h, zpowers_one_eq_bot, sup_bot_eq]
    have h2 : Nat.card (zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    have h3 := hpl.plane.card_eq
    rw [h1] at h3
    have h4 : p ^ 2 ≤ p := h3 ▸ h2
    have h5 : 1 < p := hp.one_lt
    nlinarith
  have hzb1 : (z : Y ⧸ D) ≠ 1 := by
    intro h
    have hzD : z ∈ D := (QuotientGroup.eq_one_iff z).mp h
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    apply hD3
    rw [← hord, ← Subgroup.orderOf_mk z hzD]
    exact orderOf_dvd_natCard _
  have hxzb : (x : Y ⧸ D) * (z : Y ⧸ D) = (z : Y ⧸ D) * (x : Y ⧸ D) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxz]
  have hzpb : (z : Y ⧸ D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hzp, QuotientGroup.mk_one]
  have hT' := isMaxFInvariantIn_map hp hf hfp hD3 hB hT
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup Y).map (QuotientGroup.mk' D) =
      zpowers (x : Y ⧸ D) ⊔ zpowers (z : Y ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [hBmap] at hT'
  have hZ := hβs.centreless
  have hzL := hβs.z_mem_layer
  have hne := K62.π_ne_one hZ hxzb hzb1 hzL hβs.transitive
  have hN := zcoord_mem_normalizer hZ hp hf hfp hxzb hzL hβs.card_components hβs.transitive hT'
  obtain ⟨W, hWe, hWc, hWT⟩ := K62.exists_elemAbelian_of_coords hZ hp hzpb hzL hne hN
  rw [hβs.card_components] at hWc
  exact le_pRank_normalizer hp hf hfp hD3 hB hT hWe hWc hWT

end TypeLevel

section Ambient

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628 (rrBasic_conj_centralizer)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (exists_isComponentOf_of_not_hasPrimeConstraint)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A} {X : Subgroup A} {x z : A}

theorem card_le_of_cyclic_type {G : Type*} [Group G] [Finite G] [IsCyclic G] {p : ℕ} (hp : 0 < p)
    {T : Subgroup G} (hT : ∀ t ∈ T, t ^ p = 1) : Nat.card T ≤ p := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h := IsCyclic.card_pow_eq_one_le (α := G) hp
  have h2 : (Finset.univ : Finset ↥T).card ≤
      (Finset.univ.filter (fun a : G => a ^ p = 1)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t : G)) ?_ ?_
    · intro t _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hT t t.2
    · intro a _ b _ hab
      exact Subtype.ext hab
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact h2.trans h

theorem card_le_of_conj_cyclic {p : ℕ} (hp : 0 < p) {H T : Subgroup A} (hH : IsCyclic H) {k : A}
    (hT : ∀ t ∈ T, k⁻¹ * t * k ∈ H) (hexp : ∀ t ∈ T, t ^ p = 1) : Nat.card T ≤ p := by
  have hTH : T.map (MulAut.conj k⁻¹).toMonoidHom ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply] using hT t ht
  have h1 := card_le_of_cyclic hp hH hTH (by
    rintro _ ⟨t, ht, rfl⟩
    show (k⁻¹ * t * k⁻¹⁻¹) ^ p = 1
    rw [conj_pow, hexp t ht]
    group)
  rwa [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective] at h1

theorem exists_mem_conj_le {p : ℕ} [Fact p.Prime] {S K T : Subgroup A}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) (hTK : T ≤ K) (hT : IsPGroup p T) :
    ∃ k ∈ K, ∀ y ∈ T, k⁻¹ * y * k ∈ S := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', hQ'⟩ := (hT.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hTK hy⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

theorem p65N2_beta (hβ : KFactBetaStructure) (hpl : Plane65 p P X x z)
    (hncon : ¬ HasPrimeConstraint (G := ↥X) p) (hnuniq : ¬ UniquePComponent p X)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {Fs R : Subgroup A}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hRp : IsPGroup p R)
    (hRidx : ¬ p ∣ (R.subgroupOf (X ⊓ normalizer (Fs : Set A))).index)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A)) :
    4 ≤ Open.pRank f X := by
  by_contra hlt
  push Not at hlt
  have hX3 : Open.pRank f X ≤ 3 := by omega
  haveI : Fact f.Prime := ⟨hf⟩
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : NeZero f := ⟨hf.ne_zero⟩
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  have hBX : zpowers x ⊔ zpowers z ≤ X := hBP.trans hPX
  have hpl63 := plane63_of_plane65' hpl hxX hzX
  obtain ⟨L₀, hL₀⟩ := exists_isComponentOf_of_not_hasPrimeConstraint hprime hncon
  have hL₀p : p ∣ Nat.card L₀ :=
    (cfg_of_plane63 hpl63).dvd_card_comp ⟨L₀, (CFSG.isComponent_iff_open L₀).2 hL₀⟩
  obtain ⟨K, hK, hKp, hKL⟩ : ∃ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
      IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ K ≠ L₀ := by
    by_contra hno
    push Not at hno
    exact hnuniq ⟨L₀, hL₀, hL₀p, hno⟩
  have hcomp : ∃ L K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K := ⟨K, L₀, hK, hL₀, hKL⟩
  have hT' := isMaxFInvariantIn_top hBX hF
  rw [← plane_eq_subgroupOf (⟨x, hxX⟩ : X) ⟨z, hzX⟩] at hT'
  have hkey := p_le_pRank_normalizer_of_beta hβ hf hfp hpl63 hcomp hT'
  rw [pRank_normalizer_subgroupOf hprime.one_lt hF.1.1] at hkey
  obtain ⟨E, hEN, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hprime hkey
  set N : Subgroup A := X ⊓ normalizer (Fs : Set A) with hN
  obtain ⟨χ, hχ⟩ := exists_rank_bound hf2 hprime hfp.symm hF.1.2.1 (N := N) inf_le_right
    (card_le_of_pRank_le hf hF.1.1 hX3)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let φ : ↥E →* (ZMod f)ˣ := χ.comp (Subgroup.inclusion hEN)
  have hrange : Nat.card φ.range ≤ p := by
    refine card_le_of_cyclic_type hprime.pos fun t ht => ?_
    obtain ⟨a, rfl⟩ := ht
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hEab.2 a a.2)
    rw [this, map_one]
  have hkerrange := Subgroup.card_ker_mul_card_range φ
  have hker4 : p ^ 4 ≤ Nat.card φ.ker := by
    have h1 : p ^ (p - 1) * p ≤ Nat.card φ.ker * p := by
      calc p ^ (p - 1) * p = Nat.card E := by
            rw [hEcard, ← pow_succ]
            congr 1
            have := hprime.pos
            omega
        _ = Nat.card φ.ker * Nat.card φ.range := hkerrange.symm
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hrange
    have h2 : p ^ (p - 1) ≤ Nat.card φ.ker := Nat.le_of_mul_le_mul_right h1 hprime.pos
    have h5 := hpl.five_le
    exact (Nat.pow_le_pow_right hprime.pos (by omega)).trans h2
  set E₁ : Subgroup A := φ.ker.map E.subtype with hE₁
  have hE₁card : Nat.card E₁ = Nat.card φ.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hE₁E : E₁ ≤ E := Subgroup.map_subtype_le _
  have hE₁N : E₁ ≤ N := hE₁E.trans hEN
  have hχE₁ : ∀ (a : A) (ha : a ∈ E₁), χ ⟨a, hE₁N ha⟩ = 1 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := ha
    exact he
  have h1 := hχ E₁ hE₁N (fun a ha b hb => hEc a (hE₁E ha) b (hE₁E hb))
    (fun a ha => hEab.2 a (hE₁E ha)) hχE₁
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p R N :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hRN, hRp, hRidx⟩
  have hE₁p : IsPGroup p E₁ := fun g =>
    ⟨1, Subtype.ext (by simpa using hEab.2 g.1 (hE₁E g.2))⟩
  obtain ⟨k, hkN, hk⟩ := exists_mem_conj_le hRsyl hE₁N hE₁p
  have h2 : Nat.card (E₁ ⊓ centralizer (Fs : Set A) : Subgroup A) ≤ p := by
    refine card_le_of_conj_cyclic hprime.pos hcyc (k := k) (fun t ht => ⟨hk t ht.1, ?_⟩)
      (fun t ht => hEab.2 t (hE₁E ht.1))
    have := rrBasic_conj_centralizer ((normalizer (Fs : Set A)).inv_mem (mem_inf.mp hkN).2) ht.2
    simpa using this
  have h3 : p ^ 4 ≤ p ^ 2 * p :=
    calc p ^ 4 ≤ Nat.card φ.ker := hker4
      _ = Nat.card E₁ := hE₁card.symm
      _ ≤ p ^ 2 * Nat.card (E₁ ⊓ centralizer (Fs : Set A) : Subgroup A) := h1
      _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ h2
  have h4 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hprime.one_lt (by norm_num)
  have h5 : p ^ 2 * p = p ^ 3 := by ring
  omega

end Ambient

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
