module

import CFSG.LocalAnalysis.RankFourTheoremC.PPointInvTwo
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (isSylowOf_two_of_invariantTwoMaximalWithin)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T)

variable {G : Type} [Group G] [Finite G]

theorem typeII_exists_rankTwoMaximal_of_reduced {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M U J : Subgroup G} (hU : IsPGroup p U)
    {X : Type} [Group X] (π : ↥J →* X) (hker : Nat.Coprime p (Nat.card π.ker))
    (V : Subgroup X) (hV2 : IsPGroup 2 V) (hVπ : V ≤ π.range)
    (hUV : ∀ u ∈ U, ∀ j : ↥J, π j ∈ V →
      ∃ hj : u * (j : G) * u⁻¹ ∈ J, π ⟨u * (j : G) * u⁻¹, hj⟩ ∈ V)
    (hVM : ¬ V ≤ (M.subgroupOf J).map π) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ĵ : Subgroup ↥J := V.comap π with hĴ
  set Ĵg : Subgroup G := Ĵ.map J.subtype with hĴg
  have hmap : ∀ u ∈ U, Ĵg.map (MulAut.conj u).toMonoidHom ≤ Ĵg := by
    intro u hu
    rintro _ ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨hj, hjV⟩ := hUV u hu c hc
    exact ⟨⟨u * (c : G) * u⁻¹, hj⟩, hjV, rfl⟩
  have hUĴ : U ≤ normalizer (Ĵg : Set G) := fun u hu => by
    rw [mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmap u hu) fun y hy => ?_
    have hz : (MulAut.conj u⁻¹) y ∈ Ĵg := hmap u⁻¹ (U.inv_mem hu) ⟨y, hy, rfl⟩
    exact ⟨_, hz, show u * (u⁻¹ * y * u⁻¹⁻¹) * u⁻¹ = y by group⟩
  have hcop : p.Coprime (Nat.card Ĵg) := by
    by_contra hnc
    have hdvd : p ∣ Nat.card Ĵg := by
      by_contra hnd
      exact hnc (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Ĵg) p hdvd
    obtain ⟨c, hc, hcg⟩ := g.2
    have hgp : (g : G) ^ p = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Subtype.val this
    have hcp : c ^ p = 1 := by
      apply J.subtype_injective
      rw [map_pow, hcg, map_one]
      exact hgp
    have hρc : π c = 1 := by
      obtain ⟨k, hk⟩ := hV2 ⟨π c, hc⟩
      have h1 : orderOf (π c) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hcp, map_one])
      have h2 : orderOf (π c) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop' : Nat.Coprime p (2 ^ k) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h1 h2)
    have hcOb : c ∈ π.ker := hρc
    have hordc : orderOf c = p := by
      rw [← Subgroup.orderOf_coe c]
      have hcg' : (c : G) = (g : G) := hcg
      rw [hcg', Subgroup.orderOf_coe, hg]
    have hdvdOb : p ∣ Nat.card π.ker := by
      have := orderOf_dvd_natCard (⟨c, hcOb⟩ : π.ker)
      rwa [Subgroup.orderOf_mk, hordc] at this
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hker hdvdOb)
  have hUbot : U ≤ normalizer (((⊥ : Subgroup G)) : Set G) := fun u _ => by
    rw [mem_normalizer_iff]
    intro h
    simp
  obtain ⟨W, -, hW⟩ := exists_invariantTwoMaximalWithin_containing U Ĵg ⊥ bot_le
    (IsPGroup.of_card (n := 0) (by simp)) hUbot
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 W Ĵg :=
    isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUĴ hcop hW
  have hĴJ : Ĵg ≤ J := Subgroup.map_subtype_le _
  have hWJ : W ≤ J := hW.1.trans hĴJ
  set W' : Subgroup J := W.subgroupOf J with hW'
  have hW'W : W'.map J.subtype = W := by
    rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWJ]
  have hW'Ĵ : CFSG.ABGLocalTools.IsSylowOf 2 W' Ĵ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff J, hW'W]
    exact hWs
  obtain ⟨Q, hQ⟩ := hW'Ĵ
  set φ : Ĵ →* V := (π.comp Ĵ.subtype).codRestrict V (fun c => c.2) with hφdef
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨c, hc⟩ := hVπ v.2
    exact ⟨⟨c, show π c ∈ V from by rw [hc]; exact v.2⟩, Subtype.ext hc⟩
  have hVtop : IsPGroup 2 ↥(⊤ : Subgroup V) := hV2.of_equiv Subgroup.topEquiv.symm
  have hQtop : (⊤ : Subgroup V) = (Q.mapSurjective hφ : Subgroup V) :=
    (Q.mapSurjective hφ).3 hVtop le_top
  have hVW : ∀ v ∈ V, ∃ c ∈ W', π c = v := by
    intro v hv
    have hv' : (⟨v, hv⟩ : V) ∈ (Q.mapSurjective hφ : Subgroup V) := by
      rw [← hQtop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hv'
    obtain ⟨q, hq, hqv⟩ := hv'
    refine ⟨(q : J), ?_, congrArg Subtype.val hqv⟩
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hWM : ¬ W ≤ M := by
    intro hWM
    refine hVM fun v hv => ?_
    obtain ⟨c, hcW, hcv⟩ := hVW v hv
    exact ⟨c, mem_subgroupOf.mpr (hWM (by rw [← hW'W]; exact ⟨c, hcW, rfl⟩)), hcv⟩
  obtain ⟨S₁, hWS, hS₁⟩ := exists_maximal_invariant_two_subgroup_containing U W hW.2.1 hW.2.2.1
  exact ⟨S₁, hS₁, fun h => hWM (hWS.trans h)⟩

theorem typeII_frattini_ker {Γ Q : Type*} [Group Γ] [Finite Γ] [Group Q] {p : ℕ} [Fact p.Prime]
    (ψ : Γ →* Q) (hcop : Nat.Coprime p (Nat.card ψ.ker)) {T : Subgroup Γ} (hT : IsPGroup p T)
    {j : Γ} (hj : ψ j ∈ Subgroup.normalizer ((T.map ψ : Subgroup Q) : Set Q)) :
    ∃ n ∈ Subgroup.normalizer (T : Set Γ), ψ n = ψ j := by
  classical
  set K := ψ.ker with hK
  set H : Subgroup Γ := K ⊔ T with hH
  have hTH : IsSylowOf p T H := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT, ?_⟩
    rw [hH, relIndex_sup_eq_relIndex_of_normal K T]
    intro hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
      (hdvd.trans (Subgroup.index_dvd_card (T.subgroupOf K)))
  set Tj : Subgroup Γ := T.map (MulAut.conj j).toMonoidHom with hTj
  have hmemTj : ∀ y, y ∈ Tj ↔ j⁻¹ * y * j ∈ T := by
    intro y
    rw [hTj, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hTjH : Tj ≤ H := by
    intro y hy
    rw [hmemTj] at hy
    have h1 : ψ y ∈ T.map ψ := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hj (ψ (j⁻¹ * y * j))).mp
        (Subgroup.mem_map_of_mem ψ hy)
      have e : ψ j * ψ (j⁻¹ * y * j) * (ψ j)⁻¹ = ψ y := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rwa [e] at h2
    obtain ⟨t', ht', hψ⟩ := h1
    have hk : y * t'⁻¹ ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, map_inv, ← hψ, mul_inv_cancel]
    have : y = (y * t'⁻¹) * t' := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk ht'
  have hcardTj : Nat.card Tj = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj j).injective
  have hTjS : IsSylowOf p Tj H := isSylowOf_of_card hTjH (by rw [hcardTj]; exact hTH.card_eq)
  obtain ⟨x, hxH, hx⟩ := CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hTH hTjS
  obtain ⟨k, hk, t, htT, hkt⟩ := Subgroup.mem_sup_of_normal_left.mp hxH
  subst hkt
  refine ⟨k⁻¹ * j, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ T ↔ j * y * j⁻¹ ∈ Tj := by
      rw [hmemTj]
      have : j⁻¹ * (j * y * j⁻¹) * j = y := by group
      rw [this]
    have h2 : (j * y * j⁻¹ ∈ Tj) ↔ (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) ∈ T := hx _
    have h3 : (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) =
        t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t := by group
    have h4 : t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t ∈ T ↔
        (k⁻¹ * j) * y * (k⁻¹ * j)⁻¹ ∈ T := by
      constructor
      · intro h
        have := T.mul_mem (T.mul_mem htT h) (T.inv_mem htT)
        simpa [mul_assoc] using this
      · intro h
        exact T.mul_mem (T.mul_mem (T.inv_mem htT) h) htT
    rw [h1, h2, h3, h4]
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]

theorem typeII_image_le_normalizer {p : ℕ} [Fact p.Prime] {J M T : Subgroup G}
    {X : Type} [Group X] [Finite X] (π : ↥J →* X)
    (hker : Nat.Coprime p (Nat.card π.ker)) (hkerM : ∀ j : ↥J, π j = 1 → (j : G) ∈ M)
    (hT : IsSylowOf p T J) (hNT : normalizer (T : Set G) ≤ M) (hJM : ¬ J ≤ M)
    (hmax : NormalizerMaximal p ↥π.range) (R : Sylow p X)
    (hTR : (T.subgroupOf J).map π ≤ (R : Subgroup X)) :
    (R : Subgroup X) ⊓ π.range = (T.subgroupOf J).map π ∧
      (M.subgroupOf J).map π ≤ normalizer (((R : Subgroup X) ⊓ π.range : Subgroup X) : Set X) := by
  set K : Subgroup X := π.range with hK
  let π' : ↥J →* ↥K := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  have hπ'ker : π'.ker = π.ker := MonoidHom.ker_rangeRestrict π
  obtain ⟨Tsyl, hTsyl⟩ := hT.exists_sylow_eq_subgroupOf
  let T' : Sylow p ↥K := Tsyl.mapSurjective hπ'
  have hT'coe : (T' : Subgroup ↥K) = (Tsyl : Subgroup ↥J).map π' := Sylow.coe_mapSurjective hπ' Tsyl
  have hT'map : (T' : Subgroup ↥K).map K.subtype = (T.subgroupOf J).map π := by
    rw [hT'coe, Subgroup.map_map, hTsyl]
    rfl
  have hRK : (R : Subgroup X) ⊓ K = (T.subgroupOf J).map π := by
    have hSyl : IsSylowOf p ((T.subgroupOf J).map π) K := ⟨T', hT'map⟩
    refine hSyl.eq_of_le (le_inf hTR ?_) inf_le_right R.isPGroup'.to_inf_left
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  refine ⟨hRK, ?_⟩
  set H : Subgroup ↥K := (M.subgroupOf J).map π' with hH
  have hNH : normalizer (T' : Set ↥K) ≤ H := by
    intro q hq
    obtain ⟨j, rfl⟩ := hπ' q
    have hj : π' j ∈ normalizer (((Tsyl : Subgroup ↥J).map π' : Subgroup ↥K) : Set ↥K) := by
      rw [← hT'coe]; exact hq
    obtain ⟨n, hn, hπn⟩ := typeII_frattini_ker π' (by rw [hπ'ker]; exact hker) Tsyl.isPGroup' hj
    have hnG : (n : G) ∈ normalizer (((Tsyl : Subgroup ↥J).map J.subtype : Subgroup G) : Set G) :=
      u3main_mem_normalizer_map hn
    rw [hTsyl, Subgroup.map_subgroupOf_eq_of_le hT.le] at hnG
    exact ⟨n, Subgroup.mem_subgroupOf.mpr (hNT hnG), hπn⟩
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hJM
    intro g hg
    have hmem : π' ⟨g, hg⟩ ∈ H := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hmem
    have hmg' : π m = π ⟨g, hg⟩ := congrArg Subtype.val hmg
    have hk : m⁻¹ * ⟨g, hg⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg', inv_mul_cancel]
    have h1 : ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) ∈ M := hkerM _ hk
    have h2 : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have : g = (m : G) * ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) := by simp
    rw [this]
    exact M.mul_mem h2 h1
  have hHeq : H = normalizer (T' : Set ↥K) := (hmax T' H hNH).resolve_right hHtop
  intro v hv
  obtain ⟨j, hj, rfl⟩ := hv
  have h1 : π' j ∈ H := ⟨j, hj, rfl⟩
  rw [hHeq] at h1
  have h2 := u3main_mem_normalizer_map h1
  rw [hT'map, ← hRK] at h2
  exact h2

theorem typeII_exists_reduction {C J N₀ : Subgroup G} (hCJ : C ≤ normalizer (J : Set G))
    (hCN : C ≤ normalizer (N₀ : Set G)) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (ρ : ↥C →* X), Function.Surjective ρ ∧
      ∀ c : ↥C, ρ c = 1 ↔ ∀ j ∈ J, (c : G) * j * (c : G)⁻¹ * j⁻¹ ∈ N₀ := by
  have hJc : ∀ c ∈ C, ∀ j ∈ J, c * j * c⁻¹ ∈ J := fun c hc j hj =>
    (mem_normalizer_iff.mp (hCJ hc) j).mp hj
  have hJc' : ∀ c ∈ C, ∀ j ∈ J, c⁻¹ * j * c ∈ J := by
    intro c hc j hj
    simpa using hJc c⁻¹ (C.inv_mem hc) j hj
  have hNc : ∀ c ∈ C, ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀ := fun c hc n hn =>
    (mem_normalizer_iff.mp (hCN hc) n).mp hn
  let C₀ : Subgroup ↥C :=
    { carrier := {c | ∀ j ∈ J, (c : G) * j * (c : G)⁻¹ * j⁻¹ ∈ N₀}
      mul_mem' := by
        intro c d hc hd j hj
        have h1 := hNc c c.2 _ (hd j hj)
        have h2 := hc j hj
        have h3 := N₀.mul_mem h1 h2
        have e : ((c * d : ↥C) : G) * j * ((c * d : ↥C) : G)⁻¹ * j⁻¹ =
            (c : G) * ((d : G) * j * (d : G)⁻¹ * j⁻¹) * (c : G)⁻¹ * ((c : G) * j * (c : G)⁻¹ * j⁻¹) := by
          simp only [Subgroup.coe_mul]; group
        rw [e]
        exact h3
      one_mem' := by
        intro j hj
        simp
      inv_mem' := by
        intro c hc j hj
        have h := hc ((c : G)⁻¹ * j * (c : G)) (hJc' c c.2 j hj)
        have e : (((c⁻¹ : ↥C) : G)) * j * (((c⁻¹ : ↥C) : G))⁻¹ * j⁻¹ =
            ((c : G) * ((c : G)⁻¹ * j * (c : G)) * (c : G)⁻¹ * ((c : G)⁻¹ * j * (c : G))⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]; group
        rw [e]
        exact N₀.inv_mem h }
  haveI hC₀n : C₀.Normal := by
    refine ⟨fun c hc d j hj => ?_⟩
    have hj' : (d : G)⁻¹ * j * (d : G) ∈ J := hJc' d d.2 j hj
    have h1 := hNc d d.2 _ (hc ((d : G)⁻¹ * j * (d : G)) hj')
    have e : ((d * c * d⁻¹ : ↥C) : G) * j * ((d * c * d⁻¹ : ↥C) : G)⁻¹ * j⁻¹ =
        (d : G) * ((c : G) * ((d : G)⁻¹ * j * (d : G)) * (c : G)⁻¹ * ((d : G)⁻¹ * j * (d : G))⁻¹) *
          (d : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    show ((d * c * d⁻¹ : ↥C) : G) * j * ((d * c * d⁻¹ : ↥C) : G)⁻¹ * j⁻¹ ∈ N₀
    rw [e]
    exact h1
  refine ⟨↥C ⧸ C₀, inferInstance, inferInstance, QuotientGroup.mk' C₀,
    QuotientGroup.mk'_surjective C₀, ?_⟩
  intro c
  exact QuotientGroup.eq_one_iff c

theorem typeII_isElemAbelian_range {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) {X : Type}
    [Group X] (f : ↥A →* X) : IsElemAbelian p f.range := by
  have hAc := hA.1
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, mul_comm' a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]

theorem typeII_card_range_eq {p : ℕ} (hp : p.Prime) {A : Type} [Group A] [Finite A] {X : Type} [Group X]
    (f : A →* X) (hA : Nat.card A = p ^ 2) {a : A} (ha : a ≠ 1) (hfa : f a = 1) {b : A}
    (hfb : f b ≠ 1) : Nat.card f.range = p := by
  have h1 := Subgroup.card_ker_mul_card_range f
  have hdvd : Nat.card f.range ∣ p ^ 2 := ⟨Nat.card f.ker, by rw [← hA, ← h1, mul_comm]⟩
  obtain ⟨k, hk, hkp⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k
  · exfalso
    have h0 : Nat.card f.range = 1 := by simpa using hkp
    have hsub : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp h0).1
    apply hfb
    have := hsub.elim (⟨f b, b, rfl⟩ : f.range) 1
    simpa using congrArg Subtype.val this
  · simpa using hkp
  · exfalso
    have h2 : Nat.card f.range = p ^ 2 := by simpa using hkp
    have hker1 : Nat.card f.ker = 1 := by
      have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
      rw [h2, hA] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (by simpa using h1)
    have hbot : f.ker = ⊥ := Subgroup.card_eq_one.mp hker1
    have : a ∈ f.ker := hfa
    rw [hbot, Subgroup.mem_bot] at this
    exact ha this

structure TypeIIRedFacts {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G) (J U : Subgroup G)
    {X : Type} [Group X] (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* X) (K R U₀ : Subgroup X) : Prop where
  inj : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ u3T P x J → ρ c = 1 → (c : G) = 1
  T_le : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ u3T P x J → ρ c ∈ R ⊓ K
  RK_le : ∀ s ∈ R ⊓ K, ∃ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ u3T P x J ∧ ρ c = s
  U₀_mem : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ U → ρ c ∈ U₀
  U₀_ex : ∀ v ∈ U₀, ∃ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ U ∧ ρ c = v
  K_mem : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ J → ρ c ∈ K

structure TypeIIRedFactsK {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G) (J U : Subgroup G)
    {X : Type} [Group X] (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* X) (K R U₀ : Subgroup X) : Prop
    extends TypeIIRedFacts p P x J U ρ K R U₀ where
  K_ex : ∀ k ∈ K, ∃ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ J ∧ ρ c = k
  ker_J : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) ∈ J →
    (ρ c = 1 ↔ (c : G) ∈ rankThreePrimeCore p J)

theorem typeII_lemma45_lift_B {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}
    (Bnd : ∀ (X : Type) [Group X], Subgroup X → Subgroup X → Subgroup X)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX45B : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), IsAutOverType Typ p K →
      ∀ (R : Sylow p X) (U₀ : Subgroup X), U₀ ≤ (R : Subgroup X) → IsElemAbelian p U₀ →
        Nat.card U₀ = p → Shape K (R : Subgroup X) U₀ →
        ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
          ¬ V ≤ Bnd X K (R : Subgroup X))
    (hbound : ∀ (X : Type) [Group X] [Finite X] (π : ↥J →* X), Typ p ↥π.range →
      Nat.Coprime p (Nat.card π.ker) → (∀ j : ↥J, π j = 1 → (j : G) ∈ M) →
      IsSylowOf p (u3T P x J) J → normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M → ¬ J ≤ M →
      ∀ R : Sylow p X, ((u3T P x J).subgroupOf J).map π ≤ (R : Subgroup X) →
        (R : Subgroup X) ⊓ π.range = ((u3T P x J).subgroupOf J).map π ∧
          (M.subgroupOf J).map π ≤ Bnd X π.range (R : Subgroup X))
    (hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → Typ p A → Typ p B)
    (hc : PointConfig Typ G p P M x J)
    (hT2 : 2 ≤ CFSG.Open.pRank p (u3T P x J))
    {U : Subgroup G} (hUe : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2) (hUS : U ≤ u3S P x)
    (hxU : x ∈ U) (ha : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1)
    (hshape : ∀ (X : Type) [Group X] (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* X)
      (K R U₀ : Subgroup X), TypeIIRedFactsK p P x J U ρ K R U₀ → Shape K R U₀) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := hc.five; omega
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hc.le_cent
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  set N₀ : Subgroup G := rankThreePrimeCore p J with hN₀
  have hN₀J : N₀ ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hN₀cop : p.Coprime (Nat.card N₀) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hJN : J ≤ normalizer (N₀ : Set G) := (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J).2.1
  have hCN : C ≤ normalizer (N₀ : Set G) := by
    intro g hg
    have hgJ : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJ hg)
    have h1 := glbPrimeCore_map_automorphism p J (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hZ : Subgroup.center Q = ⊥ := u3main_center_bot hN₀J hc.perfect hc.lt hc.minimal ψ hψ hker
  obtain ⟨X, hXg, hXf, ρ, hρ, hρker⟩ := typeII_exists_reduction (C := C) (J := J) (N₀ := N₀) hCJ hCN
  have hJc : ∀ c ∈ C, ∀ j ∈ J, c * j * c⁻¹ ∈ J := fun c hc' j hj =>
    (mem_normalizer_iff.mp (hCJ hc') j).mp hj
  let π : ↥J →* X := ρ.comp (Subgroup.inclusion hJC)
  have hπ : ∀ j : ↥J, π j = ρ ⟨j, hJC j.2⟩ := fun j => rfl
  set K : Subgroup X := π.range with hK
  have hπ1 : ∀ j : ↥J, π j = 1 ↔ (j : G) ∈ N₀ := by
    intro j
    rw [hπ, hρker]
    constructor
    · intro h
      have hcen : ψ j ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨j', rfl⟩ := hψ q
        have hmem : (j * j' * j⁻¹ * j'⁻¹ : ↥J) ∈ ψ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          have := h j' j'.2
          simpa using this
        have h0 := MonoidHom.mem_ker.mp hmem
        simp only [map_mul, map_inv] at h0
        exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h0)).symm
      rw [hZ, Subgroup.mem_bot] at hcen
      have : j ∈ ψ.ker := hcen
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro h j' hj'
      have h1 : j' * (j : G)⁻¹ * j'⁻¹ ∈ N₀ := (mem_normalizer_iff.mp (hJN hj') _).mp (N₀.inv_mem h)
      have := N₀.mul_mem h h1
      simpa [mul_assoc] using this
  have hπker : π.ker = N₀.subgroupOf J := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hπ1 j
  have hkerπ : Nat.Coprime p (Nat.card π.ker) := by
    rw [hπker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀J).toEquiv]
    exact hN₀cop
  haveI hKn : K.Normal := ⟨by
    rintro _ ⟨j, rfl⟩ g
    obtain ⟨d, rfl⟩ := hρ g
    refine ⟨⟨(d : G) * j * (d : G)⁻¹, hJc d d.2 j j.2⟩, ?_⟩
    have e : (⟨(d : G) * j * (d : G)⁻¹, hJC (hJc d d.2 j j.2)⟩ : ↥C) =
        d * ⟨j, hJC j.2⟩ * d⁻¹ := Subtype.ext rfl
    show ρ ⟨(d : G) * j * (d : G)⁻¹, hJC (hJc d d.2 j j.2)⟩ = ρ d * ρ ⟨j, hJC j.2⟩ * (ρ d)⁻¹
    rw [e, map_mul, map_mul, map_inv]⟩
  have hKc : Subgroup.centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha'
    obtain ⟨c, rfl⟩ := hρ a
    rw [Subgroup.mem_bot, hρker]
    intro j hj
    have hmem : (c : G) * j * (c : G)⁻¹ * j⁻¹ ∈ J := J.mul_mem (hJc c c.2 j hj) (J.inv_mem hj)
    have h1 := Subgroup.mem_centralizer_iff.mp ha' (π ⟨j, hj⟩) ⟨⟨j, hj⟩, rfl⟩
    have h1' : ρ ⟨j, hJC hj⟩ * ρ c = ρ c * ρ ⟨j, hJC hj⟩ := h1
    have h2 : π ⟨_, hmem⟩ = 1 := by
      show ρ ⟨(c : G) * j * (c : G)⁻¹ * j⁻¹, hJC hmem⟩ = 1
      have e : (⟨(c : G) * j * (c : G)⁻¹ * j⁻¹, hJC hmem⟩ : ↥C) =
          c * ⟨j, hJC hj⟩ * c⁻¹ * ⟨j, hJC hj⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1']
      group
    exact (hπ1 ⟨_, hmem⟩).mp h2
  have hkerEq : ψ.ker = π.ker := by rw [hker, hπker]
  let eK : Q ≃* ↥K :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans (QuotientGroup.quotientKerEquivRange π))
  have hKT : Typ p ↥K := hiso Q ↥K eK hQ
  have hSC : u3S P x ≤ C := inf_le_right
  let S'' : Subgroup X := (ρ.comp (Subgroup.inclusion hSC)).range
  have hS''p : IsPGroup p S'' := by
    have hSp : IsPGroup p ↥(u3S P x) := P.isPGroup'.to_inf_left
    exact hSp.of_surjective (ρ.comp (Subgroup.inclusion hSC)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨R, hR⟩ := hS''p.exists_le_sylow
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTR : ((u3T P x J).subgroupOf J).map π ≤ (R : Subgroup X) := by
    rintro _ ⟨j, hj, rfl⟩
    exact hR ⟨⟨j, hTS (Subgroup.mem_subgroupOf.mp hj)⟩, rfl⟩
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTp : IsPGroup p (u3T P x J) := P.isPGroup'.to_le hTP
  have hNT : normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M := by
    exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hTp (hTP.trans hPM) hT2
  have hN₀M : N₀ ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  have hTsyl : IsSylowOf p (u3T P x J) J := hc.generic.2.2.1.inf_of_le_normalizer hJC hCJ
  obtain ⟨hRK, hMN⟩ := hbound X π hKT hkerπ (fun j hj => hN₀M ((hπ1 j).mp hj)) hTsyl hNT hc.not_le R hTR
  have hinj : ∀ c : ↥C, (c : G) ∈ u3T P x J → ρ c = 1 → (c : G) = 1 := by
    intro c hcT hρc
    have hcJ : (c : G) ∈ J := hTJ hcT
    have h1 : π ⟨c, hcJ⟩ = 1 := hρc
    have hcop : ¬ p ∣ Nat.card π.ker := (hp.coprime_iff_not_dvd).mp hkerπ
    have h2 := u3main_eq_one_of_ker π hcop (hTp.comap_subtype (K := J)) ⟨c, hcJ⟩
      (Subgroup.mem_subgroupOf.mpr hcT) h1
    exact congrArg Subtype.val h2
  have hUC : U ≤ C := hUS.trans inf_le_right
  let U₀ : Subgroup X := (ρ.comp (Subgroup.inclusion hUC)).range
  have hU₀R : U₀ ≤ (R : Subgroup X) := by
    rintro _ ⟨u, rfl⟩
    exact hR ⟨⟨u, hUS u.2⟩, rfl⟩
  have hU₀e : IsElemAbelian p U₀ := typeII_isElemAbelian_range hUe _
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hU₀card : Nat.card U₀ = p := by
    obtain ⟨a, haUT, ha1⟩ := ha
    refine typeII_card_range_eq hp (ρ.comp (Subgroup.inclusion hUC)) hUcard
      (a := ⟨x, hxU⟩) (fun h => hx1 (congrArg Subtype.val h)) ?_
      (b := ⟨a, haUT.1⟩) ?_
    · show ρ ⟨x, hUC hxU⟩ = 1
      rw [hρker]
      intro j hj
      have hxj : x * j = j * x := (Subgroup.mem_centralizer_singleton_iff.mp (hJC hj)).symm
      have : x * j * x⁻¹ * j⁻¹ = 1 := by
        rw [hxj]; group
      simp [this]
    · intro h
      exact ha1 (hinj ⟨a, hUC haUT.1⟩ haUT.2 h)
  have hKU : ∀ c : ↥C, (c : G) ∈ J → ρ c ∈ K := fun c hcJ => ⟨⟨c, hcJ⟩, rfl⟩
  have hfacts : TypeIIRedFacts p P x J U ρ K R U₀ :=
    { inj := hinj
      T_le := fun c hcT => ⟨hR ⟨⟨c, hTS hcT⟩, rfl⟩, hKU c (hTJ hcT)⟩
      RK_le := by
        intro s hs
        rw [hRK] at hs
        obtain ⟨j, hj, rfl⟩ := hs
        exact ⟨⟨j, hJC j.2⟩, Subgroup.mem_subgroupOf.mp hj, rfl⟩
      U₀_mem := fun c hcU => ⟨⟨c, hcU⟩, rfl⟩
      U₀_ex := by
        rintro _ ⟨u, rfl⟩
        exact ⟨⟨u, hUC u.2⟩, u.2, rfl⟩
      K_mem := hKU }
  have hfactsK : TypeIIRedFactsK p P x J U ρ K R U₀ :=
    { hfacts with
      K_ex := by
        rintro k ⟨j, rfl⟩
        exact ⟨⟨j, hJC j.2⟩, j.2, rfl⟩
      ker_J := fun c hcJ => hπ1 ⟨c, hcJ⟩ }
  obtain ⟨V, hVK, hV2, hU₀V, hnotV⟩ := hX45B X K ⟨hKn, hKc, hKT⟩ R U₀ hU₀R hU₀e hU₀card
    (hshape X ρ K R U₀ hfactsK)
  refine typeII_exists_rankTwoMaximal_of_reduced hp hp2 (P.isPGroup'.to_le (hUS.trans inf_le_left))
    π hkerπ V hV2 hVK ?_ ?_
  · intro u hu j hj
    have huC : u ∈ C := hUC hu
    have hmem : u * (j : G) * u⁻¹ ∈ J := hJc u huC j j.2
    refine ⟨hmem, ?_⟩
    have hnorm : ρ ⟨u, huC⟩ ∈ normalizer (V : Set X) := hU₀V ⟨⟨u, hu⟩, rfl⟩
    have h1 := (mem_normalizer_iff.mp hnorm (π j)).mp hj
    have e : π ⟨u * (j : G) * u⁻¹, hmem⟩ = ρ ⟨u, huC⟩ * π j * (ρ ⟨u, huC⟩)⁻¹ := by
      show ρ ⟨u * (j : G) * u⁻¹, hJC hmem⟩ = _
      have e2 : (⟨u * (j : G) * u⁻¹, hJC hmem⟩ : ↥C) = ⟨u, huC⟩ * ⟨j, hJC j.2⟩ * ⟨u, huC⟩⁻¹ :=
        Subtype.ext rfl
      rw [e2, map_mul, map_mul, map_inv]
      rfl
    rw [e]
    exact h1
  · intro hle
    exact hnotV (hle.trans hMN)

theorem typeII_lemma45_lift {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX45 : Lemma45Facts Typ p Shape)
    (hmax : ∀ (K : Type) [Group K] [Finite K], Typ p K → NormalizerMaximal p K)
    (hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → Typ p A → Typ p B)
    (hc : PointConfig Typ G p P M x J)
    (hT2 : 2 ≤ CFSG.Open.pRank p (u3T P x J))
    {U : Subgroup G} (hUe : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2) (hUS : U ≤ u3S P x)
    (hxU : x ∈ U) (ha : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1)
    (hshape : ∀ (X : Type) [Group X] (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* X)
      (K R U₀ : Subgroup X), TypeIIRedFacts p P x J U ρ K R U₀ → Shape K R U₀) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact typeII_lemma45_lift_B (fun X _ K R => normalizer (((R ⊓ K : Subgroup X)) : Set X)) hS hD1 hU0 hX45
    (fun X _ _ π hKT hker hkerM hT hNT hJM R hTR =>
      typeII_image_le_normalizer π hker hkerM hT hNT hJM (hmax _ hKT) R hTR)
    hiso hc hT2 hUe hUcard hUS hxU ha
    (fun X _ ρ K R U₀ hf => hshape X ρ K R U₀ hf.toTypeIIRedFacts)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
