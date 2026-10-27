module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FixedData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FixFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22OneClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.RankTwoE
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKExclude
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.Unc25G2.M2x CFSG.EvenSporadicStandard.M22Std.TabCheck
open CFSG.EvenSporadicStandard.M23Std

theorem m22_rankFour
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsSporadic L .M22) : RankFour L := by
  obtain ⟨e⟩ := hL
  let φ : Carrier .M22 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ]⟩
  have hS := (Certificates.certificate24781).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M22.exists_at hP sylowS_index_odd
  exact hrange ▸ rankFour_range_of_twoEAt hP sylowS_index_odd h2E hφ

theorem m22_localData
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M22)
    {z : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ L ⊔ zpowers z) :
    ∃ (t m : G) (T1 F1 F2 : Subgroup G), t ∈ L ∧ OneClassData L z t ∧
      FusionData L t T1 F1 F2 m ∧ NData L F1 ∧ FixedData L F1 ∧ GoodK z F1 ∧
      NormQuot (alternatingGroup (Fin 6)) (normalizer (F1 : Set G) ⊓ L) F1 ∧ FixFour L F1 := by
  have := h.simple
  obtain ⟨e⟩ := hL
  let φ : Carrier .M22 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ]⟩
  have hS := (Certificates.certificate24781).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M22.exists_at hP sylowS_index_odd
  obtain ⟨F1, F2, hD, hN, hmem1⟩ := m22_fusionData_pinned h2E
  have hD' := hrange ▸ FusionData.map hφ hD
  have hN' := hrange ▸ NData.map hφ hN
  have hX' := hrange ▸ FixedData.map hφ (fixedData_pinned hmem1)
  have hLift' := hrange ▸ LiftData.map hφ (liftData_pinned hmem1)
  have hFix' : FixFour L (F1.map φ) := hrange ▸ FixFour.map hφ (fixFour_pinned hmem1)
  have htL : φ tEl ∈ L := hrange ▸ ⟨tEl, rfl⟩
  have ht2 : orderOf (φ tEl) = 2 := by
    obtain ⟨hsq, h1⟩ := tEl_involution
    rw [orderOf_injective φ hφ]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  have hOne := m22_oneClassData h ⟨e⟩ hz hz2 hC htL ht2
  have hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z) := fun u hu hu2 hu1 =>
    fused_all h.nonabelian hOne hu hu2 hu1
  have htr := exists_normalizer_conj_eq_mul h.nonabelian hOne hD' hN'.trans
  have hA6 : NormQuot (alternatingGroup (Fin 6))
      (normalizer ((F1.map φ : Subgroup G) : Set G) ⊓ L) (F1.map φ) := by
    rw [← hrange, normalizer_map_inf_range hφ]
    exact NormQuot.map hφ (normQuot_pinned hmem1 hN)
  refine ⟨φ tEl, φ mEl, sylowS.map φ, F1.map φ, F2.map φ, htL, hOne, hD', hN', hX', ?_, hA6,
    hFix'⟩
  rcases goodK_or_badK_of_fixed hOne hZ hN' hX' htr with hgood | hbad
  · exact hgood
  · exact (badK_false hOne hZ hN' hX' htr hbad hLift').elim

end CFSG.EvenSporadicStandard.M22Std
