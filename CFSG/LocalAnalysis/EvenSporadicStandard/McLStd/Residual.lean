module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Id2519
  CFSG.QuasithinUnique.I32
open CFSG.OddStandard.Solomon75

variable {G : Type} [Group G]

@[expose] def layerClosure (L : Subgroup G) (u : G) : Subgroup G :=
  ⨆ g ∈ oddLayer (centralizer ({u} : Set G)), CFSG.conjugate (centralizer ({u} : Set G) ⊓ L) g

@[expose] def ContainerCase (L : Subgroup G) (t u : G) : Prop :=
  IsTwoComponentIn (layerClosure L u) (centralizer ({u} : Set G)) ∧
    t ∈ normalizer ((layerClosure L u : Subgroup G) : Set G)

@[expose] def SwappedPair (L : Subgroup G) (t u : G) : Prop :=
  ∃ J : Subgroup G, IsTwoComponentIn J (centralizer ({u} : Set G)) ∧ J ≠ CFSG.conjugate J t ∧
    layerClosure L u = J ⊔ CFSG.conjugate J t ∧
    OddTwoIso J (centralizer ({u} : Set G) ⊓ L)

@[expose] def NoSwappedPair (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∀ t u : G, t ∈ centralizer (L : Set G) → orderOf t = 2 → u ∈ L → orderOf u = 2 →
      ¬ SwappedPair L t u

@[expose] def ContainerIsDoubleCover (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∀ t u : G, t ∈ centralizer (L : Set G) → orderOf t = 2 → u ∈ L → orderOf u = 2 →
      ContainerCase L t u →
        ∃ m : ℕ, 8 ≤ m ∧
          IsDoubleCoverOfAlt (↥(layerClosure L u) ⧸ pPrimeCore 2 ↥(layerClosure L u)) m

theorem conjugate_one_eq (B : Subgroup G) : CFSG.conjugate B 1 = B := by
  unfold CFSG.conjugate
  ext x
  simp

theorem le_layerClosure (L : Subgroup G) (u : G) :
    centralizer ({u} : Set G) ⊓ L ≤ layerClosure L u := by
  unfold layerClosure
  refine le_trans (le_of_eq (conjugate_one_eq _).symm) ?_
  exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl

variable [Finite G]

theorem containerCase_or_swappedPair {L : Subgroup G} (h : StdHyp G L) {t u : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hu : u ∈ L) (hu2 : orderOf u = 2)
    {n : ℕ} (hB : IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) n) :
    ContainerCase L t u ∨ SwappedPair L t u :=
  layer_dichotomy h ht ht2 hu hu2 hB

theorem hasIntrinsicAn_of_containerCase {L : Subgroup G} {t u : G} (hu : u ∈ L)
    (hu2 : orderOf u = 2) (hA : ContainerCase L t u) {m : ℕ} (hm : 8 ≤ m)
    (hKcov : IsDoubleCoverOfAlt (↥(layerClosure L u) ⧸ pPrimeCore 2 ↥(layerClosure L u)) m) :
    HasIntrinsicAn G := by
  have hKH : layerClosure L u ≤ centralizer ({u} : Set G) :=
    CFSG.Quasithin.le_of_mem_cComp hA.1.1
  have huK : u ∈ layerClosure L u :=
    le_layerClosure L u ⟨mem_centralizer_singleton_iff.2 rfl, hu⟩
  have hPK : IsPComponent 2 ((layerClosure L u).subgroupOf (centralizer ({u} : Set G))) :=
    (ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).2
      ((isTwoComponentIn_iff hKH).1 hA.1)
  obtain ⟨hq, hc, hquot⟩ := hKcov
  exact ⟨u, layerClosure L u, m, hu2, hm, hKH, hPK, huK, hq.1, hc, hquot⟩

theorem stdHasIntrinsicAn_of_residuals {s : TauCeti.SporadicName} {n : ℕ}
    (hinv : ∀ (T : Type) [Group T] [Finite T], IsSporadic T s → ∃ t : T, orderOf t = 2)
    (hcov : ∀ (T : Type) [Group T], IsSporadic T s → ∀ t : T, orderOf t = 2 →
      IsDoubleCoverOfAlt ↥(centralizer ({t} : Set T)) n)
    (hsw : NoSwappedPair s) (hct : ContainerIsDoubleCover s) : StdHasIntrinsicAn s := by
  intro G _ _ L hStd hL
  obtain ⟨t, ht, ht2⟩ := hStd.exists_involution_centralizer
  obtain ⟨ū, hū⟩ := hinv ↥L hL
  have hu2 : orderOf (ū : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hū
  have hu : (ū : G) ∈ L := ū.2
  have hūeq : (⟨(ū : G), hu⟩ : L) = ū := rfl
  have hB : IsDoubleCoverOfAlt ↥(centralizer ({(ū : G)} : Set G) ⊓ L) n := by
    refine isDoubleCoverOfAlt_inf hu ?_
    rw [hūeq]
    exact hcov ↥L hL ū hū
  rcases containerCase_or_swappedPair hStd ht ht2 hu hu2 hB with hA | hS
  · obtain ⟨m, hm, hKcov⟩ := hct G L hStd hL t ū ht ht2 hu hu2 hA
    exact hasIntrinsicAn_of_containerCase hu hu2 hA hm hKcov
  · exact absurd hS (hsw G L hStd hL t ū ht ht2 hu hu2)

end CFSG.EvenSporadicStandard.McLStd
