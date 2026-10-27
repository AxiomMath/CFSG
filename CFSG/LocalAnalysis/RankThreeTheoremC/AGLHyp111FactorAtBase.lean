module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111StarAt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem star_of_absorbsAt_of_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M H B R Y : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hBp : IsPGroup p B) (hBH : B ≤ H) (hKX : ¬ K ≤ d1X0 p M H) (habs : AGLAbsorbsAt p M H K R)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → B ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hY : IsMaxInvariantTwoIn B Y (d1PlusCore p H K)) (hY1 : Y ≠ ⊥)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.Quasithin.CGS Y ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov := cover_normalizer hp hp2 hBH hBp hY
  obtain ⟨hYX, hY2, hBY, hYmax⟩ := hY
  have hN : ∀ C : Subgroup G, C ≤ Y → C ≠ ⊥ → (C.subgroupOf Y).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := by
    intro C hCY hC1 hchar
    have hNYC : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      CFSG.Semidihedral.PrimeOrderCyclicConfinementLift.normalizer_le_of_characteristic_subgroupOf
        hCY hchar
    have hcovC : AGLCovers p H (Subgroup.normalizer (C : Set G)) K :=
      hcov.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNYC hx.2⟩)
    have hNM : ¬ Subgroup.normalizer (C : Set G) ≤ M := by
      intro hNM
      exact hKX (hcovC.trans (Subgroup.map_mono fun x hx => ⟨hx.1, hNM hx.2⟩))
    exact habs _ ⟨C, hC1, hY2.to_le hCY, rfl⟩ hNM (hRY.trans hNYC) hcovC
  have hCGS : CFSG.Quasithin.CGS Y ≤ H :=
    iSup_le fun C => iSup_le fun hCY => iSup_le fun hC1 => iSup_le fun hchar => hN C hCY hC1 hchar
  refine ⟨hCGS, hY2, hBY, fun S hS2 hBS hYS => ?_⟩
  have hNYH : Subgroup.normalizer (Y : Set G) ≤ H := by
    refine hN Y le_rfl hY1 ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  set T := S ⊓ Subgroup.normalizer (Y : Set G) with hT
  have hT2 : IsPGroup 2 T := hS2.to_le inf_le_left
  have hBT : B ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hBS (hBY.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hTX := hb3 T hT2 (inf_le_right.trans hNYH) hBT
  have hTY : T = Y := hYmax T hTX hT2 hBT (le_inf hYS Subgroup.le_normalizer)
  by_contra hSY
  have hlt : Y.subgroupOf S ≠ ⊤ := by
    intro htop
    exact hSY (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hYS)
  have : Group.IsNilpotent S := hS2.isNilpotent
  obtain ⟨x, hxN, hxY⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (Y.subgroupOf S) (lt_top_iff_ne_top.mpr hlt))
  have hmapY : (Y.subgroupOf S).map S.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYS]
  have hxN' : (x : G) ∈ Subgroup.normalizer (Y : Set G) := by
    have := Subgroup.le_normalizer_map S.subtype ⟨x, hxN, rfl⟩
    rwa [hmapY] at this
  have hxT : (x : G) ∈ T := ⟨x.2, hxN'⟩
  rw [hTY] at hxT
  exact hxY hxT

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
