module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoConnected
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.Combinatorics.ConnectedBipartitionAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K]

variable (K) in
@[expose] def graphAutHom (p : ℕ) :
    MulAut (StatedProj (StatedSp 2 K)) →* (incidenceGraph K p ≃g incidenceGraph K p) where
  toFun α := LinearFlag.parabolicGraphAut p α
  map_one' := RelIso.ext fun M => Subtype.ext
    (map_toMonoidHom_one (M : Subgroup (StatedProj (StatedSp 2 K))))
  map_mul' α β := RelIso.ext fun M => Subtype.ext
    (map_toMonoidHom_mul α β (M : Subgroup (StatedProj (StatedSp 2 K))))

theorem coe_graphAutHom_apply (p : ℕ) (α : MulAut (StatedProj (StatedSp 2 K)))
    (M : spExtremalParabolics 2 K p) :
    ((graphAutHom K p α M : spExtremalParabolics 2 K p) :
      Subgroup (StatedProj (StatedSp 2 K))) = (M : Subgroup _).map α.toMonoidHom :=
  rfl

theorem pointParabolics_subset [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    pointParabolics K ⊆ spExtremalParabolics 2 K p := by
  rw [(extremal_parabolics (K := K) p rfl).2.1]
  exact Set.subset_union_left

theorem planeParabolics_subset [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    planeParabolics K ⊆ spExtremalParabolics 2 K p := by
  rw [(extremal_parabolics (K := K) p rfl).2.1]
  exact Set.subset_union_right

theorem image_graphAutHom_eq_iff (p : ℕ) (α : MulAut (StatedProj (StatedSp 2 K)))
    {S T : Set (Subgroup (StatedProj (StatedSp 2 K)))} (hS : S ⊆ spExtremalParabolics 2 K p)
    (hT : T ⊆ spExtremalParabolics 2 K p) :
    graphAutHom K p α '' {M : spExtremalParabolics 2 K p | (M : Subgroup _) ∈ S} =
        {M : spExtremalParabolics 2 K p | (M : Subgroup _) ∈ T} ↔
      (fun M => M.map α.toMonoidHom) '' S = T := by
  have hval : ∀ R : Set (Subgroup (StatedProj (StatedSp 2 K))),
      R ⊆ spExtremalParabolics 2 K p →
      Subtype.val '' {M : spExtremalParabolics 2 K p | (M : Subgroup _) ∈ R} = R := by
    intro R hR
    ext M
    constructor
    · rintro ⟨M', hM', rfl⟩
      exact hM'
    · intro hM
      exact ⟨⟨M, hR hM⟩, hM, rfl⟩
  rw [← (Set.image_injective.mpr Subtype.val_injective).eq_iff, Set.image_image, hval T hT]
  conv_lhs => rw [show (fun M : spExtremalParabolics 2 K p =>
      ((graphAutHom K p α M : spExtremalParabolics 2 K p) : Subgroup _)) =
      (fun M => M.map α.toMonoidHom) ∘ Subtype.val from rfl, Set.image_comp, hval S hS]

theorem type_kernel [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    (∀ α : MulAut (StatedProj (StatedSp 2 K)),
      ∃ Φ : incidenceGraph K p ≃g incidenceGraph K p,
        (∀ M, (Φ M : Subgroup (StatedProj (StatedSp 2 K))) =
          (M : Subgroup (StatedProj (StatedSp 2 K))).map α.toMonoidHom) ∧
        (((fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K ∧
            (fun M => M.map α.toMonoidHom) '' planeParabolics K = planeParabolics K) ∨
          ((fun M => M.map α.toMonoidHom) '' pointParabolics K = planeParabolics K ∧
            (fun M => M.map α.toMonoidHom) '' planeParabolics K = pointParabolics K))) ∧
    (typeKernel K).Normal ∧ (typeKernel K).index ≤ 2 ∧
    inner (StatedProj (StatedSp 2 K)) ≤ typeKernel K := by
  classical
  obtain ⟨hconn, hbip, hcov, hXne, hYne, -⟩ := incidence_connected (K := K) p
  obtain ⟨hparts, ρ, -, hker, -, hindex⟩ :=
    CFSG.Combinatorics.connected_bipartition_automorphism_action (incidenceGraph K p) hconn
      (pointVertices K p) (planeVertices K p) hbip.disjoint hcov hXne hYne
      fun _ _ h => hbip.mem_of_adj h
  have hX := pointParabolics_subset (K := K) p
  have hY := planeParabolics_subset (K := K) p
  have hH : typeKernel K = (ρ.comp (graphAutHom K p)).ker := by
    ext α
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_typeKernel]
    exact (image_graphAutHom_eq_iff p α hX hX).symm
  refine ⟨fun α => ⟨graphAutHom K p α, fun M => rfl, ?_⟩, hH ▸ MonoidHom.normal_ker _, ?_, ?_⟩
  · rcases hparts (graphAutHom K p α) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(image_graphAutHom_eq_iff p α hX hX).mp h1,
        (image_graphAutHom_eq_iff p α hY hY).mp h2⟩
    · exact Or.inr ⟨(image_graphAutHom_eq_iff p α hX hY).mp h1,
        (image_graphAutHom_eq_iff p α hY hX).mp h2⟩
  · rw [hH, Subgroup.index_ker]
    calc Nat.card (ρ.comp (graphAutHom K p)).range ≤ Nat.card ρ.range :=
          Subgroup.card_le_of_le (by
            rw [MonoidHom.range_comp]
            exact Subgroup.map_le_range _ _)
      _ = ρ.ker.index := (Subgroup.index_ker ρ).symm
      _ ≤ 2 := hindex
  · rintro _ ⟨x, rfl⟩
    have hconj : ∀ y : StatedProj (StatedSp 2 K), ∀ M ∈ pointParabolics K,
        M.map (MulAut.conj y).toMonoidHom ∈ pointParabolics K := by
      rintro y _ ⟨L, hL, rfl⟩
      refine ⟨(y • (⟨L, hL⟩ : SpPoint 2 K)).line, (y • (⟨L, hL⟩ : SpPoint 2 K)).finrank_line, ?_⟩
      exact (projStabilizer_smul y ⟨L, hL⟩).symm
    refine mem_typeKernel_of_forall (hconj x) fun M hM => ?_
    rw [← map_inv]
    exact hconj x⁻¹ M hM

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
