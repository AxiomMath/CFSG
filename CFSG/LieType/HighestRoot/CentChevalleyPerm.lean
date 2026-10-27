module

public import CFSG.LieType.HighestRoot.CentChevalley

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

noncomputable abbrev pairGroup
    (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ) :
    Subgroup (ModGL τ K) :=
  rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)

@[expose] def PermutesPairs
    (R : Set (Fin τ.rank → ℤ)) (g : ModGL τ K) : Prop :=
  ∀ β ∈ R, ∃ β' ∈ R, ∀ y, y ∈ pairGroup τ K β ↔ g * y * g⁻¹ ∈ pairGroup τ K β'

variable (K) in
@[expose] noncomputable def pairPermuter
    (R : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ K) where
  carrier := {g | PermutesPairs R g ∧ PermutesPairs R g⁻¹}
  mul_mem' := by
    have key : ∀ {g h : ModGL τ K}, PermutesPairs R g → PermutesPairs R h →
        PermutesPairs R (g * h) := by
      intro g h hg hh β hβ
      obtain ⟨β₁, hβ₁, h₁⟩ := hh β hβ
      obtain ⟨β₂, hβ₂, h₂⟩ := hg β₁ hβ₁
      refine ⟨β₂, hβ₂, fun y => ?_⟩
      rw [h₁, h₂]
      constructor <;> intro hy <;> convert hy using 1
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨key hg hh, ?_⟩
    rw [mul_inv_rev]
    exact key hh' hg'
  one_mem' := by
    refine ⟨fun β hβ => ⟨β, hβ, fun y => ?_⟩, fun β hβ => ⟨β, hβ, fun y => ?_⟩⟩ <;> simp
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨hg', ?_⟩
    rw [inv_inv]
    exact hg

theorem mem_pairPermuter_of_normalizer
    {R : Set (Fin τ.rank → ℤ)} {g : ModGL τ K}
    (h : ∀ β ∈ R, g ∈ Subgroup.normalizer (pairGroup τ K β : Set (ModGL τ K))) :
    g ∈ pairPermuter K R := by
  refine ⟨fun β hβ => ⟨β, hβ, fun y => Subgroup.mem_normalizer_iff.1 (h β hβ) y⟩,
    fun β hβ => ⟨β, hβ, fun y => Subgroup.mem_normalizer_iff.1 (inv_mem (h β hβ)) y⟩⟩

theorem mem_iff_conj_mem_of_map_eq {G : Type*} [Group G] {H H' : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H') (y : G) : y ∈ H ↔ g * y * g⁻¹ ∈ H' := by
  rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  group

theorem mem_iff_inv_conj_mem_of_map_eq {G : Type*} [Group G] {H H' : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H') (y : G) :
    y ∈ H' ↔ g⁻¹ * y * g⁻¹⁻¹ ∈ H := by
  rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem map_conj_canonicalRep_pairGroup
    (w : WeylGroup τ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    (pairGroup τ K β).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      pairGroup τ K (w • β) := by
  rw [Subgroup.map_sup, (canonical_weyl_root_transport τ K).2.1 w β hβ,
    (canonical_weyl_root_transport τ K).2.1 w (-β) (IsRoot.neg hβ), smul_neg]

theorem toralCentralizer_le_pairPermuter
    {a : Fin τ.rank → Kˣ}
    (hcomm : ∀ β ∈ rootCharKernel a, ∀ α ∈ rootCharKernel a, α ≠ β → α ≠ -β →
      ∀ x ∈ rootSubgroup τ K α,
        (∀ y ∈ rootSubgroup τ K β, Commute x y) ∧ ∀ y ∈ rootSubgroup τ K (-β), Commute x y) :
    toralCentralizer τ K a ≤ pairPermuter K (rootCharKernel a) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro t ht
    refine mem_pairPermuter_of_normalizer fun β hβ => ?_
    change t ∈ Subgroup.normalizer ((rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) :
      Subgroup (ModGL τ K)) : Set (ModGL τ K))
    rw [← rootSpan_pair_eq]
    refine torusGroup_le_normalizer_rootSpan ?_ ht
    rintro α (rfl | rfl)
    · exact hβ.1
    · exact IsRoot.neg hβ.1
  · refine iSup₂_le fun α hα x hx => mem_pairPermuter_of_normalizer fun β hβ => ?_
    by_cases h1 : α = β
    · subst h1
      exact Subgroup.le_normalizer (Subgroup.mem_sup_left hx)
    by_cases h2 : α = -β
    · subst h2
      exact Subgroup.le_normalizer (Subgroup.mem_sup_right hx)
    obtain ⟨hc1, hc2⟩ := hcomm β hβ α hα h1 h2 x hx
    exact mem_normalizer_sup_of_commute hc1 hc2
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hmem : ∀ {v : Fin τ.rank → ℤ} {u : WeylGroup τ}, u ∈ rootCharStabilizer a →
        v ∈ rootCharKernel a → u • v ∈ rootCharKernel a :=
      fun {v u} hu hv => ⟨IsRoot.smul hv.1 u, by rw [hu v]; exact hv.2⟩
    have hw' : w⁻¹ ∈ rootCharStabilizer a := fun v => by
      rw [← hw (w⁻¹ • v), smul_inv_smul]
    refine ⟨fun β hβ => ⟨w • β, hmem hw hβ, mem_iff_conj_mem_of_map_eq
      (map_conj_canonicalRep_pairGroup w hβ.1)⟩, fun β hβ => ⟨w⁻¹ • β, hmem hw' hβ, fun y => ?_⟩⟩
    have h := map_conj_canonicalRep_pairGroup (K := K) w (IsRoot.smul hβ.1 w⁻¹)
    rw [smul_inv_smul] at h
    rw [mem_iff_inv_conj_mem_of_map_eq h y]

end CFSG.LieType.HighestRoot
