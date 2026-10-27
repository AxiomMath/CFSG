module

public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem rootSubgroup_le_borelGroup
    (R : Type*) [CommRing R] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α) : rootSubgroup τ R α ≤ borelGroup τ R :=
  le_trans (le_iSup₂_of_le α ⟨hα, hpos⟩ le_rfl) le_sup_right

theorem reduced_word_borel_extraction
    (τ : Tag) (R : Type) [CommRing R]
    (A : Subgroup (Module.End R (RootModule τ R))ˣ) (hB : borelGroup τ R ≤ A) :
    ∀ (ω : List (Fin τ.rank)), (coxeterSystem τ).IsReduced ω →
      (borelGroup τ R).map (MulAut.conj
          (canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).wordProd ω))).toMonoidHom ≤ A →
      ∀ i ∈ ω, weylElt τ R i 1 ∈ A := by
  intro ω
  induction ω with
  | nil => intro _ _ i hi; exact absurd hi List.not_mem_nil
  | cons i ω ih =>
    intro hred hw
    set w := (coxeterSystem τ).wordProd (i :: ω) with hwdef
    have hw' : w = simple τ i * (coxeterSystem τ).wordProd ω := (coxeterSystem τ).wordProd_cons i ω
    have hred' : (coxeterSystem τ).IsReduced ω := by
      have := hred.drop 1
      simpa using this
    have hlen : (coxeterSystem τ).length w =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) + 1 := by
      rw [hred.eq, hred'.eq, List.length_cons]
    have hdesc : (coxeterSystem τ).IsLeftDescent w i := by
      rw [isLeftDescent_iff_length, hw', ← mul_assoc, simple_mul_simple_self, one_mul, ← hw', hlen]
    have hneg := (smul_single_mem_negRoots_iff w⁻¹ i).2
      ((coxeterSystem τ).isRightDescent_inv_iff.2 hdesc)
    set α := -(w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) with hα
    have hαr : IsRoot τ α := IsRoot.neg hneg.1
    have hαp : 0 < height α := by rw [hα, height_neg]; linarith [hneg.2]
    have hwα : w • α = -Pi.single i 1 := by rw [hα, smul_neg, smul_inv_smul]
    have hY : rootSubgroup τ R (-Pi.single i 1) ≤ A := by
      rw [← hwα, ← (canonical_weyl_root_transport τ R).2.1 w α hαr]
      exact le_trans (Subgroup.map_mono (rootSubgroup_le_borelGroup R hαr hαp)) hw
    have hX : rootSubgroup τ R (Pi.single i 1) ≤ A :=
      le_trans (rootSubgroup_le_borelGroup R (isRoot_single τ i) (by
        rw [height_single]; exact one_pos)) hB
    have hn : weylElt τ R i 1 ∈ A := by
      rw [weylElt_eq_xUnit_mul]
      refine mul_mem (mul_mem ?_ ?_) ?_
      · rw [← pinnedX_single]; exact hX (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [← pinnedX_neg_single]; exact hY (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [← pinnedX_single]; exact hX (Subgroup.subset_closure ⟨_, rfl⟩)
    have hrep : weylElt τ R i 1 * canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).wordProd ω) =
        canonicalRep (coxeterSystem τ) R w := by
      rw [hw']
      exact weylElt_mul_canonicalRep_of_length_eq (by rw [← hw', hlen])
    have hw'' : (borelGroup τ R).map (MulAut.conj
        (canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).wordProd ω))).toMonoidHom ≤ A := by
      have heq : canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).wordProd ω) =
          (weylElt τ R i 1)⁻¹ * canonicalRep (coxeterSystem τ) R w := by
        rw [← hrep, inv_mul_cancel_left]
      rw [heq, map_conj_mul]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' := hw hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem (inv_mem hn) hy') (inv_mem (inv_mem hn))
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hn
    · exact ih hred' hw'' j hj

end CFSG.LieType.Chevalley
