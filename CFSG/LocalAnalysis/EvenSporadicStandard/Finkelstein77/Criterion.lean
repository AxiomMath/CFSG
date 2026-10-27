module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def innAut (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range

@[expose] def NodeCriterion (Y : Type*) [Group Y] : Prop :=
  ∀ x : MulAut Y, orderOf x = 2 → ∀ M : Subgroup (MulAut Y), (M = innAut Y ∨ M = ⊤) →
    CFSG.Assembly.oddCore ↥(M ⊓ centralizer ({x} : Set (MulAut Y))) = ⊥ ∧
      ∀ B : Subgroup ↥(M ⊓ centralizer ({x} : Set (MulAut Y))), B.Normal →
        ¬ (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
          Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))

theorem eq_or_eq_top_of_index_dvd_two {Γ : Type*} [Group Γ] {H : Subgroup Γ} (hH : H.index ∣ 2)
    {M : Subgroup Γ} (hM : H ≤ M) : M = H ∨ M = ⊤ := by
  have h2 : M.index ∣ 2 := (Subgroup.index_dvd_of_le hM).trans hH
  have hmul : H.relIndex M * M.index = H.index := Subgroup.relIndex_mul_index hM
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · refine Or.inl (le_antisymm ?_ hM)
    rw [h] at hmul
    have h3 : H.relIndex M * 2 ∣ 1 * 2 := by
      rw [hmul, one_mul]
      exact hH
    have h4 : H.relIndex M ∣ 1 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
    exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp h4)

theorem hypothesisOne_of_nodeCriterion {Y : Type*} [Group Y] (hOut : (innAut Y).index ∣ 2)
    (h : NodeCriterion Y) : HypothesisOne Y := by
  intro M hM x hxM hx2 B hB
  obtain ⟨h0, hB'⟩ := h x hx2 M (eq_or_eq_top_of_index_dvd_two hOut hM)
  let e : (↥(M ⊓ centralizer ({x} : Set (MulAut Y))) ⧸
      CFSG.Assembly.oddCore ↥(M ⊓ centralizer ({x} : Set (MulAut Y)))) ≃*
        ↥(M ⊓ centralizer ({x} : Set (MulAut Y))) :=
    (QuotientGroup.quotientMulEquivOfEq h0).trans QuotientGroup.quotientBot
  have hBn : (B.map e.toMonoidHom).Normal := hB.map e.toMonoidHom e.surjective
  let f : B ≃* B.map e.toMonoidHom := B.equivMapOfInjective e.toMonoidHom e.injective
  rintro (⟨⟨g⟩⟩ | ⟨⟨g⟩⟩)
  · exact hB' _ hBn (Or.inl ⟨f.symm.trans g⟩)
  · exact hB' _ hBn (Or.inr ⟨f.symm.trans g⟩)

end CFSG.EvenSporadicStandard.Finkelstein77
