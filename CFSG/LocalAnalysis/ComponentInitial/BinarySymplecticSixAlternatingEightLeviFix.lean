module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightPointAction

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Module SymplecticFlag CFSG.Assembly.LowTwoRank Degree64
open LinearMap (BilinForm)

section Basis

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

include he in
theorem mem_pairOrth_inl_two : e (Sum.inl 2) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp

include he in
theorem mem_pairOrth_inr_two : e (Sum.inr 2) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp

abbrev ptE₃ : 𝔼 := ⟨e (Sum.inl 2), mem_pairOrth_inl_two he⟩

abbrev ptF₃ : 𝔼 := ⟨e (Sum.inr 2), mem_pairOrth_inr_two he⟩

theorem eq_comb (w : 𝔼) :
    w = e.repr w (Sum.inl 1) • ptE₂ he + e.repr w (Sum.inl 2) • ptE₃ he +
      e.repr w (Sum.inr 1) • ptF₂ he + e.repr w (Sum.inr 2) • ptF₃ he := by
  apply Subtype.ext
  apply e.repr.injective
  ext i
  simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, Basis.repr_self, smul_eq_mul]
  rcases i with i | i <;> fin_cases i
  · simp [repr_inl_zero he w]
  · simp
  · simp
  · simp [repr_inr_zero he w]
  · simp
  · simp

include he in
theorem eq_zero_of_forall_bilin {w : 𝔼} (h₁ : b (e (Sum.inl 1)) w = 0)
    (h₂ : b (e (Sum.inl 2)) w = 0) (h₃ : b (e (Sum.inr 1)) w = 0)
    (h₄ : b (e (Sum.inr 2)) w = 0) : w = 0 := by
  rw [bilin_inl he] at h₁ h₂
  rw [bilin_inr he] at h₃ h₄
  rw [eq_comb he w, h₁, h₂, h₃, h₄]
  simp

include he in
theorem bilin_ee (i j : Fin 3) : b (e (Sum.inl i)) (e (Sum.inl j)) = 0 := by
  rw [bilin_inl he, e.repr_self]
  simp

include he in
theorem bilin_ff (i j : Fin 3) : b (e (Sum.inr i)) (e (Sum.inr j)) = 0 := by
  rw [bilin_inr he, e.repr_self]
  simp

include he in
theorem bilin_eq_zero_of_perp {v w : 𝔼} (hv₂ : b (e (Sum.inl 1)) v = 0)
    (hv₃ : b (e (Sum.inl 2)) v = 0) (hw₂ : b (e (Sum.inl 1)) w = 0)
    (hw₃ : b (e (Sum.inl 2)) w = 0) : b v w = 0 := by
  rw [bilin_inl he] at hv₂ hv₃ hw₂ hw₃
  rw [form_pointSpan he, hv₂, hv₃, hw₂, hw₃]
  ring

end Basis

section Fix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (hb : b.IsAlt) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "sE" => OddQuadraticFive.sE

theorem zmod_two_eq_of_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 → x = y := by
  decide

theorem bilin_sE (S : bilinIsometryGroup (b.restrict 𝔼)) (x y : 𝔼) :
    b (sE S x) (sE S y) = b x y :=
  OddQuadraticFive.b_sE S x y

theorem bilin_e_add_of_fix {S : bilinIsometryGroup (b.restrict 𝔼)} {u : 𝔼}
    (hu : sE S u = u) (x : 𝔼) : b u (sE S x + x) = 0 := by
  have h := bilin_sE S u x
  rw [hu] at h
  rw [map_add, h]
  exact OddQuadraticFive.zmod2_add_self _

include hb he in
theorem bilin_symm_of_fix {S : bilinIsometryGroup (b.restrict 𝔼)}
    (h₂ : sE S (ptE₂ he) = ptE₂ he) (h₃ : sE S (ptE₃ he) = ptE₃ he) :
    b (sE S (ptF₃ he)) (ptF₂ he) = b (sE S (ptF₂ he)) (ptF₃ he) := by
  set v₂ := sE S (ptF₂ he) + ptF₂ he with hv₂
  set v₃ := sE S (ptF₃ he) + ptF₃ he with hv₃
  have hSf₂ : sE S (ptF₂ he) = ptF₂ he + v₂ := by
    rw [hv₂, add_left_comm, add_self_eq_zero_zmod_two, add_zero]
  have hSf₃ : sE S (ptF₃ he) = ptF₃ he + v₃ := by
    rw [hv₃, add_left_comm, add_self_eq_zero_zmod_two, add_zero]
  have hvv : b v₂ v₃ = 0 := bilin_eq_zero_of_perp he
    (bilin_e_add_of_fix h₂ _) (bilin_e_add_of_fix h₃ _)
    (bilin_e_add_of_fix h₂ _) (bilin_e_add_of_fix h₃ _)
  have hiso := bilin_sE S (ptF₂ he) (ptF₃ he)
  have hff : b (e (Sum.inr 1)) (e (Sum.inr 2)) = 0 := bilin_ff he 1 2
  have hff' : b (e (Sum.inr 2)) (e (Sum.inr 1)) = 0 := bilin_ff he 2 1
  rw [hSf₂, hSf₃] at hiso ⊢
  simp only [Submodule.coe_add, map_add, LinearMap.add_apply] at hiso ⊢
  change b (e (Sum.inr 1)) (e (Sum.inr 2)) + b v₂ (e (Sum.inr 2)) +
    (b (e (Sum.inr 1)) v₃ + b v₂ v₃) = b (e (Sum.inr 1)) (e (Sum.inr 2)) at hiso
  change b (e (Sum.inr 2)) (e (Sum.inr 1)) + b v₃ (e (Sum.inr 1)) =
    b (e (Sum.inr 1)) (e (Sum.inr 2)) + b v₂ (e (Sum.inr 2))
  rw [hff, hvv, add_zero, zero_add] at hiso
  rw [hff, hff', zero_add, zero_add, BinarySymplecticTransvection.symm_apply hb]
  exact (zmod_two_eq_of_add_eq_zero _ _ hiso).symm

include hb he in
theorem eq_of_fix {S S' : bilinIsometryGroup (b.restrict 𝔼)}
    (h₂ : sE S (ptE₂ he) = ptE₂ he) (h₃ : sE S (ptE₃ he) = ptE₃ he)
    (h₂' : sE S' (ptE₂ he) = ptE₂ he) (h₃' : sE S' (ptE₃ he) = ptE₃ he)
    (k₁ : b (sE S (ptF₂ he)) (ptF₂ he) = b (sE S' (ptF₂ he)) (ptF₂ he))
    (k₂ : b (sE S (ptF₂ he)) (ptF₃ he) = b (sE S' (ptF₂ he)) (ptF₃ he))
    (k₃ : b (sE S (ptF₃ he)) (ptF₃ he) = b (sE S' (ptF₃ he)) (ptF₃ he)) : S = S' := by
  have hsame : ∀ (u : 𝔼), sE S u = u → sE S' u = u → ∀ x : 𝔼,
      b u (sE S x + sE S' x) = 0 := by
    intro u hu hu' x
    have h1 := bilin_e_add_of_fix hu x
    have h2 := bilin_e_add_of_fix hu' x
    rw [map_add] at h1 h2 ⊢
    rw [zmod_two_eq_of_add_eq_zero _ _ h1, zmod_two_eq_of_add_eq_zero _ _ h2]
    exact OddQuadraticFive.zmod2_add_self _
  have hf : ∀ j : Fin 3, ∀ y : 𝔼,
      b (e (Sum.inr j)) (sE S y + sE S' y) = b (sE S y) (e (Sum.inr j)) +
        b (sE S' y) (e (Sum.inr j)) := by
    intro j y
    rw [map_add]
    congr 1 <;> exact BinarySymplecticTransvection.symm_apply hb _ _
  have hF₂ : sE S (ptF₂ he) = sE S' (ptF₂ he) := by
    apply OddQuadraticFive.eq_of_add_eq_zero_zmod2
    refine eq_zero_of_forall_bilin he (hsame (ptE₂ he) h₂ h₂' _) (hsame (ptE₃ he) h₃ h₃' _) ?_ ?_
    · rw [Submodule.coe_add, hf, k₁]
      exact OddQuadraticFive.zmod2_add_self _
    · rw [Submodule.coe_add, hf, k₂]
      exact OddQuadraticFive.zmod2_add_self _
  have hF₃ : sE S (ptF₃ he) = sE S' (ptF₃ he) := by
    apply OddQuadraticFive.eq_of_add_eq_zero_zmod2
    refine eq_zero_of_forall_bilin he (hsame (ptE₂ he) h₂ h₂' _) (hsame (ptE₃ he) h₃ h₃' _) ?_ ?_
    · rw [Submodule.coe_add, hf]
      change b (sE S (ptF₃ he)) (ptF₂ he) + b (sE S' (ptF₃ he)) (ptF₂ he) = 0
      rw [bilin_symm_of_fix hb he h₂ h₃, bilin_symm_of_fix hb he h₂' h₃', k₂]
      exact OddQuadraticFive.zmod2_add_self _
    · rw [Submodule.coe_add, hf, k₃]
      exact OddQuadraticFive.zmod2_add_self _
  refine Subtype.ext (Units.ext (LinearMap.ext fun w => ?_))
  change sE S w = sE S' w
  rw [eq_comb he w]
  simp only [map_add, map_smul, h₂, h₃, h₂', h₃', hF₂, hF₃]

end Fix

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
