module

public import CFSG.FeitThompson.Local.GeneralLinearReductionKernel
import CFSG.FeitThompson.Local.RepresentationLiftOneStep

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Representation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {A : Type*} [Group A]

abbrev glModPReduction (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ℕ) {e : ℕ} (he : e ≠ 0) :
    GL ι (ZMod (p ^ e)) →* GL ι (ZMod p) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_pow_self p he) (ZMod p))

lemma glModPReduction_comp_glPowReduction {e : ℕ} (he : e ≠ 0) :
    glModPReduction ι p (Nat.succ_ne_zero e)
      = (glModPReduction ι p he).comp (glPowReduction ι p e) := by
  rw [glModPReduction, glModPReduction, glPowReduction_eq_map,
    ← Matrix.GeneralLinearGroup.map_comp]
  congr 1
  exact Subsingleton.elim _ _

private lemma exists_lift_one (ρ : A →* GL ι (ZMod p)) :
    ∃ ρ₁ : A →* GL ι (ZMod (p ^ 1)),
      (glModPReduction ι p Nat.one_ne_zero).comp ρ₁ = ρ := by
  refine ⟨(Matrix.GeneralLinearGroup.map
    (ZMod.castHom (pow_one p).dvd (ZMod (p ^ 1)))).comp ρ, ?_⟩
  rw [glModPReduction, ← MonoidHom.comp_assoc, ← Matrix.GeneralLinearGroup.map_comp,
    Subsingleton.elim ((ZMod.castHom (dvd_pow_self p Nat.one_ne_zero) (ZMod p)).comp
      (ZMod.castHom (pow_one p).dvd (ZMod (p ^ 1)))) (RingHom.id (ZMod p)),
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_comp]

private theorem exists_lift_succ [Finite A] (hp : p.Prime) (hA : ¬ p ∣ Nat.card A)
    (ρ : A →* GL ι (ZMod p)) (e : ℕ) :
    ∃ ρₑ : A →* GL ι (ZMod (p ^ (e + 1))),
      (glModPReduction ι p e.succ_ne_zero).comp ρₑ = ρ := by
  induction e with
  | zero => exact exists_lift_one ρ
  | succ e ih =>
      obtain ⟨ρₑ, hρₑ⟩ := ih
      obtain ⟨ρ', hρ'⟩ := exists_monoidHom_glPowReduction_comp_eq (ι := ι) hp
        (Nat.le_add_left 1 e) hA ρₑ
      exact ⟨ρ', by rw [glModPReduction_comp_glPowReduction e.succ_ne_zero,
        MonoidHom.comp_assoc, hρ', hρₑ]⟩

theorem exists_monoidHom_glModPReduction_comp_eq [Finite A] (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL ι (ZMod p)) {e : ℕ} (he : 1 ≤ e) :
    ∃ ρₑ : A →* GL ι (ZMod (p ^ e)),
      (glModPReduction ι p (Nat.one_le_iff_ne_zero.1 he)).comp ρₑ = ρ := by
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  exact exists_lift_succ hp hA ρ e

theorem exists_monoidHom_castHom_entry_eq_of_one_le [Finite A] (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL ι (ZMod p)) {e : ℕ} (he : 1 ≤ e) :
    ∃ ρₑ : A →* GL ι (ZMod (p ^ e)), ∀ (a : A) (i j : ι),
      ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.1 he)) (ZMod p) (ρₑ a i j)
        = ρ a i j := by
  obtain ⟨ρₑ, hρₑ⟩ := exists_monoidHom_glModPReduction_comp_eq (ι := ι) hp hA ρ he
  refine ⟨ρₑ, fun a i j => ?_⟩
  have h : glModPReduction ι p (Nat.one_le_iff_ne_zero.1 he) (ρₑ a) = ρ a :=
    DFunLike.congr_fun hρₑ a
  calc ZMod.castHom (dvd_pow_self p (Nat.one_le_iff_ne_zero.1 he)) (ZMod p) (ρₑ a i j)
      = glModPReduction ι p (Nat.one_le_iff_ne_zero.1 he) (ρₑ a) i j :=
        (Matrix.GeneralLinearGroup.map_apply _ _ _ _).symm
    _ = ρ a i j := by rw [h]

end Representation

end CFSG.FeitThompson
