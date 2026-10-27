module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin

public section

namespace CFSG.OddStandard.SmallF3.Omega

private instance z4o_decIsEvenVec : DecidablePred (IsEvenVec (n := 5)) := fun v => by
  unfold IsEvenVec; infer_instance

@[expose] def z4oS1 (c : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap (c.succAbove 0) (c.succAbove 1) * Equiv.swap (c.succAbove 2) (c.succAbove 3)

@[expose] def z4oS2 (c : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap (c.succAbove 0) (c.succAbove 2) * Equiv.swap (c.succAbove 1) (c.succAbove 3)

theorem z4oS1_mem (c : Fin 5) : z4oS1 c ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  revert c
  unfold z4oS1
  decide +kernel

theorem z4oS2_mem (c : Fin 5) : z4oS2 c ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  revert c
  unfold z4oS2
  decide +kernel

theorem z4oS1_apply (c : Fin 5) : z4oS1 c c = c := by
  revert c
  unfold z4oS1
  decide +kernel

theorem z4oS2_apply (c : Fin 5) : z4oS2 c c = c := by
  revert c
  unfold z4oS2
  decide +kernel

theorem z4oS1_mul_self (c : Fin 5) : z4oS1 c * z4oS1 c = 1 := by
  revert c
  unfold z4oS1
  decide +kernel

theorem z4oS2_mul_self (c : Fin 5) : z4oS2 c * z4oS2 c = 1 := by
  revert c
  unfold z4oS2
  decide +kernel

theorem z4oS_comm (c : Fin 5) : z4oS1 c * z4oS2 c = z4oS2 c * z4oS1 c := by
  revert c
  unfold z4oS1 z4oS2
  decide +kernel

theorem z4o_klein_cases (c : Fin 5) {σ : Equiv.Perm (Fin 5)} (h1 : σ c = c) (h2 : σ * σ = 1)
    (h3 : Equiv.Perm.sign σ = 1) :
    σ = 1 ∨ σ = z4oS1 c ∨ σ = z4oS2 c ∨ σ = z4oS1 c * z4oS2 c := by
  revert h1 h2 h3 σ c
  unfold z4oS1 z4oS2
  decide +kernel

theorem z4o_h1_one (c : Fin 5) {x : Fin 5 → ZMod 2} (hx : IsEvenVec x)
    (h1 : permVec (z4oS1 c) x = x) : ∃ y, IsEvenVec y ∧ x = y + permVec (z4oS1 c) y := by
  revert h1 hx x c
  unfold z4oS1 permVec
  decide +kernel

private def z4oH2 (c : Fin 5) (x : Fin 5 → ZMod 2) : Prop :=
  ∃ y, IsEvenVec y ∧ permVec (z4oS1 c) y = y ∧ x = y + permVec (z4oS2 c) y

private instance z4o_decH2 (c : Fin 5) : DecidablePred (z4oH2 c) := fun x => by
  unfold z4oH2 permVec; infer_instance

private theorem z4o_h1_two_aux : ∀ (c : Fin 5) (x : Fin 5 → ZMod 2), IsEvenVec x →
    x ∘ ⇑(z4oS1 c).symm = x → x ∘ ⇑(z4oS2 c).symm = x → z4oH2 c x := by
  unfold z4oS1 z4oS2
  decide +kernel

theorem z4o_h1_two (c : Fin 5) {x : Fin 5 → ZMod 2} (hx : IsEvenVec x)
    (h1 : permVec (z4oS1 c) x = x) (h2 : permVec (z4oS2 c) x = x) :
    ∃ y, IsEvenVec y ∧ permVec (z4oS1 c) y = y ∧ x = y + permVec (z4oS2 c) y :=
  z4o_h1_two_aux c x hx h1 h2

theorem z4o_fix_klein (c : Fin 5) {x : Fin 5 → ZMod 2} (hx : IsEvenVec x)
    (h1 : permVec (z4oS1 c) x = x) (h2 : permVec (z4oS2 c) x = x) : x = 0 ∨ x = wvec c := by
  revert h1 h2 hx x c
  unfold z4oS1 z4oS2 permVec wvec
  decide +kernel

private theorem z4o_swap_conj_aux : ∀ a b c d : Fin 5, c = a ∨ c = b ∨ d = a ∨ d = b ∨
    Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap a b =
      Equiv.swap c d * Equiv.swap a b := by
  decide +kernel

theorem z4o_swap_conj {a b c d : Fin 5} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) :
    Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * (Equiv.swap a b)⁻¹ =
      Equiv.swap c d * Equiv.swap a b := by
  rw [Equiv.swap_inv]
  rcases z4o_swap_conj_aux a b c d with h | h | h | h | h
  · exact absurd h hca
  · exact absurd h hcb
  · exact absurd h hda
  · exact absurd h hdb
  · exact h

private def z4oSpan (c d e : Fin 5) (x : Fin 5 → ZMod 2) : Prop :=
  x = 0 ∨ x = wvec c ∨ x = wvec d ∨ x = wvec e ∨ x = wvec c + wvec d ∨
    x = wvec c + wvec e ∨ x = wvec d + wvec e ∨ x = wvec c + wvec d + wvec e

private instance z4o_decSpan (c d e : Fin 5) : DecidablePred (z4oSpan c d e) := fun x => by
  unfold z4oSpan; infer_instance

private def z4oThree (a b c d e : Fin 5) : Prop :=
  c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ e ≠ a ∧ e ≠ b ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
    ∀ x : Fin 5 → ZMod 2, IsEvenVec x → x a = x b → z4oSpan c d e x

private instance z4o_decThree (a b c d e : Fin 5) : Decidable (z4oThree a b c d e) := by
  unfold z4oThree; infer_instance

private theorem z4o_three_aux : ∀ a b : Fin 5, a = b ∨ ∃ c d e : Fin 5, z4oThree a b c d e := by
  decide +kernel

theorem z4o_three (a b : Fin 5) (hab : a ≠ b) :
    ∃ c d e : Fin 5, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ e ≠ a ∧ e ≠ b ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      ∀ x : Fin 5 → ZMod 2, IsEvenVec x → x a = x b →
        x = 0 ∨ x = wvec c ∨ x = wvec d ∨ x = wvec e ∨ x = wvec c + wvec d ∨
          x = wvec c + wvec e ∨ x = wvec d + wvec e ∨ x = wvec c + wvec d + wvec e :=
  (z4o_three_aux a b).resolve_left hab

end CFSG.OddStandard.SmallF3.Omega
