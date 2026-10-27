module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

private def evec5 (i : Fin 5) : Fin 5 → ZMod 2 := Pi.single i 1

private def p (a b : Fin 5) : Fin 5 → ZMod 2 := evec5 a + evec5 b

private def u (a : Fin 5) : Fin 5 → ZMod 2 := (fun _ : Fin 5 => 1) + evec5 a

private lemma p_self (a : Fin 5) : p a a = 0 :=
  CharTwo.add_self_eq_zero (evec5 a)

private lemma isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

private lemma isEvenVec_p_unfolded : ∀ a b : Fin 5, (∑ i, p a b i = 0) := by
  decide +kernel

private lemma isEvenVec_p (a b : Fin 5) : IsEvenVec (p a b) := isEvenVec_p_unfolded a b

private lemma u_add_u : ∀ a b : Fin 5, u a + u b = p a b := by
  decide +kernel

private lemma permVec_add (σ : Equiv.Perm (Fin 5)) (v w : Fin 5 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext i; simp [permVec, Pi.add_apply]

private lemma permVec_zero (σ : Equiv.Perm (Fin 5)) :
    permVec σ (0 : Fin 5 → ZMod 2) = 0 := by
  funext i; simp [permVec]

private lemma permVec_evec5 (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    permVec σ (evec5 i) = evec5 (σ i) := by
  funext l
  simp only [permVec, Function.comp_apply, evec5, Pi.single_apply, Equiv.symm_apply_eq]

private lemma permVec_p (σ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    permVec σ (p a b) = p (σ a) (σ b) := by
  simp [p, permVec_add, permVec_evec5]

private lemma permVec_const (σ : Equiv.Perm (Fin 5)) (c : ZMod 2) :
    permVec σ (fun _ : Fin 5 => c) = fun _ => c := by
  funext i; simp [permVec]

private lemma permVec_u (σ : Equiv.Perm (Fin 5)) (a : Fin 5) :
    permVec σ (u a) = u (σ a) := by
  simp only [u]
  rw [permVec_add, permVec_const, permVec_evec5]

private lemma alt_one_transitive_aux :
    ∀ i a : Fin 5, ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ i = a := by
  decide +kernel

private lemma alt_one_transitive (i a : Fin 5) :
    ∃ σ ∈ alternatingGroup (Fin 5), σ i = a := by
  obtain ⟨σ, hσ, hσi⟩ := alt_one_transitive_aux i a
  exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, hσi⟩

private lemma alt_two_transitive_aux :
    ∀ i j a b : Fin 5, i ≠ j → a ≠ b →
      ∃ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ i = a ∧ σ j = b := by
  decide +kernel

private lemma alt_two_transitive (i j a b : Fin 5) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ ∈ alternatingGroup (Fin 5), σ i = a ∧ σ j = b := by
  obtain ⟨σ, hσ, hσa, hσb⟩ := alt_two_transitive_aux i j a b hij hab
  exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, hσa, hσb⟩

private lemma evenVec_nonzero_cases :
    ∀ v : Fin 5 → ZMod 2, (∑ i, v i = 0) → v ≠ 0 →
      (∃ a b : Fin 5, a ≠ b ∧ v = p a b) ∨ ∃ a : Fin 5, v = u a := by
  decide +kernel

private lemma evenVec_two_pairs :
    ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) → ∃ a b c d : Fin 5, w = p a b + p c d := by
  decide +kernel

private def τ1 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

private def τ2 : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

private def τ3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 4

private lemma tau1_mem : τ1 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

private lemma tau2_mem : τ2 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

private lemma tau3_mem : τ3 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel

private lemma p01_fixed_tau1 : permVec τ1 (p 0 1) = p 0 1 := by decide +kernel

private lemma p01_fixed_tau2 : permVec τ2 (p 0 1) = p 0 1 := by decide +kernel

private lemma p01_fixed_tau3 : permVec τ3 (p 0 1) = p 0 1 := by decide +kernel

private lemma fixed_three :
    ∀ u : Fin 5 → ZMod 2, (∑ i, u i = 0) → permVec τ1 u = u → permVec τ2 u = u →
      permVec τ3 u = u → u = 0 ∨ u = p 0 1 := by
  decide +kernel

theorem prince_invariant_all (S : Set (Fin 5 → ZMod 2))
    (hadd : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S)
    (hinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ S, permVec σ v ∈ S)
    (hev : ∀ v ∈ S, IsEvenVec v) {v₀ : Fin 5 → ZMod 2} (hv₀ : v₀ ∈ S) (hne : v₀ ≠ 0) :
    ∀ w : Fin 5 → ZMod 2, IsEvenVec w → w ∈ S := by
  have h0 : (0 : Fin 5 → ZMod 2) ∈ S := by
    have h := hadd v₀ hv₀ v₀ hv₀
    rw [CharTwo.add_self_eq_zero] at h
    exact h
  have hpair : ∀ i j : Fin 5, p i j ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [p_self]
      exact h0
    · rcases evenVec_nonzero_cases v₀ (hev v₀ hv₀) hne with ⟨a, b, hab, hv0⟩ | ⟨a, hv0⟩
      · obtain ⟨σ, hσ, hσa, hσb⟩ := alt_two_transitive a b i j hab hij
        rw [← hσa, ← hσb, ← permVec_p]
        exact hinv σ hσ (p a b) (by rw [← hv0]; exact hv₀)
      · have hua : u a ∈ S := by rw [← hv0]; exact hv₀
        have hui : u i ∈ S := by
          obtain ⟨σ, hσ, hσi⟩ := alt_one_transitive a i
          have hperm : permVec σ (u a) = u i := by rw [permVec_u, hσi]
          rw [← hperm]
          exact hinv σ hσ (u a) hua
        have huj : u j ∈ S := by
          obtain ⟨σ, hσ, hσj⟩ := alt_one_transitive a j
          have hperm : permVec σ (u a) = u j := by rw [permVec_u, hσj]
          rw [← hperm]
          exact hinv σ hσ (u a) hua
        rw [← u_add_u i j]
        exact hadd (u i) hui (u j) huj
  intro w hw
  obtain ⟨a, b, c, d, rfl⟩ := evenVec_two_pairs w hw
  exact hadd (p a b) (hpair a b) (p c d) (hpair c d)

theorem prince_endo (s : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2))
    (hev : ∀ v, IsEvenVec v → IsEvenVec (s v))
    (hadd : ∀ v w, IsEvenVec v → IsEvenVec w → s (v + w) = s v + s w)
    (hequi : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v →
      s (permVec σ v) = permVec σ (s v)) :
    (∀ v, IsEvenVec v → s v = 0) ∨ (∀ v, IsEvenVec v → s v = v) := by
  have hz : IsEvenVec (0 : Fin 5 → ZMod 2) := isEvenVec_zero
  have hs0 : s 0 = 0 := by
    have h := hadd 0 0 hz hz
    rw [add_zero] at h
    rw [CharTwo.add_self_eq_zero] at h
    exact h
  have hp01 : IsEvenVec (p 0 1) := isEvenVec_p 0 1
  have hu_even : IsEvenVec (s (p 0 1)) := hev (p 0 1) hp01
  have hfix1 : permVec τ1 (s (p 0 1)) = s (p 0 1) := by
    rw [← hequi τ1 tau1_mem (p 0 1) hp01, p01_fixed_tau1]
  have hfix2 : permVec τ2 (s (p 0 1)) = s (p 0 1) := by
    rw [← hequi τ2 tau2_mem (p 0 1) hp01, p01_fixed_tau2]
  have hfix3 : permVec τ3 (s (p 0 1)) = s (p 0 1) := by
    rw [← hequi τ3 tau3_mem (p 0 1) hp01, p01_fixed_tau3]
  rcases fixed_three (s (p 0 1)) hu_even hfix1 hfix2 hfix3 with hu0 | hup
  · left
    have hsp : ∀ a b : Fin 5, s (p a b) = 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab; rw [p_self, hs0]
      · obtain ⟨σ, hσ, hσa, hσb⟩ := alt_two_transitive 0 1 a b (by decide) hab
        have hpa : p a b = permVec σ (p 0 1) := by rw [permVec_p, hσa, hσb]
        rw [hpa, hequi σ hσ (p 0 1) hp01, hu0, permVec_zero]
    intro v hv
    obtain ⟨a, b, c, d, rfl⟩ := evenVec_two_pairs v hv
    rw [hadd (p a b) (p c d) (isEvenVec_p a b) (isEvenVec_p c d), hsp a b, hsp c d,
      add_zero]
  · right
    have hsp : ∀ a b : Fin 5, s (p a b) = p a b := by
      intro a b
      by_cases hab : a = b
      · subst hab; rw [p_self, hs0]
      · obtain ⟨σ, hσ, hσa, hσb⟩ := alt_two_transitive 0 1 a b (by decide) hab
        have hpa : p a b = permVec σ (p 0 1) := by rw [permVec_p, hσa, hσb]
        rw [hpa, hequi σ hσ (p 0 1) hp01, hup, permVec_p, hσa, hσb]
    intro v hv
    obtain ⟨a, b, c, d, rfl⟩ := evenVec_two_pairs v hv
    rw [hadd (p a b) (p c d) (isEvenVec_p a b) (isEvenVec_p c d), hsp a b, hsp c d]

end CFSG.OddStandard.SmallF3.Omega
