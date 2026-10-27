module

public import CFSG.SignalizerFunctorTheorem.Solvable.Bender.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open

theorem exists_comm_fail {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {A T : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) (hcardA : Nat.card A = p ^ 2)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hcop : Nat.Coprime p (Nat.card T))
    (hfaith : ∀ a ∈ A, (∀ t ∈ T, a * t = t * a) → a = 1)
    {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    ∃ a ∈ A, a ∉ Subgroup.zpowers b ∧ ∃ t ∈ T, a * t = t * a ∧ b * t ≠ t * b := by
  classical
  haveI := Fact.mk hp
  by_contra hcon
  push Not at hcon
  have hord : ∀ g ∈ A, g ≠ 1 → orderOf g = p := fun g hg hg1 =>
    orderOf_eq_prime (hA.2 g hg) hg1
  have hH : ∀ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p A,
      T ⊓ Subgroup.centralizer (H : Set G) ≤ T ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro H hHmem t ht
    obtain ⟨htT, htC⟩ := ht
    refine ⟨htT, ?_⟩
    obtain ⟨hHA, hcardH⟩ := hHmem
    have hH' : Nat.card H = p := by
      have h1 : Nat.card A = p * Nat.card H := hcardH
      rw [hcardA, pow_two] at h1
      exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
    by_cases hbH : b ∈ H
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp htC) b hbH
    · have hnt : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH']; exact hp.one_lt)
      obtain ⟨a0, ha0⟩ := exists_ne (1 : H)
      have ha0H : (a0 : G) ∈ H := a0.2
      have ha0A : (a0 : G) ∈ A := hHA ha0H
      have ha0ne : (a0 : G) ≠ 1 := fun h => ha0 (Subtype.ext h)
      have hanb : (a0 : G) ∉ Subgroup.zpowers b := by
        intro hmem
        have hle : Subgroup.zpowers (a0 : G) ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hmem
        have heq : Subgroup.zpowers (a0 : G) = Subgroup.zpowers b := by
          apply Subgroup.eq_of_le_of_card_ge hle
          rw [Nat.card_zpowers, Nat.card_zpowers, hord _ ha0A ha0ne, hord b hb hb1]
        have hbz : b ∈ Subgroup.zpowers (a0 : G) := by
          rw [heq]
          exact Subgroup.mem_zpowers b
        exact hbH (Subgroup.zpowers_le.2 ha0H hbz)
      have hcomm : a0 * t = t * a0 := (Subgroup.mem_centralizer_iff.mp htC) (a0 : G) ha0H
      have hbt : b * t = t * b := hcon (a0 : G) ha0A hanb t htT hcomm
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hbt)
  have hsup : (⨆ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p A,
      T ⊓ Subgroup.centralizer (H : Set G)) = T :=
    CFSG.SignalizerFunctorTheorem.Solvable.Bender.iSup_hyperplanes_inf_centralizer hp hA
      (by rw [hcardA]; exact Nat.le_self_pow two_ne_zero p) hAT hcop
  have hTb : T ≤ Subgroup.centralizer ({b} : Set G) := by
    calc T = ⨆ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p A,
          T ⊓ Subgroup.centralizer (H : Set G) := hsup.symm
      _ ≤ T ⊓ Subgroup.centralizer ({b} : Set G) := iSup₂_le (fun H hH' => hH H hH')
      _ ≤ Subgroup.centralizer ({b} : Set G) := inf_le_right
  apply hb1
  apply hfaith b hb
  intro t ht
  exact (Subgroup.mem_centralizer_iff.mp (hTb ht)) b (Set.mem_singleton b)

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
