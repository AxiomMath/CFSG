module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Perm

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

theorem IsU42Two.perm_eq_one
    {A : Type} [Group A] (h : IsU42Two A) {n : ℕ} (hn : n ≤ 26)
    (φ : A →* Equiv.Perm (Fin n)) {a : A} (ha : a ∈ commutator A) : φ a = 1 := by
  obtain ⟨U, _, e, hU, hc⟩ := h.exists_commutator_eq
  rw [hc] at ha
  have hmem : a ∈ Subgroup.map (e.symm : MulAut U →* A) (MulAut.conj : U →* MulAut U).range :=
    ⟨e a, ha, by simp⟩
  exact MonoidHom.mem_ker.1 (inn_le_ker_perm hU e hn φ hmem)

theorem u42Facts_holds :
    U42Facts where
  center_bot := by
    intro A _ h
    exact h.center_eq_bot
  complete := by
    intro A _ h φ
    exact h.complete φ
  card := by
    intro A _ h
    exact h.card_eq
  normal := by
    intro A _ h N hN
    exact h.normal_eq N hN
  perm := by
    intro A _ h n hn φ a ha
    exact h.perm_eq_one hn φ ha

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
