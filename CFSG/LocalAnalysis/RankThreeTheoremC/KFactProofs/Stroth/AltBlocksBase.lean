module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksModel
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

variable {k p m : ℕ}

theorem translHom_injective [NeZero p] : Function.Injective (translHom (k := k) (p := p)) := by
  intro f g h
  have h1 : transl (Multiplicative.toAdd f) = transl (Multiplicative.toAdd g) := h
  apply Multiplicative.toAdd.injective
  funext j
  have h2 := congrArg (fun σ : Equiv.Perm (Fin k × ZMod p) => (σ (j, 0)).2) h1
  simpa using h2

theorem baseHom_injective [NeZero p] : Function.Injective (baseHom (k := k) (p := p) (m := m)) := by
  intro f g h
  rw [baseHom_apply, baseHom_apply] at h
  apply translHom_injective (k := k) (p := p)
  have h1 : transl (Multiplicative.toAdd f) = transl (Multiplicative.toAdd g) := by
    refine Equiv.ext fun x => ?_
    have h2 := congrArg (fun τ : Equiv.Perm (Ω k p m) => τ (Sum.inl x)) h
    simpa using h2
  exact h1

theorem card_base [NeZero p] : Nat.card (base (k := k) (p := p) (m := m)) = p ^ k := by
  have e : Multiplicative (Fin k → ZMod p) ≃* base (k := k) (p := p) (m := m) :=
    MonoidHom.ofInjective (baseHom_injective (k := k) (p := p) (m := m))
  rw [← Nat.card_congr e.toEquiv]
  show Nat.card (Fin k → ZMod p) = p ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem p_nsmul_eq_zero (f : Fin k → ZMod p) : p • f = 0 := by
  funext j
  simp

theorem sign_blockPerm [NeZero p] (π : Equiv.Perm (Fin k × ZMod p)) :
    Equiv.Perm.sign (blockPerm (m := m) π) = Equiv.Perm.sign π := by
  rw [blockPerm, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]

private theorem sign_eq_one_of_pow_eq_one {α : Type*} [Fintype α] [DecidableEq α] (hp : Odd p)
    {σ : Equiv.Perm α} (h : σ ^ p = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, hp.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem sign_transl [NeZero p] (hp : Odd p) (f : Fin k → ZMod p) :
    Equiv.Perm.sign (transl f) = 1 := by
  apply sign_eq_one_of_pow_eq_one hp
  have h : transl f = translHom (Multiplicative.ofAdd f) := rfl
  rw [h, ← map_pow, ← ofAdd_nsmul, p_nsmul_eq_zero, ofAdd_zero, map_one]

theorem base_le_alternatingGroup [NeZero p] (hp : Odd p) :
    base (k := k) (p := p) (m := m) ≤ alternatingGroup (Ω k p m) := by
  intro x hx
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [Equiv.Perm.mem_alternatingGroup, baseHom_apply, sign_blockPerm, sign_transl hp]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
