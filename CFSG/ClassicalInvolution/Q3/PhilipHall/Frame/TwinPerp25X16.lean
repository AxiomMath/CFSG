module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X9
public import CFSG.ClassicalInvolution.Asc77.AscCX9P

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open scoped MatrixGroups

section SL2

@[expose] def sl23i : SL(2, ZMod 3) := ⟨!![0, 1; -1, 0], by decide⟩

@[expose] def sl23j : SL(2, ZMod 3) := ⟨!![1, 1; 1, -1], by decide⟩

theorem sl23_ij_rel : sl23i ^ 4 = 1 ∧ sl23i * sl23i ≠ 1 ∧ sl23j * sl23j = sl23i * sl23i ∧
    sl23i * sl23j * sl23i = sl23j ∧ sl23j * sl23u * sl23i = sl23u ∧
    (sl23i * sl23j) * sl23u * sl23j = sl23u := by decide +kernel

theorem sl23_Q_words : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 →
    ∃ m : Fin 4, ∃ n : Fin 2, q = sl23i ^ (m : ℕ) * sl23j ^ (n : ℕ) := by decide +kernel

theorem sl23_stab_u : ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → a * a ≠ 1 → b * b = a * a →
    a * b * a = b → b * sl23u * a = sl23u → (a * b) * sl23u * b = sl23u →
    ∃ g : SL(2, ZMod 3), g * sl23u = sl23u * g ∧ a * g = g * sl23i ∧ b * g = g * sl23j := by
  decide +kernel


theorem sl23_hom_inner (α : SL(2, ZMod 3) →* SL(2, ZMod 3)) (hinj : Function.Injective α)
    (hu : ∃ g : SL(2, ZMod 3), α sl23u = g * sl23u * g⁻¹) :
    ∃ g : SL(2, ZMod 3), ∀ x, α x = g * x * g⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := hu
  obtain ⟨hi4, hi2, hj2, hiji, hjui, hijuj⟩ := sl23_ij_rel
  let α' : SL(2, ZMod 3) →* SL(2, ZMod 3) := (MulAut.conj g₀⁻¹).toMonoidHom.comp α
  have hα' : ∀ x, α' x = g₀⁻¹ * α x * g₀ := fun x => by
    show g₀⁻¹ * α x * g₀⁻¹⁻¹ = _
    rw [inv_inv]
  have hinj' : Function.Injective α' := (MulAut.conj g₀⁻¹).injective.comp hinj
  have hu' : α' sl23u = sl23u := by rw [hα', hg₀]; group
  have ha4 : (α' sl23i) ^ 4 = 1 := by rw [← map_pow, hi4, map_one]
  have ha2 : α' sl23i * α' sl23i ≠ 1 := by
    intro h
    rw [← map_mul, ← map_one α'] at h
    exact hi2 (hinj' h)
  have hb2 : α' sl23j * α' sl23j = α' sl23i * α' sl23i := by rw [← map_mul, ← map_mul, hj2]
  have hab : α' sl23i * α' sl23j * α' sl23i = α' sl23j := by rw [← map_mul, ← map_mul, hiji]
  have hbua : α' sl23j * sl23u * α' sl23i = sl23u := by
    have := congrArg α' hjui
    rw [map_mul, map_mul, hu'] at this
    exact this
  have habub : (α' sl23i * α' sl23j) * sl23u * α' sl23j = sl23u := by
    have := congrArg α' hijuj
    rw [map_mul, map_mul, map_mul, hu'] at this
    exact this
  obtain ⟨g, hgu, hag, hbg⟩ := sl23_stab_u _ _ ha4 ha2 hb2 hab hbua habub
  have hconj : ∀ x, α' x = g * x * g⁻¹ := by
    intro x
    obtain ⟨q, hq, k, rfl⟩ := sl23_decomp x
    obtain ⟨m, n, rfl⟩ := sl23_Q_words q hq
    have h1 : α' sl23i = g * sl23i * g⁻¹ := by rw [← hag]; group
    have h2 : α' sl23j = g * sl23j * g⁻¹ := by rw [← hbg]; group
    have h3 : α' sl23u = g * sl23u * g⁻¹ := by rw [hu', hgu]; group
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, h1, h2, h3, conj_pow, conj_pow, conj_pow]
    group
  refine ⟨g₀ * g, fun x => ?_⟩
  calc α x = g₀ * (g₀⁻¹ * α x * g₀) * g₀⁻¹ := by group
    _ = g₀ * α' x * g₀⁻¹ := by rw [← hα' x]
    _ = g₀ * (g * x * g⁻¹) * g₀⁻¹ := by rw [hconj x]
    _ = (g₀ * g) * x * (g₀ * g)⁻¹ := by group

theorem diagTriv_inner_of_equiv {H : Type} [Group H] (e : H ≃* SL(2, ZMod 3)) (α : H ≃* H)
    (h : CFSG.ClassicalInvolution.Asc77.CX.DiagTriv 3 α) : ∃ g : H, ∀ x : H, α x = g * x * g⁻¹ := by
  set u := e.symm sl23u with hu
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, sl23_u3, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    have : sl23u = 1 := by
      have := congrArg e h1
      simpa [hu] using this
    exact absurd (congrArg (fun m : SL(2, ZMod 3) => m) this) (by decide +kernel)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  obtain ⟨g, hg⟩ := h u hord
  let αS : SL(2, ZMod 3) ≃* SL(2, ZMod 3) := e.symm.trans (α.trans e)
  have hαS : ∀ s, αS s = e (α (e.symm s)) := fun s => rfl
  obtain ⟨g', hg'⟩ := sl23_hom_inner αS.toMonoidHom αS.injective ⟨e g, by
    show αS sl23u = _
    rw [hαS, ← hu, hg, map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply]⟩
  refine ⟨e.symm g', fun x => ?_⟩
  have h1 := hg' (e x)
  have h2 : αS (e x) = e (α x) := by rw [hαS, MulEquiv.symm_apply_apply]
  have h3 : e (α x) = g' * e x * g'⁻¹ := by rw [← h2]; exact h1
  apply e.injective
  rw [h3]
  simp

end SL2

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
