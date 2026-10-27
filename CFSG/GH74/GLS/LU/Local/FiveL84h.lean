module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

noncomputable def wt (a h : G) : ZMod 5 :=
  ((Classical.epsilon (fun k : ℕ => h * a * h⁻¹ = a ^ k) : ℕ) : ZMod 5)

theorem wt_eq {a h : G} (ha : orderOf a = 5) {k : ℕ} (hk : h * a * h⁻¹ = a ^ k) :
    wt a h = (k : ZMod 5) := by
  have hs := Classical.epsilon_spec (p := fun k : ℕ => h * a * h⁻¹ = a ^ k) ⟨k, hk⟩
  have h1 : a ^ (Classical.epsilon (fun k : ℕ => h * a * h⁻¹ = a ^ k)) = a ^ k := by
    rw [← hs, hk]
  have h2 := (pow_eq_pow_iff_modEq (x := a)).1 h1
  rw [ha] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h2

theorem wt_one {a : G} (ha : orderOf a = 5) : wt a 1 = 1 := by
  have := wt_eq (a := a) (h := 1) ha (k := 1) (by simp)
  simpa using this

theorem wt_mul {a h h' : G} (ha : orderOf a = 5) {k k' : ℕ} (hk : h * a * h⁻¹ = a ^ k)
    (hk' : h' * a * h'⁻¹ = a ^ k') : wt a (h * h') = wt a h * wt a h' := by
  rw [wt_eq ha hk, wt_eq ha hk']
  have : (h * h') * a * (h * h')⁻¹ = a ^ (k * k') := by
    have e1 : (h * h') * a * (h * h')⁻¹ = h * (h' * a * h'⁻¹) * h⁻¹ := by group
    rw [e1, hk', ← conj_pow, hk, ← pow_mul]
  rw [wt_eq ha this]
  push_cast; ring

theorem wt_conj {a g h : G} (ha : orderOf a = 5) {k : ℕ}
    (hk : (g⁻¹ * h * g) * a * (g⁻¹ * h * g)⁻¹ = a ^ k) :
    wt (g * a * g⁻¹) h = wt a (g⁻¹ * h * g) := by
  rw [wt_eq ha hk]
  have ha' : orderOf (g * a * g⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    simpa [MulAut.conj_apply, ha] using this
  have hk2 : h * (g * a * g⁻¹) * h⁻¹ = (g * a * g⁻¹) ^ k := by
    have e1 : h * (g * a * g⁻¹) * h⁻¹ = g * ((g⁻¹ * h * g) * a * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by
      group
    rw [e1, hk, conj_pow]
  rw [wt_eq ha' hk2]

@[expose] noncomputable def chiHom (H : Subgroup G) {a : G} (ha : orderOf a = 5)
    (hH : ∀ h ∈ H, ∃ k : ℕ, h * a * h⁻¹ = a ^ k) : ↥H →* (ZMod 5)ˣ :=
  (MonoidHom.mk (OneHom.mk (fun h : ↥H => wt a (h : G)) (wt_one ha)) (fun (h h' : ↥H) =>
    wt_mul ha (hH h h.2).choose_spec (hH h' h'.2).choose_spec)).toHomUnits

end CFSG.GH74.GLS.LU.Local.Five
