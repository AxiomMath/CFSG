module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GH74.QTGen4.Recog.G23

variable {G : Type*} [Group G]

def cosetPsi (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (t : G)
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) : V →* V where
  toFun v := ⟨v * (t * v * t⁻¹), V.mul_mem v.2 (ht v v.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have hA : t * (a : G) * t⁻¹ ∈ V := ht a a.2
    have h1 : t * ((a : G) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    have h2 : (b : G) * (t * a * t⁻¹) = (t * a * t⁻¹) * b := hV _ b.2 _ hA
    show (a : G) * b * (t * ((a : G) * b) * t⁻¹) =
      ((a : G) * (t * a * t⁻¹)) * ((b : G) * (t * b * t⁻¹))
    rw [h1]
    calc (a : G) * b * ((t * a * t⁻¹) * (t * b * t⁻¹))
        = (a : G) * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = (a : G) * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h2]
      _ = ((a : G) * (t * a * t⁻¹)) * ((b : G) * (t * b * t⁻¹)) := by group

theorem cosetPsi_cosetPsi (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) (t : G) (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (hts : t * t ∈ V) (v : V) :
    cosetPsi V hV t ht (cosetPsi V hV t ht v) = 1 := by
  apply Subtype.ext
  have hA : t * (v : G) * t⁻¹ ∈ V := ht v v.2
  have hs : (t * t) * (v : G) = (v : G) * (t * t) := hV _ hts _ v.2
  have hconj : t * (t * (v : G) * t⁻¹) * t⁻¹ = (v : G) := by
    have e : t * (t * (v : G) * t⁻¹) * t⁻¹ = (t * t) * (v : G) * (t * t)⁻¹ := by group
    rw [e, hs]
    group
  have hAA : (t * (v : G) * t⁻¹) * (t * (v : G) * t⁻¹) = 1 := hexp _ hA
  have e2 : t * ((v : G) * (t * (v : G) * t⁻¹)) * t⁻¹ =
      (t * (v : G) * t⁻¹) * (t * (t * (v : G) * t⁻¹) * t⁻¹) := by group
  show ((v : G) * (t * (v : G) * t⁻¹)) * (t * ((v : G) * (t * (v : G) * t⁻¹)) * t⁻¹) = 1
  rw [e2, hconj]
  calc (v : G) * (t * (v : G) * t⁻¹) * ((t * (v : G) * t⁻¹) * (v : G))
      = (v : G) * ((t * (v : G) * t⁻¹) * (t * (v : G) * t⁻¹)) * (v : G) := by group
    _ = (v : G) * (v : G) := by rw [hAA, mul_one]
    _ = 1 := hexp _ v.2

theorem card_eq_four_of {k i : ℕ} (h : k * i = 8) (hik : i ≤ k) (hk : k ≠ 8) : k = 4 := by
  have hk8 : k ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨i, h.symm⟩
  interval_cases k <;> omega

theorem cosetPsi_ker_card (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) (hcard : Nat.card V = 8) (t : G)
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hts : t * t ∈ V)
    (hα : ∃ v ∈ V, t * v * t⁻¹ ≠ v) :
    Nat.card (cosetPsi V hV t ht).ker = 4 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hmul := Subgroup.card_ker_mul_card_range (cosetPsi V hV t ht)
  rw [hcard] at hmul
  have hle : (cosetPsi V hV t ht).range ≤ (cosetPsi V hV t ht).ker := by
    intro x hx
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
    exact MonoidHom.mem_ker.mpr (cosetPsi_cosetPsi V hV hexp t ht hts v)
  have hi : Nat.card (cosetPsi V hV t ht).range ≤ Nat.card (cosetPsi V hV t ht).ker :=
    Subgroup.card_le_of_le hle
  have hne : Nat.card (cosetPsi V hV t ht).ker ≠ 8 := by
    intro h8
    have htop : (cosetPsi V hV t ht).ker = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h8, hcard])
    obtain ⟨v, hv, hne⟩ := hα
    have hmem : (⟨v, hv⟩ : V) ∈ (cosetPsi V hV t ht).ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h1 : (v : G) * (t * v * t⁻¹) = 1 := congrArg Subtype.val hmem
    have h2 : t * v * t⁻¹ = v := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right (hexp v hv)
    exact hne h2
  exact card_eq_four_of hmul hi hne

theorem card_coset_involutions (V : Subgroup G) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) (hcard : Nat.card V = 8) (t : G)
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hts : t * t ∈ V)
    (hα : ∃ v ∈ V, t * v * t⁻¹ ≠ v) (v0 : V) (hv0 : (t * (v0 : G)) * (t * (v0 : G)) = 1) :
    Nat.card {v : V // (t * (v : G)) * (t * (v : G)) = 1} = 4 := by
  obtain ⟨c, hc⟩ : ∃ c : V, (c : G) = (t * t)⁻¹ := ⟨⟨(t * t)⁻¹, V.inv_mem hts⟩, rfl⟩
  have hiff : ∀ v : V, (t * (v : G)) * (t * (v : G)) = 1 ↔ cosetPsi V hV t ht v = c := by
    intro v
    have hAs : (t * (v : G) * t⁻¹) * (t * t) ∈ V := V.mul_mem (ht v v.2) hts
    have key : (t * (v : G)) * (t * (v : G)) =
        ((v : G) * (t * (v : G) * t⁻¹)) * (t * t) := by
      calc (t * (v : G)) * (t * (v : G)) = ((t * (v : G) * t⁻¹) * (t * t)) * (v : G) := by group
        _ = (v : G) * ((t * (v : G) * t⁻¹) * (t * t)) := hV _ hAs _ v.2
        _ = ((v : G) * (t * (v : G) * t⁻¹)) * (t * t) := by group
    rw [key, mul_eq_one_iff_eq_inv, ← Subtype.coe_inj, hc]
    exact Iff.rfl
  have hsol : cosetPsi V hV t ht v0 = c := (hiff v0).mp hv0
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), ← cosetPsi_ker_card V hV hexp hcard t ht hts hα]
  refine Nat.card_congr ((Equiv.subtypeEquiv (Equiv.mulLeft v0⁻¹) ?_).trans
    (Equiv.subtypeEquivRight fun k => MonoidHom.mem_ker.symm))
  intro v
  show cosetPsi V hV t ht v = c ↔ cosetPsi V hV t ht (v0⁻¹ * v) = 1
  rw [map_mul, map_inv, hsol, inv_mul_eq_one]
  exact eq_comm

end CFSG.GH74.QTGen4.Recog.G23
