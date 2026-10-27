module

public import CFSG.GH74.GLS.LU.Local.FiveStdInputs
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd

open Subgroup

variable {G : Type} [Group G]

structure Model (ι : E → G) : Prop where
  valid_one : validE oneE = true
  valid_mul : ∀ x y, validE x = true → validE y = true → validE (mulE x y) = true
  valid_inv : ∀ x, validE x = true → validE (invE x) = true
  map_one : ι oneE = 1
  map_mul : ∀ x y, validE x = true → validE y = true → ι (mulE x y) = ι x * ι y
  map_inv : ∀ x, validE x = true → ι (invE x) = (ι x)⁻¹
  inj : ∀ x y, validE x = true → validE y = true → ι x = ι y → x = y

def S (ι : E → G) (L : List E) : Set G := ι '' {x | x ∈ L}

abbrev V (L : List E) : Prop := ∀ x ∈ L, validE x = true

omit [Group G] in
theorem mem_S {ι : E → G} {L : List E} {g : G} : g ∈ S ι L ↔ ∃ x ∈ L, ι x = g := Iff.rfl

theorem V_nil : V ([] : List E) := fun _ h => by simp at h

theorem V_cons {x : E} {L : List E} (hx : validE x = true) (hL : V L) : V (x :: L) := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact hL y hy

theorem V_filter {L : List E} (p : E → Bool) (hL : V L) : V (L.filter p) :=
  fun y hy => hL y (List.mem_of_mem_filter hy)

theorem ordAux_ge (x : E) : ∀ (fuel : ℕ) (y : E) (k : ℕ), k ≤ ordAux x fuel y k
  | 0, _, _ => le_rfl
  | fuel + 1, y, k => by
    by_cases hye : y = oneE
    · simp [ordAux, hye]
    · have : ordAux x (fuel + 1) y k = ordAux x fuel (mulE y x) (k + 1) := by simp [ordAux, hye]
      rw [this]
      exact (Nat.le_succ k).trans (ordAux_ge x fuel _ (k + 1))

theorem ordE_pos (x : E) : 1 ≤ ordE x := ordAux_ge x 300 x 1

namespace Model

variable {ι : E → G} (hM : Model ι)
include hM

theorem powE_spec {x : E} (hx : validE x = true) :
    ∀ n, validE (powE x n) = true ∧ ι (powE x n) = ι x ^ n
  | 0 => ⟨hM.valid_one, by simp [powE, hM.map_one]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := powE_spec hx n
    refine ⟨hM.valid_mul _ _ h1 hx, ?_⟩
    rw [powE, hM.map_mul _ _ h1 hx, h2, pow_succ]

theorem valid_powE {x : E} (hx : validE x = true) (n : ℕ) : validE (powE x n) = true :=
  (hM.powE_spec hx n).1

theorem map_powE {x : E} (hx : validE x = true) (n : ℕ) : ι (powE x n) = ι x ^ n :=
  (hM.powE_spec hx n).2

theorem valid_conjE {g x : E} (hg : validE g = true) (hx : validE x = true) : validE (conjE g x) = true :=
  hM.valid_mul _ _ (hM.valid_mul _ _ hg hx) (hM.valid_inv _ hg)

theorem map_conjE {g x : E} (hg : validE g = true) (hx : validE x = true) :
    ι (conjE g x) = ι g * ι x * (ι g)⁻¹ := by
  rw [conjE, hM.map_mul _ _ (hM.valid_mul _ _ hg hx) (hM.valid_inv _ hg), hM.map_mul _ _ hg hx,
    hM.map_inv _ hg]

omit [Group G] hM in
theorem conjI_eq (g x : E) : conjI g (invE g) x = conjE g x := rfl

theorem valid_conjI {g x : E} (hg : validE g = true) (hx : validE x = true) :
    validE (conjI g (invE g) x) = true := hM.valid_conjE hg hx

theorem map_conjI {g x : E} (hg : validE g = true) (hx : validE x = true) :
    ι (conjI g (invE g) x) = ι g * ι x * (ι g)⁻¹ := hM.map_conjE hg hx

theorem ordAux_spec {x : E} (hx : validE x = true) :
    ∀ (fuel : ℕ) (y : E) (k : ℕ), validE y = true → ι y = ι x ^ k → 1 ≤ k →
      (∀ j, 1 ≤ j → j < k → ι x ^ j ≠ 1) →
      ((ordAux x fuel y k = k + fuel ∧ ∀ j, 1 ≤ j → j < k + fuel → ι x ^ j ≠ 1) ∨
        (ordAux x fuel y k < k + fuel ∧ ι x ^ ordAux x fuel y k = 1 ∧
          ∀ j, 1 ≤ j → j < ordAux x fuel y k → ι x ^ j ≠ 1))
  | 0, y, k, _, _, _, hmin => Or.inl ⟨by simp [ordAux], by simpa using hmin⟩
  | fuel + 1, y, k, hy, hyk, hk, hmin => by
    by_cases hye : y = oneE
    · right
      subst hye
      refine ⟨?_, ?_, ?_⟩
      · simp [ordAux]
      · simp [ordAux]; rw [← hyk, hM.map_one]
      · simpa [ordAux] using hmin
    · have hne : ι x ^ k ≠ 1 := by
        intro h1
        apply hye
        apply hM.inj _ _ hy hM.valid_one
        rw [hyk, h1, hM.map_one]
      have hstep : ordAux x (fuel + 1) y k = ordAux x fuel (mulE y x) (k + 1) := by
        simp [ordAux, hye]
      rw [hstep]
      have := ordAux_spec hx fuel (mulE y x) (k + 1) (hM.valid_mul _ _ hy hx)
        (by rw [hM.map_mul _ _ hy hx, hyk, pow_succ]) (by omega)
        (fun j hj1 hj2 => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with h | h
          · exact hmin j hj1 h
          · rw [h]; exact hne)
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · left
        refine ⟨by omega, fun j hj1 hj2 => h2 j hj1 (by omega)⟩
      · right
        exact ⟨by omega, h2, h3⟩

theorem ordE_spec {x : E} (hx : validE x = true) :
    (ordE x = 301 ∧ ∀ j, 1 ≤ j → j < 301 → ι x ^ j ≠ 1) ∨
      (ordE x < 301 ∧ ι x ^ ordE x = 1 ∧ ∀ j, 1 ≤ j → j < ordE x → ι x ^ j ≠ 1) := by
  have := hM.ordAux_spec hx 300 x 1 hx (by simp) le_rfl (fun j h1 h2 => by omega)
  exact this

theorem orderOf_of_ordE {x : E} (hx : validE x = true) {n : ℕ} (h : ordE x = n) (hn : n ≤ 300) :
    orderOf (ι x) = n := by
  rcases hM.ordE_spec hx with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
  · omega
  · rw [← h]
    exact (orderOf_eq_iff (ordE_pos x)).2 ⟨h2, fun m hm hm0 => h3 m hm0 hm⟩

theorem ordE_of_orderOf {x : E} (hx : validE x = true) {n : ℕ} (h : orderOf (ι x) = n) (hn1 : 1 ≤ n)
    (hn : n ≤ 300) : ordE x = n := by
  rcases hM.ordE_spec hx with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exfalso
    have hpos : 0 < orderOf (ι x) := by omega
    have := pow_orderOf_eq_one (ι x)
    exact h2 (orderOf (ι x)) hpos (by omega) this
  · have := (orderOf_eq_iff (ordE_pos x)).2 ⟨h2, fun m hm hm0 => h3 m hm0 hm⟩
    exact this.symm.trans h

end Model

end CFSG.GH74.GLS.LU.Local.FiveStd
