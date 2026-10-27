module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinData
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

open Equiv

theorem swap_conj_mem {K : Subgroup (Perm (Fin 6))} {π : Perm (Fin 6)} (hπ : π ∈ K) {x y : Fin 6}
    (h : swap x y ∈ K) : swap (π x) (π y) ∈ K := by
  rw [Equiv.swap_apply_apply]
  exact K.mul_mem (K.mul_mem hπ h) (K.inv_mem hπ)

theorem top_of_swaps {K : Subgroup (Perm (Fin 6))} (h : ∀ x y : Fin 6, x ≠ y → swap x y ∈ K) :
    K = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  exact h x y hxy

theorem top_of_Y2 {K : Subgroup (Perm (Fin 6))} (hY : ∀ π ∈ Y2L, π ∈ K)
    (hiso : ∀ x y : Fin 6, x ≠ y → swap x y ∈ K →
      ∃ u v : Fin 6, u ≠ v ∧ swap u v ∈ K ∧ swap u v * swap x y ≠ swap x y * swap u v) :
    K = ⊤ := by
  have h45 : swap 4 5 ∈ K := hY _ (by decide)
  have key : ∀ u v : Fin 6, u ≠ v → swap u v * swap 4 5 ≠ swap 4 5 * swap u v →
      ((u = 4 ∨ u = 5) ∧ v < 4) ∨ (u < 4 ∧ (v = 4 ∨ v = 5)) := by decide
  have hV : ∀ v x : Fin 6, v < 4 → x < 4 → ∃ π ∈ Y2L, π v = x ∧ π 4 = 4 := by decide
  have e5 : ∀ v : Fin 6, v < 4 → swap (swap 4 5 5) (swap 4 5 v) = swap 4 v := by decide
  have e4 : ∀ v : Fin 6, v < 4 → swap (swap 4 5 4) (swap 4 5 v) = swap 5 v := by decide
  have hall : ∀ x : Fin 6, x < 4 ∨ x = 4 ∨ x = 5 := by decide
  have hswap : ∀ x y : Fin 6, swap x y ∈ K → swap y x ∈ K := fun x y h => by
    rwa [Equiv.swap_comm]
  have hcross : ∃ w : Fin 6, w < 4 ∧ swap 4 w ∈ K := by
    obtain ⟨u, v, huv, huvK, hnc⟩ := hiso 4 5 (by decide) h45
    rcases key u v huv hnc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases hu with rfl | rfl
      · exact ⟨v, hv, huvK⟩
      · refine ⟨v, hv, ?_⟩
        have := swap_conj_mem h45 huvK
        rwa [e5 v hv] at this
    · rcases hv with rfl | rfl
      · exact ⟨u, hu, hswap _ _ huvK⟩
      · refine ⟨u, hu, ?_⟩
        have := swap_conj_mem h45 (hswap _ _ huvK)
        rwa [e5 u hu] at this
  have h4 : ∀ x : Fin 6, x < 4 → swap 4 x ∈ K := by
    obtain ⟨w, hw, hK⟩ := hcross
    intro x hx
    obtain ⟨π, hπ, h1, h2⟩ := hV w x hw hx
    have := swap_conj_mem (hY π hπ) hK
    rwa [h1, h2] at this
  have h5 : ∀ x : Fin 6, x < 4 → swap 5 x ∈ K := by
    intro x hx
    have := swap_conj_mem h45 (h4 x hx)
    rwa [e4 x hx] at this
  have hb : ∀ x y : Fin 6, x < 4 → y < 4 → x ≠ y → swap x y ∈ K := by
    have e : ∀ x y : Fin 6, x < 4 → y < 4 → x ≠ y →
        swap (swap 4 x 4) (swap 4 x y) = swap x y := by decide
    intro x y hx hy hxy
    have := swap_conj_mem (π := swap 4 x) (h4 x hx) (h4 y hy)
    rwa [e x y hx hy hxy] at this
  refine top_of_swaps fun x y hxy => ?_
  rcases hall x with hx | rfl | rfl <;> rcases hall y with hy | rfl | rfl
  · exact hb x y hx hy hxy
  · exact hswap _ _ (h4 x hx)
  · exact hswap _ _ (h5 x hx)
  · exact h4 y hy
  · exact absurd rfl hxy
  · exact h45
  · exact h5 y hy
  · exact hswap _ _ h45
  · exact absurd rfl hxy

@[expose] def repY1 (x : Fin 6) : Fin 6 := ![0, 0, 2, 2, 4, 4] x

theorem top_of_Y1 {K : Subgroup (Perm (Fin 6))} (hY : ∀ π ∈ Y1L, π ∈ K)
    (hiso : ∀ x y : Fin 6, x ≠ y → swap x y ∈ K →
      ∃ u v : Fin 6, u ≠ v ∧ swap u v ∈ K ∧ swap u v * swap x y ≠ swap x y * swap u v) :
    K = ⊤ := by
  have h01 : swap 0 1 ∈ K := hY _ (by decide)
  have h23 : swap 2 3 ∈ K := hY _ (by decide)
  have h45 : swap 4 5 ∈ K := hY _ (by decide)
  have hswap : ∀ x y : Fin 6, swap x y ∈ K → swap y x ∈ K := fun x y h => by
    rwa [Equiv.swap_comm]
  have hrep : ∀ u : Fin 6, repY1 u = 0 ∨ repY1 u = 2 ∨ repY1 u = 4 := by decide
  have hdown : ∀ u v : Fin 6, repY1 u ≠ repY1 v →
      ∃ π ∈ Y1L, π u = repY1 u ∧ π v = repY1 v := by decide
  have hup : ∀ u v : Fin 6, repY1 u ≠ repY1 v →
      ∃ π ∈ Y1L, π (repY1 u) = u ∧ π (repY1 v) = v := by decide
  have down : ∀ u v : Fin 6, repY1 u ≠ repY1 v → swap u v ∈ K → swap (repY1 u) (repY1 v) ∈ K := by
    intro u v h huv
    obtain ⟨π, hπ, h1, h2⟩ := hdown u v h
    have := swap_conj_mem (hY π hπ) huv
    rwa [h1, h2] at this
  have up : ∀ u v : Fin 6, repY1 u ≠ repY1 v → swap (repY1 u) (repY1 v) ∈ K → swap u v ∈ K := by
    intro u v h huv
    obtain ⟨π, hπ, h1, h2⟩ := hup u v h
    have := swap_conj_mem (hY π hπ) huv
    rwa [h1, h2] at this
  have link : ∀ b : Fin 6, (∃ u v : Fin 6, u ≠ v ∧ swap u v ∈ K ∧
      ((repY1 u = b ∧ repY1 v ≠ b) ∨ (repY1 u ≠ b ∧ repY1 v = b))) →
      ∃ c : Fin 6, c ≠ b ∧ (c = 0 ∨ c = 2 ∨ c = 4) ∧ swap b c ∈ K := by
    rintro b ⟨u, v, huv, hK, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨repY1 v, h2, hrep v, ?_⟩
      have := down u v (fun h => h2 (h ▸ h1)) hK
      rwa [h1] at this
    · refine ⟨repY1 u, h1, hrep u, ?_⟩
      have := down u v (fun h => h1 (h ▸ h2)) hK
      rw [h2] at this
      exact hswap _ _ this
  have key0 : ∀ u v : Fin 6, u ≠ v → swap u v * swap 0 1 ≠ swap 0 1 * swap u v →
      (repY1 u = 0 ∧ repY1 v ≠ 0) ∨ (repY1 u ≠ 0 ∧ repY1 v = 0) := by decide
  have key2 : ∀ u v : Fin 6, u ≠ v → swap u v * swap 2 3 ≠ swap 2 3 * swap u v →
      (repY1 u = 2 ∧ repY1 v ≠ 2) ∨ (repY1 u ≠ 2 ∧ repY1 v = 2) := by decide
  have key4 : ∀ u v : Fin 6, u ≠ v → swap u v * swap 4 5 ≠ swap 4 5 * swap u v →
      (repY1 u = 4 ∧ repY1 v ≠ 4) ∨ (repY1 u ≠ 4 ∧ repY1 v = 4) := by decide
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c : Fin 6, c ≠ 0 ∧ (c = 0 ∨ c = 2 ∨ c = 4) ∧ swap 0 c ∈ K := by
    refine link 0 ?_
    obtain ⟨u, v, huv, hK, hnc⟩ := hiso 0 1 (by decide) h01
    exact ⟨u, v, huv, hK, key0 u v huv hnc⟩
  obtain ⟨c2, hc2, hc2'⟩ : ∃ c : Fin 6, c ≠ 2 ∧ (c = 0 ∨ c = 2 ∨ c = 4) ∧ swap 2 c ∈ K := by
    refine link 2 ?_
    obtain ⟨u, v, huv, hK, hnc⟩ := hiso 2 3 (by decide) h23
    exact ⟨u, v, huv, hK, key2 u v huv hnc⟩
  obtain ⟨c4, hc4, hc4'⟩ : ∃ c : Fin 6, c ≠ 4 ∧ (c = 0 ∨ c = 2 ∨ c = 4) ∧ swap 4 c ∈ K := by
    refine link 4 ?_
    obtain ⟨u, v, huv, hK, hnc⟩ := hiso 4 5 (by decide) h45
    exact ⟨u, v, huv, hK, key4 u v huv hnc⟩
  have f0 : swap 0 2 ∈ K ∨ swap 0 4 ∈ K := by
    rcases hc0'.1 with rfl | rfl | rfl
    · exact absurd rfl hc0
    · exact Or.inl hc0'.2
    · exact Or.inr hc0'.2
  have f2 : swap 0 2 ∈ K ∨ swap 2 4 ∈ K := by
    rcases hc2'.1 with rfl | rfl | rfl
    · exact Or.inl (hswap _ _ hc2'.2)
    · exact absurd rfl hc2
    · exact Or.inr hc2'.2
  have f4 : swap 0 4 ∈ K ∨ swap 2 4 ∈ K := by
    rcases hc4'.1 with rfl | rfl | rfl
    · exact Or.inl (hswap _ _ hc4'.2)
    · exact Or.inr (hswap _ _ hc4'.2)
    · exact absurd rfl hc4
  have t1 : swap 0 2 ∈ K → swap 0 4 ∈ K → swap 2 4 ∈ K := fun ha hb => by
    have := swap_conj_mem ha hb
    have e : swap (swap (0 : Fin 6) 2 0) (swap 0 2 4) = swap 2 4 := by decide
    rwa [e] at this
  have t2 : swap 0 2 ∈ K → swap 2 4 ∈ K → swap 0 4 ∈ K := fun ha hb => by
    have := swap_conj_mem ha hb
    have e : swap (swap (0 : Fin 6) 2 2) (swap 0 2 4) = swap 0 4 := by decide
    rwa [e] at this
  have t3 : swap 0 4 ∈ K → swap 2 4 ∈ K → swap 0 2 ∈ K := fun ha hb => by
    have := swap_conj_mem ha hb
    have e : swap (swap (0 : Fin 6) 4 2) (swap 0 4 4) = swap 2 0 := by decide
    rw [e] at this
    exact hswap _ _ this
  have hall : swap 0 2 ∈ K ∧ swap 0 4 ∈ K ∧ swap 2 4 ∈ K := by
    rcases f0 with ha | hb
    · rcases f4 with hb | hc
      · exact ⟨ha, hb, t1 ha hb⟩
      · exact ⟨ha, t2 ha hc, hc⟩
    · rcases f2 with ha | hc
      · exact ⟨ha, hb, t1 ha hb⟩
      · exact ⟨t3 hb hc, hb, hc⟩
  have hl : ∀ a b : Fin 6, (a = 0 ∨ a = 2 ∨ a = 4) → (b = 0 ∨ b = 2 ∨ b = 4) → a ≠ b →
      swap a b ∈ K := by
    rintro a b (rfl | rfl | rfl) (rfl | rfl | rfl) hab
    · exact absurd rfl hab
    · exact hall.1
    · exact hall.2.1
    · exact hswap _ _ hall.1
    · exact absurd rfl hab
    · exact hall.2.2
    · exact hswap _ _ hall.2.1
    · exact hswap _ _ hall.2.2
    · exact absurd rfl hab
  have hsame : ∀ x y : Fin 6, x ≠ y → repY1 x = repY1 y → swap x y ∈ K := by
    have : ∀ x y : Fin 6, x ≠ y → repY1 x = repY1 y →
        (swap x y = swap 0 1 ∨ swap x y = swap 2 3 ∨ swap x y = swap 4 5) := by decide
    intro x y hxy h
    rcases this x y hxy h with e | e | e <;> rw [e] <;> assumption
  refine top_of_swaps fun x y hxy => ?_
  by_cases h : repY1 x = repY1 y
  · exact hsame x y hxy h
  · exact up x y h (hl _ _ (hrep x) (hrep y) h)

end CFSG.GF2Type.Aschbacher1976Full.HS.TransFin
