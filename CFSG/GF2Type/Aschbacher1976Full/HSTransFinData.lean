module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteWlog

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.Six

@[expose] def Y1L : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5]

@[expose] def Y2L : List (Perm (Fin 6)) :=
  [1, dt 0 1 2 3, dt 0 2 1 3, dt 0 3 1 2, swap 4 5, dt 0 1 2 3 * swap 4 5, dt 0 2 1 3 * swap 4 5,
    dt 0 3 1 2 * swap 4 5]

theorem Y1L_nodup : Y1L.Nodup := by decide +kernel

theorem Y2L_nodup : Y2L.Nodup := by decide +kernel

theorem Y1L_length : Y1L.length = 8 := by decide +kernel

theorem Y2L_length : Y2L.length = 8 := by decide +kernel

theorem cenA : ∀ x ∈ allT 6, mulT x (tab dA) = mulT (tab dA) x →
    mulT x (tab eA) = mulT (tab eA) x → x ∈ Y1L.map tab := by
  decide +kernel

theorem cenB : ∀ x ∈ allT 6, mulT x (tab dB) = mulT (tab dB) x →
    mulT x (tab eB) = mulT (tab eB) x → x ∈ Y2L.map tab := by
  decide +kernel

theorem witA : ∀ a ∈ Y1L.map tab, a ≠ oneT 6 → ∃ g ∈ invsT,
    mulT (mulT (mulT a g) (mulT a g)) (mulT (mulT a g) (mulT a g)) = oneT 6 ∧
    ∃ x ∈ Y1L.map tab, cjT g x ∉ Y1L.map tab := by
  decide +kernel

theorem witB : ∀ a ∈ Y2L.map tab, a ≠ oneT 6 → ∃ g ∈ invsT,
    mulT (mulT (mulT a g) (mulT a g)) (mulT (mulT a g) (mulT a g)) = oneT 6 ∧
    ∃ x ∈ Y2L.map tab, cjT g x ∉ Y2L.map tab := by
  decide +kernel

theorem witness_of_tables (L : List (Perm (Fin 6)))
    (hw : ∀ a ∈ L.map tab, a ≠ oneT 6 → ∃ g ∈ invsT,
      mulT (mulT (mulT a g) (mulT a g)) (mulT (mulT a g) (mulT a g)) = oneT 6 ∧
      ∃ x ∈ L.map tab, cjT g x ∉ L.map tab)
    {x : Perm (Fin 6)} (hx : x ∈ L) (hx1 : x ≠ 1) :
    ∃ g : Perm (Fin 6), g * g = 1 ∧ (x * g) ^ 4 = 1 ∧ ∃ x₀ ∈ L, g * x₀ * g⁻¹ ∉ L := by
  have hx1' : tab x ≠ oneT 6 := fun h => hx1 (tab_injective (h.trans tab_one.symm))
  obtain ⟨g', hg', h4, x₀', hx₀', hn⟩ := hw (tab x) (List.mem_map_of_mem hx) hx1'
  have hg'' : g' ∈ allT 6 := (List.mem_filter.1 hg').1
  have hg2' : mulT g' g' = oneT 6 := by
    have := (List.mem_filter.1 hg').2
    simpa using this
  obtain ⟨g, rfl⟩ := exists_of_mem_allT hg''
  obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.1 hx₀'
  refine ⟨g, ?_, ?_, x₀, hx₀, ?_⟩
  · apply tab_injective
    rw [tab_mul, hg2', tab_one]
  · apply tab_injective
    have e : (x * g) ^ 4 = (x * g * (x * g)) * (x * g * (x * g)) := by simp [pow_succ, mul_assoc]
    rw [e, tab_mul, tab_mul, tab_mul, tab_one]
    exact h4
  · intro h
    apply hn
    rw [← tab_conj]
    exact List.mem_map_of_mem h

end CFSG.GF2Type.Aschbacher1976Full.HS.TransFin
