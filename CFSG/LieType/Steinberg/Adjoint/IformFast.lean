module

public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

@[expose] def iform6 (u v : Fin 6 → ℤ) : ℤ :=
  2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5)
    - (u 0 * v 2 + u 2 * v 0) - (u 1 * v 3 + u 3 * v 1) - (u 2 * v 3 + u 3 * v 2)
    - (u 3 * v 4 + u 4 * v 3) - (u 4 * v 5 + u 5 * v 4)

theorem iform_eq_iform6 (u v : Fin Tag.E6.rank → ℤ) : iform u v = iform6 u v := by
  change ∑ i : Fin 6, ∑ j : Fin 6, u i * Tag.symmetrizedCartan Tag.E6 i j * v j = _
  have h : ∀ i j : Fin 6, Tag.symmetrizedCartan Tag.E6 i j = Tag.cartanE 6 i j := by
    intro i j
    show ((1 : Matrix (Fin 6) (Fin 6) ℤ) * Tag.cartanE 6) i j = _
    rw [Matrix.one_mul]
  simp only [h, Fin.sum_univ_six, iform6]
  simp [Tag.cartanE]
  ring

@[expose] def iform8 (u v : Fin 8 → ℤ) : ℤ :=
  2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5 + u 6 * v 6 +
      u 7 * v 7)
    - (u 0 * v 2 + u 2 * v 0) - (u 1 * v 3 + u 3 * v 1) - (u 2 * v 3 + u 3 * v 2)
    - (u 3 * v 4 + u 4 * v 3) - (u 4 * v 5 + u 5 * v 4) - (u 5 * v 6 + u 6 * v 5)
    - (u 6 * v 7 + u 7 * v 6)

theorem iform_eq_iform8 (u v : Fin Tag.E8.rank → ℤ) : iform u v = iform8 u v := by
  change ∑ i : Fin 8, ∑ j : Fin 8, u i * Tag.symmetrizedCartan Tag.E8 i j * v j = _
  have h : ∀ i j : Fin 8, Tag.symmetrizedCartan Tag.E8 i j = Tag.cartanE 8 i j := by
    intro i j
    show ((1 : Matrix (Fin 8) (Fin 8) ℤ) * Tag.cartanE 8) i j = _
    rw [Matrix.one_mul]
  simp only [h, Fin.sum_univ_eight, iform8]
  simp [Tag.cartanE]
  ring

theorem iform_E8_fun : (iform : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ) = iform8 :=
  funext fun u => funext fun v => iform_eq_iform8 u v

@[expose] def iformF4 (u v : Fin 4 → ℤ) : ℤ :=
  4 * u 0 * v 0 + 4 * u 1 * v 1 + 2 * u 2 * v 2 + 2 * u 3 * v 3 - 2 * (u 0 * v 1 + u 1 * v 0)
    - 2 * (u 1 * v 2 + u 2 * v 1) - (u 2 * v 3 + u 3 * v 2)

@[expose] def scF4 : Fin 4 → Fin 4 → ℤ :=
  ![![4, -2, 0, 0], ![-2, 4, -2, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]]

theorem symmetrizedCartan_F4_pairs : ∀ p : Fin Tag.F4.rank × Fin Tag.F4.rank,
    Tag.symmetrizedCartan Tag.F4 p.1 p.2 = scF4 p.1 p.2 := by
  decide +kernel

theorem symmetrizedCartan_F4_eq (i j : Fin 4) : Tag.symmetrizedCartan Tag.F4 i j = scF4 i j :=
  symmetrizedCartan_F4_pairs (i, j)

theorem iform_eq_iformF4 (u v : Fin Tag.F4.rank → ℤ) : iform u v = iformF4 u v := by
  change ∑ i : Fin 4, ∑ j : Fin 4, u i * Tag.symmetrizedCartan Tag.F4 i j * v j = _
  simp only [symmetrizedCartan_F4_eq, Fin.sum_univ_four, iformF4, scF4]
  simp
  ring

end CFSG.LieType.Steinberg.Adjoint
