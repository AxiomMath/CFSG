module

public import CFSG.CharacterTheory.Wreathed.Coordinates

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def diagonalHom (m : ℕ) : Multiplicative (ZMod m) →* Wreath m where
  toFun a := element m (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0
  map_one' := by simp
  map_mul' a b := by
    change element m (Multiplicative.toAdd a + Multiplicative.toAdd b)
      (Multiplicative.toAdd a + Multiplicative.toAdd b) 0 = _
    rw [element_base_mul]

theorem diagonalHom_injective (m : ℕ) : Function.Injective (diagonalHom m) := by
  intro a b h
  have hc := congrArg (fun g : Wreath m => g.left (Multiplicative.ofAdd 0)) h
  simpa [diagonalHom, element] using hc

theorem element_mem_center_iff (m : ℕ) (hm : 1 < m)
    (a b : ZMod m) (e : ZMod 2) :
    element m a b e ∈ Subgroup.center (Wreath m) ↔ e = 0 ∧ a = b := by
  let : Fact (1 < m) := ⟨hm⟩
  constructor
  · intro h
    have hswap := Subgroup.mem_center_iff.mp h (element m 0 0 1)
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_swap_mul, element_base_mul] at hswap
      have hc := congrArg (fun g : Wreath m =>
        Multiplicative.toAdd (g.left (Multiplicative.ofAdd 0))) hswap
      simp only [element_left_zero] at hc
      change 0 + b = a + 0 at hc
      rw [zero_add, add_zero] at hc
      exact ⟨rfl, hc.symm⟩
    · have hbase := Subgroup.mem_center_iff.mp h (element m 1 0 0)
      rw [element_base_mul, element_swap_mul] at hbase
      have hc := congrArg (fun g : Wreath m =>
        Multiplicative.toAdd (g.left (Multiplicative.ofAdd 0))) hbase
      simp only [element_left_zero] at hc
      change 1 + a = a + 0 at hc
      have hzero : (1 : ZMod m) = 0 := by linear_combination hc
      exact False.elim (one_ne_zero hzero)
  · rintro ⟨rfl, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    change element m c d f * element m a a 0 = element m a a 0 * element m c d f
    rcases swap_exponent_cases f with rfl | rfl
    · simp only [element_base_mul, add_comm]
    · rw [element_swap_mul, element_base_mul]
      simp only [add_comm, zero_add]

theorem center_eq_diagonal_range (m : ℕ) (hm : 1 < m) :
    Subgroup.center (Wreath m) = (diagonalHom m).range := by
  ext g
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b e ∈ Subgroup.center (Wreath m) ↔
    element m a b e ∈ (diagonalHom m).range
  rw [element_mem_center_iff m hm]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  · rintro ⟨c, hc⟩
    change element m (Multiplicative.toAdd c) (Multiplicative.toAdd c) 0 =
      element m a b e at hc
    have heq := element_injective m
      (a₁ := (Multiplicative.toAdd c, Multiplicative.toAdd c, 0)) (a₂ := (a, b, e)) hc
    exact ⟨(congrArg (fun x : ZMod m × ZMod m × ZMod 2 => x.2.2) heq).symm,
      (congrArg (fun x : ZMod m × ZMod m × ZMod 2 => x.1) heq).symm.trans
        (congrArg (fun x : ZMod m × ZMod m × ZMod 2 => x.2.1) heq)⟩

theorem diagonal_range_eq_zpowers (m : ℕ) :
    (diagonalHom m).range = Subgroup.zpowers (element m 1 1 0) := by
  have hgen : Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod m)) = ⊤ := by
    ext a
    simp only [Subgroup.mem_top, iff_true, Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
    refine ⟨k, ?_⟩
    apply Multiplicative.toAdd.injective
    change k • (1 : ZMod m) = Multiplicative.toAdd a
    simpa only [zsmul_eq_mul, mul_one] using hk
  change (diagonalHom m).range =
    Subgroup.zpowers ((diagonalHom m) (Multiplicative.ofAdd (1 : ZMod m)))
  rw [← MonoidHom.map_zpowers (diagonalHom m) (Multiplicative.ofAdd (1 : ZMod m)),
    hgen, MonoidHom.range_eq_map]

theorem center_eq_zpowers (m : ℕ) (hm : 1 < m) :
    Subgroup.center (Wreath m) = Subgroup.zpowers (element m 1 1 0) := by
  rw [center_eq_diagonal_range m hm, diagonal_range_eq_zpowers]

@[expose] def cyclicCenterEquiv (m : ℕ) (hm : 1 < m) :
    Multiplicative (ZMod m) ≃* Subgroup.center (Wreath m) :=
  (MonoidHom.ofInjective (diagonalHom_injective m)).trans
    (MulEquiv.subgroupCongr (center_eq_diagonal_range m hm).symm)

theorem card_center (m : ℕ) (hm : 1 < m) : Nat.card (Subgroup.center (Wreath m)) = m := by
  rw [← Nat.card_congr (cyclicCenterEquiv m hm).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem center_isCyclic (m : ℕ) (hm : 1 < m) : IsCyclic (Subgroup.center (Wreath m)) :=
  (cyclicCenterEquiv m hm).isCyclic.mp inferInstance

@[expose] def dihedralProjection (m : ℕ) : Wreath m →* DihedralGroup m where
  toFun g :=
    let c := coordinateEquiv m g
    if c.2.2 = 0 then DihedralGroup.r (c.1 - c.2.1)
    else DihedralGroup.sr (c.2.1 - c.1)
  map_one' := by
    change (if (coordinateEquiv m (element m 0 0 0)).2.2 = 0 then _ else _) = 1
    simp [coordinateEquiv, element]
  map_mul' g h := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective h
    change (let x := coordinateEquiv m (element m a b e * element m c d f)
      ; if x.2.2 = 0 then DihedralGroup.r (x.1 - x.2.1)
        else DihedralGroup.sr (x.2.1 - x.1)) =
      (if e = 0 then DihedralGroup.r (a - b) else DihedralGroup.sr (b - a)) *
        (if f = 0 then DihedralGroup.r (c - d) else DihedralGroup.sr (d - c))
    rcases swap_exponent_cases e with rfl | rfl <;>
      rcases swap_exponent_cases f with rfl | rfl
    · rw [element_base_mul]
      simp [coordinateEquiv, element]
      abel
    · rw [element_base_mul]
      simp [coordinateEquiv, element]
      abel
    · rw [element_swap_mul]
      simp [coordinateEquiv, element]
      abel
    · rw [element_swap_mul]
      simp [coordinateEquiv, element, show (1 + 1 : ZMod 2) = 0 by decide]
      abel

theorem dihedralProjection_surjective (m : ℕ) : Function.Surjective (dihedralProjection m) := by
  intro g
  cases g with
  | r a =>
    refine ⟨element m a 0 0, ?_⟩
    simp [dihedralProjection, coordinateEquiv, element]
  | sr a =>
    refine ⟨element m 0 a 1, ?_⟩
    simp [dihedralProjection, coordinateEquiv, element]

theorem dihedralProjection_ker_eq_center (m : ℕ) (hm : 1 < m) :
    (dihedralProjection m).ker = Subgroup.center (Wreath m) := by
  ext g
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b e ∈ (dihedralProjection m).ker ↔
    element m a b e ∈ Subgroup.center (Wreath m)
  rw [element_mem_center_iff m hm]
  rcases swap_exponent_cases e with rfl | rfl <;>
    simp [MonoidHom.mem_ker, dihedralProjection, coordinateEquiv, element,
      ← DihedralGroup.r_zero, sub_eq_zero]

@[expose] def centerQuotientEquivDihedral (m : ℕ) (hm : 1 < m) :
    Wreath m ⧸ Subgroup.center (Wreath m) ≃* DihedralGroup m :=
  (QuotientGroup.quotientMulEquivOfEq (dihedralProjection_ker_eq_center m hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (dihedralProjection m)
      (dihedralProjection_surjective m))

theorem card_center_quotient (m : ℕ) (hm : 1 < m) :
    Nat.card (Wreath m ⧸ Subgroup.center (Wreath m)) = 2 * m := by
  rw [Nat.card_congr (centerQuotientEquivDihedral m hm).toEquiv, DihedralGroup.nat_card]

end CFSG.Wreathed
