module

public import CFSG.CharacterTheory.Wreathed.CharacteristicBase
public import CFSG.CharacterTheory.Wreathed.Generators

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def derivedCoordinateEquiv (m : ℕ) :
    Multiplicative (ZMod m) ≃* commutator (Wreath m) :=
  (MonoidHom.ofInjective (antiDiagonalHom_injective m)).trans
    (MulEquiv.subgroupCongr (by
      rw [derived_eq_zpowers, antiDiagonal_range_eq_zpowers]))

theorem card_derived (m : ℕ) : Nat.card (commutator (Wreath m)) = m := by
  rw [← Nat.card_congr (derivedCoordinateEquiv m).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem derived_isCyclic (m : ℕ) : IsCyclic (commutator (Wreath m)) :=
  (derivedCoordinateEquiv m).isCyclic.mp inferInstance

@[expose] def centerDerivedAction (m : ℕ) :
    MulAut (Wreath m) →* MulAut (Subgroup.center (Wreath m)) × MulAut (commutator (Wreath m)) :=
  (MulAut.characteristic (Subgroup.center (Wreath m))).prod
    (MulAut.characteristic (commutator (Wreath m)))

theorem centerDerivedAction_kernel_fixes_center (m : ℕ)
    (φ : (centerDerivedAction m).ker) (g : Wreath m)
    (hg : g ∈ Subgroup.center (Wreath m)) : φ.val g = g := by
  have hp : (MulAut.characteristic (Subgroup.center (Wreath m))) φ.val = 1 :=
    congrArg Prod.fst φ.property
  have heq := DFunLike.congr_fun hp (⟨g, hg⟩ : Subgroup.center (Wreath m))
  have hv := congrArg Subtype.val heq
  simpa only [MulAut.characteristic_apply_apply_coe, MulAut.one_apply] using hv

theorem centerDerivedAction_kernel_fixes_derived (m : ℕ)
    (φ : (centerDerivedAction m).ker) (g : Wreath m)
    (hg : g ∈ commutator (Wreath m)) : φ.val g = g := by
  have hp : (MulAut.characteristic (commutator (Wreath m))) φ.val = 1 :=
    congrArg Prod.snd φ.property
  have heq := DFunLike.congr_fun hp (⟨g, hg⟩ : commutator (Wreath m))
  have hv := congrArg Subtype.val heq
  simpa only [MulAut.characteristic_apply_apply_coe, MulAut.one_apply] using hv

theorem automorphism_mem_base_iff (m : ℕ) (hm : 2 < m) (φ : MulAut (Wreath m))
    (g : Wreath m) : φ g ∈ baseSubgroup m ↔ g ∈ baseSubgroup m := by
  have hchar := base_characteristic m hm
  have hc := hchar.fixed φ
  change g ∈ (baseSubgroup m).comap φ.toMonoidHom ↔ g ∈ baseSubgroup m
  rw [hc]

theorem automorphism_swap_coordinates (m : ℕ) (hm : 2 < m) (φ : MulAut (Wreath m)) :
    ∃ u : ZMod m, φ (element m 0 0 1) = element m u (-u) 1 := by
  obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv m).symm.surjective (φ (element m 0 0 1))
  change element m a b e = φ (element m 0 0 1) at heq
  have he : e = 1 := by
    rcases swap_exponent_cases e with he | he
    · have hmem : φ (element m 0 0 1) ∈ baseSubgroup m := by
        rw [← heq, element_mem_base, he]
      have hb := (automorphism_mem_base_iff m hm φ _).mp hmem
      have hbad := (element_mem_base m 0 0 1).mp hb
      exact False.elim (one_ne_zero hbad)
    · exact he
  rw [he] at heq
  have hsq : element m a b 1 ^ 2 = 1 := by
    rw [heq, ← map_pow, element_swap_sq]
    simp
  rw [element_swap_sq, element_base_eq_one_iff] at hsq
  have hb : b = -a := by linear_combination hsq.1
  exact ⟨a, by rw [← heq, hb]⟩

theorem centerDerivedAction_kernel_base_coordinates (m : ℕ) (hm : 2 < m)
    (φ : (centerDerivedAction m).ker) :
    ∃ c : ZMod m, φ.val (element m 1 0 0) = element m (1 + c) c 0 ∧ 2 • c = 0 := by
  obtain ⟨⟨b, c, e⟩, hs⟩ := (coordinateEquiv m).symm.surjective (φ.val (element m 1 0 0))
  change element m b c e = φ.val (element m 1 0 0) at hs
  have he : e = 0 := by
    have hmem := (automorphism_mem_base_iff m hm φ.val (element m 1 0 0)).mpr (by simp)
    rw [← hs, element_mem_base] at hmem
    exact hmem
  rw [he] at hs
  obtain ⟨u, hz⟩ := automorphism_swap_coordinates m hm φ.val
  have ht : φ.val (element m 0 1 0) = element m c b 0 := by
    have hconj : element m 0 0 1 * element m 1 0 0 * (element m 0 0 1)⁻¹ =
        element m 0 1 0 := conjugate_base_by_swap m 1 0 0 0
    rw [← hconj, map_mul, map_mul, map_inv, hz, ← hs, conjugate_base_by_swap]
  have ha : φ.val (element m 1 1 0) = element m 1 1 0 :=
    centerDerivedAction_kernel_fixes_center m φ _
      ((element_mem_center_iff m (by omega) 1 1 0).mpr ⟨rfl, rfl⟩)
  have hr : φ.val (element m 1 (-1) 0) = element m 1 (-1) 0 := by
    apply centerDerivedAction_kernel_fixes_derived m φ
    rw [derived_eq_zpowers]
    exact Subgroup.mem_zpowers _
  have ha' : b + c = 1 := by
    have hmul : element m 1 0 0 * element m 0 1 0 = element m 1 1 0 := by
      simp only [element_base_mul, add_zero, zero_add]
    rw [← hmul, map_mul, ← hs, ht, element_base_mul] at ha
    rw [hmul] at ha
    exact ((element_eq_iff _ _ _ _ _ _ _).mp ha).1
  have hr' : b - c = 1 := by
    have hmul : element m 1 0 0 * (element m 0 1 0)⁻¹ = element m 1 (-1) 0 := by
      rw [element_base_inv, element_base_mul]
      simp
    rw [← hmul, map_mul, map_inv, ← hs, ht, element_base_inv, element_base_mul] at hr
    rw [hmul] at hr
    have heq := ((element_eq_iff _ _ _ _ _ _ _).mp hr).1
    simpa only [sub_eq_add_neg] using heq
  have hc : 2 • c = 0 := by
    rw [two_nsmul]
    linear_combination ha' - hr'
  have hb : b = 1 + c := by linear_combination hr'
  exact ⟨c, by rw [← hs, hb], hc⟩

theorem centerDerivedAction_kernel_s_displacement (m : ℕ) (hm : 2 < m)
    (φ : (centerDerivedAction m).ker) :
    φ.val (element m 1 0 0) * (element m 1 0 0)⁻¹ ∈ Subgroup.center (Wreath m) := by
  obtain ⟨c, hs, _⟩ := centerDerivedAction_kernel_base_coordinates m hm φ
  rw [hs, element_base_inv, element_base_mul]
  have heq : element m (1 + c + -1) (c + -0) 0 = element m c c 0 := by
    rw [element_eq_iff]
    refine ⟨?_, ?_, rfl⟩ <;> abel
  rw [heq, element_mem_center_iff m (by omega)]
  exact ⟨rfl, rfl⟩

theorem centerDerivedAction_kernel_z_displacement (m : ℕ) (hm : 2 < m)
    (φ : (centerDerivedAction m).ker) :
    φ.val (element m 0 0 1) * (element m 0 0 1)⁻¹ ∈ commutator (Wreath m) := by
  obtain ⟨u, hz⟩ := automorphism_swap_coordinates m hm φ.val
  rw [hz, element_swap_inv, element_swap_mul,
    show (1 + 1 : ZMod 2) = 0 by decide]
  rw [derived_eq_zpowers, ← antiDiagonal_range_eq_zpowers]
  refine ⟨Multiplicative.ofAdd u, ?_⟩
  change element m u (-u) 0 = element m (u + -0) (-u + -0) 0
  simp

theorem centerDerivedAction_kernel_displacement_mul (m : ℕ)
    (φ ψ : (centerDerivedAction m).ker) (g : Wreath m)
    (hfix : φ.val (ψ.val g * g⁻¹) = ψ.val g * g⁻¹)
    (hcomm : Commute (ψ.val g * g⁻¹) (φ.val g * g⁻¹)) :
    (φ * ψ).val g * g⁻¹ = (φ.val g * g⁻¹) * (ψ.val g * g⁻¹) := by
  have hψ : ψ.val g = (ψ.val g * g⁻¹) * g := by group
  change φ.val (ψ.val g) * g⁻¹ = _
  calc
    φ.val (ψ.val g) * g⁻¹ = φ.val ((ψ.val g * g⁻¹) * g) * g⁻¹ :=
      congrArg (fun a => φ.val a * g⁻¹) hψ
    _ = (ψ.val g * g⁻¹) * φ.val g * g⁻¹ := by rw [map_mul, hfix]
    _ =
        (ψ.val g * g⁻¹) * (φ.val g * g⁻¹) := mul_assoc _ _ _
    _ = (φ.val g * g⁻¹) * (ψ.val g * g⁻¹) := hcomm.eq

@[expose] def centerDerivedKernelDisplacement (m : ℕ) (hm : 2 < m) :
    (centerDerivedAction m).ker →*
      Subgroup.center (Wreath m) × commutator (Wreath m) where
  toFun φ :=
    (⟨φ.val (element m 1 0 0) * (element m 1 0 0)⁻¹,
      centerDerivedAction_kernel_s_displacement m hm φ⟩,
     ⟨φ.val (element m 0 0 1) * (element m 0 0 1)⁻¹,
      centerDerivedAction_kernel_z_displacement m hm φ⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_mul' φ ψ := by
    let : IsCyclic (commutator (Wreath m)) := derived_isCyclic m
    apply Prod.ext
    · apply Subtype.ext
      apply centerDerivedAction_kernel_displacement_mul
      · exact centerDerivedAction_kernel_fixes_center m φ _
          (centerDerivedAction_kernel_s_displacement m hm ψ)
      · exact (Subgroup.mem_center_iff.mp
          (centerDerivedAction_kernel_s_displacement m hm φ) _)
    · apply Subtype.ext
      apply centerDerivedAction_kernel_displacement_mul
      · exact centerDerivedAction_kernel_fixes_derived m φ _
          (centerDerivedAction_kernel_z_displacement m hm ψ)
      · have hcomm := (isMulCommutative_iff.mp
          (inferInstance : IsMulCommutative (commutator (Wreath m))))
          (⟨ψ.val (element m 0 0 1) * (element m 0 0 1)⁻¹,
            centerDerivedAction_kernel_z_displacement m hm ψ⟩ : commutator (Wreath m))
          ⟨φ.val (element m 0 0 1) * (element m 0 0 1)⁻¹,
            centerDerivedAction_kernel_z_displacement m hm φ⟩
        exact congrArg Subtype.val hcomm

theorem centerDerivedKernelDisplacement_injective (m : ℕ) (hm : 2 < m) :
    Function.Injective (centerDerivedKernelDisplacement m hm) := by
  intro φ ψ h
  have hs : φ.val (element m 1 0 0) = ψ.val (element m 1 0 0) := by
    have heq := congrArg (fun p : Subgroup.center (Wreath m) × commutator (Wreath m) =>
      p.1.val) h
    change φ.val (element m 1 0 0) * (element m 1 0 0)⁻¹ =
      ψ.val (element m 1 0 0) * (element m 1 0 0)⁻¹ at heq
    exact mul_right_cancel heq
  have hz : φ.val (element m 0 0 1) = ψ.val (element m 0 0 1) := by
    have heq := congrArg (fun p : Subgroup.center (Wreath m) × commutator (Wreath m) =>
      p.2.val) h
    change φ.val (element m 0 0 1) * (element m 0 0 1)⁻¹ =
      ψ.val (element m 0 0 1) * (element m 0 0 1)⁻¹ at heq
    exact mul_right_cancel heq
  apply Subtype.ext
  exact MulEquiv.toMonoidHom_injective (wreathHom_ext m hs hz)

end CFSG.Wreathed
