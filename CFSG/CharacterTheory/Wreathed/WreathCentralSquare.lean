module

public import CFSG.CharacterTheory.Wreathed.QuaternionCentralQuotient

public noncomputable section
namespace CFSG.Wreathed.WreathCentralSquare
universe u
open scoped Classical

@[expose] def originalRoot (m : ℕ) : Wreath m := Original.s m * Original.z m

theorem originalRoot_eq (m : ℕ) : originalRoot m = element m 1 0 1 := by
  simp [originalRoot, Original.s, Original.z, element_base_mul]

theorem originalRoot_sq (m : ℕ) : originalRoot m ^ 2 = Original.a m := by
  rw [originalRoot_eq, element_swap_sq, Original.a_eq, add_zero]

theorem originalRoot_pow_modulus (n : ℕ) (hn : 1 ≤ n) :
    originalRoot (2 ^ n) ^ (2 ^ n) = Original.x (2 ^ n) := by
  rw [← wreath_modulus_twice_half n hn, pow_mul, originalRoot_sq]
  simp only [Original.x, wreath_modulus_twice_half n hn]

@[expose] def parity (m : ℕ) (hm : 2 ∣ m) : Wreath m →* Multiplicative (ZMod 2) where
  toFun g :=
    let c := coordinateEquiv m g
    Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (c.1 + c.2.1))
  map_one' := by
    change Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (0 + 0)) = 1
    simp
  map_mul' g k := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective k
    change (let x := coordinateEquiv m (element m a b e * element m c d f)
      ; Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (x.1 + x.2.1))) =
      Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (a + b)) *
        Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (c + d))
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_base_mul]
      apply Multiplicative.toAdd.injective
      change ZMod.castHom hm (ZMod 2) (a + c+(b + d)) =
        ZMod.castHom hm (ZMod 2) (a + b) + ZMod.castHom hm (ZMod 2) (c + d)
      rw [← map_add]
      congr 1
      abel
    · rw [element_swap_mul]
      apply Multiplicative.toAdd.injective
      change ZMod.castHom hm (ZMod 2) (a + d+(b + c)) =
        ZMod.castHom hm (ZMod 2) (a + b) + ZMod.castHom hm (ZMod 2) (c + d)
      rw [← map_add]
      congr 1
      abel

theorem parity_element (m : ℕ) (hm : 2 ∣ m) (a b : ZMod m) (e : ZMod 2) :
    parity m hm (element m a b e) =
      Multiplicative.ofAdd (ZMod.castHom hm (ZMod 2) (a + b)) := rfl

theorem parity_originalRoot (m : ℕ) (hm : 2 ∣ m) :
    parity m hm (originalRoot m) = Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [originalRoot_eq, parity_element, add_zero, map_one]

theorem originalRoot_orderOf (n : ℕ) (hn : 2 ≤ n) :
    orderOf (originalRoot (2 ^ n)) = 2 * 2 ^ n := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx := (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  have hxne : Original.x (2 ^ n) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hnot : originalRoot (2 ^ n) ^ 2 ^ n ≠ 1 := by
    rw [originalRoot_pow_modulus n (by omega)]
    exact hxne
  have hfin : originalRoot (2 ^ n) ^ 2 ^ (n + 1) = 1 := by
    rw [pow_succ, Nat.mul_comm (2 ^ n) 2]
    exact element_pow_twice_modulus (2 ^ n) _
  simpa only [pow_succ, Nat.mul_comm] using orderOf_eq_prime_pow hnot hfin

theorem parity_surjective (m : ℕ) (hm : 2 ∣ m) :
    Function.Surjective (parity m hm) := by
  intro c
  rcases swap_exponent_cases c.toAdd with hc | hc
  · refine ⟨1, ?_⟩
    rw [map_one]
    apply Multiplicative.toAdd.injective
    exact hc.symm
  · exact ⟨originalRoot m, (parity_originalRoot m hm).trans (congrArg Multiplicative.ofAdd hc.symm)⟩

theorem parity_index (m : ℕ) (hm : 2 ∣ m) : (parity m hm).ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (parity_surjective m hm), Subgroup.card_top]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem parity_card (m : ℕ) (hm : 2 ∣ m) : Nat.card (parity m hm).ker = m ^ 2 := by
  have h := (parity m hm).ker.card_mul_index
  rw [parity_index m hm, card_wreath] at h
  omega

theorem original_Z_sup_Y_le_parity (n : ℕ) (hn : 2 ≤ n) :
    Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) ≤
      (parity (2 ^ n) (dvd_pow_self 2 (by omega : n ≠ 0))).ker := by
  let hm : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  change Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) ≤ (parity (2 ^ n) hm).ker
  apply sup_le
  · apply Subgroup.zpowers_le.mpr
    change parity (2 ^ n) hm (Original.a (2 ^ n)) = 1
    rw [Original.a_eq, parity_element, map_add, map_one]
    decide
  · rw [Original.Y, Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · rw [hg]
      change parity (2 ^ n) hm (Original.r (2 ^ n)) = 1
      rw [Original.r_eq, parity_element, add_neg_cancel, map_zero]
      rfl
    · rw [Set.mem_singleton_iff.mp hg]
      change parity (2 ^ n) hm (Original.d (2 ^ n)) = 1
      rw [Original.d_eq, parity_element, add_zero, map_natCast]
      have hhalf : 2 ∣ 2 ^ n / 2 := by
        have heq : 2 ^ n / 2 = 2 ^ (n - 1) := by
          change 2 ^ n / 2 ^ 1 = 2 ^ (n - 1)
          exact Nat.pow_div (by omega : 1 ≤ n) (by decide : 0 < 2)
        rw [heq]
        exact dvd_pow_self 2 (by omega : n - 1 ≠ 0)
      have hcast := (ZMod.natCast_eq_zero_iff (2 ^ n / 2) 2).mpr hhalf
      rw [hcast]
      rfl

theorem original_Z_sup_Y_index (n : ℕ) (hn : 2 ≤ n) :
    (Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n)).index = 2 := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨hYnormal, _, hYquot, _⟩ := hstructure.quaternion_quotient
  let := hYnormal
  have hYindex : (Original.Y (2 ^ n)).index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hYquot
  have hZcard : Nat.card (Original.Z (2 ^ n)) = 2 ^ n := by
    rw [Original.Z, Nat.card_zpowers, Original.orderOf_a]
  have hYZcard : Nat.card (Original.Y (2 ^ n) ⊓ Original.Z (2 ^ n) :
      Subgroup (Wreath (2 ^ n))) = 2 := by
    rw [inf_comm, original_Z_inf_Y n hn, Nat.card_zpowers]
    exact hstructure.involution_orders.1
  have hrel := Subgroup.relIndex_mul_card (Original.Y (2 ^ n)) (Original.Z (2 ^ n))
  rw [hYZcard, hZcard] at hrel
  have hproduct := Subgroup.relIndex_mul_index
    (show Original.Y (2 ^ n) ≤ Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) from le_sup_right)
  rw [Subgroup.relIndex_sup_right, hYindex] at hproduct
  have hnonzero : (Original.Y (2 ^ n)).relIndex (Original.Z (2 ^ n)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    have hpos : 0 < 2 ^ n := by positivity
    omega
  exact mul_left_cancel₀ hnonzero (hproduct.trans hrel.symm)

theorem original_Z_sup_Y_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) : Subgroup (Wreath (2 ^ n))) =
      (2 ^ n) ^ 2 := by
  have h := (Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n)).card_mul_index
  rw [original_Z_sup_Y_index n hn, card_wreath] at h
  omega

theorem parity_ker (n : ℕ) (hn : 2 ≤ n) :
    (parity (2 ^ n) (dvd_pow_self 2 (by omega : n ≠ 0))).ker =
      Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) := by
  apply (Subgroup.eq_of_le_of_card_ge (original_Z_sup_Y_le_parity n hn) ?_).symm
  rw [parity_card, original_Z_sup_Y_card n hn]

theorem originalRoot_not_mem_Z_sup_Y (n : ℕ) (hn : 2 ≤ n) :
    originalRoot (2 ^ n) ∉ Original.Z (2 ^ n) ⊔ Original.Y (2 ^ n) := by
  intro h
  have hp := original_Z_sup_Y_le_parity n hn h
  change parity (2 ^ n) _ (originalRoot (2 ^ n)) = 1 at hp
  rw [parity_originalRoot] at hp
  have hz := congrArg Multiplicative.toAdd hp
  exact one_ne_zero hz

variable {H : Type u} [Group H]

@[expose] def actualRoot {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) : H :=
  wreathModelHom S e (originalRoot m)

theorem actualRoot_eq {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) :
    actualRoot S e = wreathModelHom S e (Original.s m) *
      wreathModelHom S e (Original.z m) := map_mul _ _ _

theorem actualRoot_mem_sylow {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) :
    actualRoot S e ∈ (S : Subgroup H) := (e.symm (originalRoot m)).property

theorem actualRoot_sq {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) :
    actualRoot S e ^ 2 = wreathModelHom S e (Original.a m) := by
  rw [actualRoot, ← map_pow, originalRoot_sq]

theorem actualRoot_pow_modulus (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) :
    actualRoot S e ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [actualRoot, ← map_pow, originalRoot_pow_modulus n hn]

theorem actualRoot_orderOf (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (actualRoot S e) = 2 * 2 ^ n := by
  rw [actualRoot, orderOf_injective _ (wreathModelHom_injective S e), originalRoot_orderOf n hn]

theorem actualRoot_not_mem_center_sup_Y (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) :
    actualRoot S e ∉ modelCenter S e ⊔ modelY S e := by
  rw [modelCenter, modelY, ← Subgroup.map_sup]
  intro h
  obtain ⟨w, hw, heq⟩ := Subgroup.mem_map.mp h
  have hwroot : w = originalRoot (2 ^ n) := wreathModelHom_injective S e heq
  exact originalRoot_not_mem_Z_sup_Y n hn (hwroot ▸ hw)

theorem inf_normal_sup_of_le (S A M : Subgroup H) [M.Normal] (hAS : A ≤ S) :
    S ⊓ (A ⊔ M) = A ⊔ (S ⊓ M) := by
  apply le_antisymm
  · rintro x ⟨hxS, hx⟩
    obtain ⟨a, ha, m, hm, ham⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hmS : m ∈ S := by
      have hax : a⁻¹ * x ∈ S := S.mul_mem (S.inv_mem (hAS ha)) hxS
      rwa [← ham, inv_mul_cancel_left] at hax
    rw [← ham]
    exact (A ⊔ (S ⊓ M)).mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right ⟨hmS, hm⟩)
  · apply sup_le
    · exact le_inf hAS le_sup_left
    · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)

theorem actualRoot_not_mem_center_sup_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M : Subgroup H) [M.Normal]
    (hM : (S : Subgroup H) ⊓ M = modelY S e) :
    actualRoot S e ∉ modelCenter S e ⊔ M := by
  intro h
  have hA : modelCenter S e ≤ (S : Subgroup H) := by
    rw [modelCenter, ← wreathModelHom_range S e]
    exact Subgroup.map_le_range (f := wreathModelHom S e) (H := Original.Z (2 ^ n))
  have hi : actualRoot S e ∈ (S : Subgroup H) ⊓ (modelCenter S e ⊔ M) :=
    ⟨actualRoot_mem_sylow S e, h⟩
  rw [inf_normal_sup_of_le _ _ _ hA, hM] at hi
  exact actualRoot_not_mem_center_sup_Y n hn S e hi

theorem conjugate_square_of_central (t a h : H) (ha : a ∈ Subgroup.center H)
    (hsq : t ^ 2 = a) : (h * t * h⁻¹) ^ 2 = a := by
  change (MulAut.conj h t) ^ 2 = a
  rw [← map_pow, hsq]
  change h * a * h⁻¹ = a
  have hc := Subgroup.mem_center_iff.mp ha h
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def conjugateRoot {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) (h : H) : H :=
  h * actualRoot S e * h⁻¹

theorem conjugateRoot_eq_generators {m : ℕ}
    (S : Sylow 2 H) (e : S ≃* Wreath m) (h : H) :
    conjugateRoot S e h =
      (h * wreathModelHom S e (Original.s m) * h⁻¹) *
      (h * wreathModelHom S e (Original.z m) * h⁻¹) := by
  rw [conjugateRoot, actualRoot_eq]
  group

theorem conjugateRoot_mem_conjugate_sylow {m : ℕ}
    (S : Sylow 2 H) (e : S ≃* Wreath m) (h : H) :
    conjugateRoot S e h ∈ (S : Subgroup H).map (MulAut.conj h).toMonoidHom :=
  Subgroup.mem_map.mpr ⟨actualRoot S e, actualRoot_mem_sylow S e, rfl⟩

theorem conjugateRoot_mem_of_conjugate_sylow_le {m : ℕ}
    (S : Sylow 2 H) (e : S ≃* Wreath m) (h : H) (H₀ : Subgroup H)
    (hS₀ : (S : Subgroup H).map (MulAut.conj h).toMonoidHom ≤ H₀) :
    conjugateRoot S e h ∈ H₀ := hS₀ (conjugateRoot_mem_conjugate_sylow S e h)

theorem conjugateRoot_sq {m : ℕ} (S : Sylow 2 H) (e : S ≃* Wreath m) (h : H)
    (hcentral : modelCenter S e ≤ Subgroup.center H) :
    conjugateRoot S e h ^ 2 = wreathModelHom S e (Original.a m) := by
  have ha : wreathModelHom S e (Original.a m) ∈ modelCenter S e := by
    exact Subgroup.mem_map.mpr ⟨Original.a m, Subgroup.mem_zpowers _, rfl⟩
  exact conjugate_square_of_central _ _ _ (hcentral ha) (actualRoot_sq S e)

theorem conjugateRoot_pow_modulus (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (h : H)
    (hcentral : modelCenter S e ≤ Subgroup.center H) :
    conjugateRoot S e h ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) := by
  calc
    conjugateRoot S e h ^ (2 ^ n) =
        conjugateRoot S e h ^ (2 * (2 ^ n / 2)) :=
      congrArg (fun k : ℕ => conjugateRoot S e h ^ k)
        (wreath_modulus_twice_half n hn).symm
    _ = (conjugateRoot S e h ^ 2) ^ (2 ^ n / 2) := pow_mul _ _ _
    _ = wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2) := by
      rw [conjugateRoot_sq S e h hcentral]
    _ = wreathModelHom S e (Original.x (2 ^ n)) := (map_pow _ _ _).symm

theorem conjugateRoot_orderOf (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (h : H) :
    orderOf (conjugateRoot S e h) = 2 * 2 ^ n := by
  change orderOf (MulAut.conj h (actualRoot S e)) = _
  rw [MulEquiv.orderOf_eq, actualRoot_orderOf n hn S e]

theorem conjugateRoot_not_mem_center_sup_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M : Subgroup H) [M.Normal]
    (hM : (S : Subgroup H) ⊓ M = modelY S e)
    (hcentral : modelCenter S e ≤ Subgroup.center H) (h : H) :
    conjugateRoot S e h ∉ modelCenter S e ⊔ M := by
  let : (modelCenter S e).Normal := Subgroup.normal_of_le_center hcentral
  have hinv : (modelCenter S e ⊔ M).Normal := inferInstance
  intro hx
  have hback := hinv.conj_mem (conjugateRoot S e h) hx h⁻¹
  have heq : h⁻¹ * conjugateRoot S e h * (h⁻¹)⁻¹ = actualRoot S e := by
    rw [conjugateRoot]
    group
  rw [heq] at hback
  exact actualRoot_not_mem_center_sup_normal n hn S e M hM hback

structure ActualConjugateSquareRootData (n : ℕ) (S : Sylow 2 H)
    (e : S ≃* Wreath (2 ^ n)) (M H₀ : Subgroup H) (h : H) : Prop where
  actual_generators : conjugateRoot S e h =
    (h * wreathModelHom S e (Original.s (2 ^ n)) * h⁻¹) *
      (h * wreathModelHom S e (Original.z (2 ^ n)) * h⁻¹)
  actual_sylow_membership : conjugateRoot S e h ∈
    (S : Subgroup H).map (MulAut.conj h).toMonoidHom
  fixed_subgroup_membership : conjugateRoot S e h ∈ H₀
  square : conjugateRoot S e h ^ 2 = wreathModelHom S e (Original.a (2 ^ n))
  modulus_power : conjugateRoot S e h ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n))
  exact_order : orderOf (conjugateRoot S e h) = 2 * 2 ^ n
  outside_normal_product : conjugateRoot S e h ∉ modelCenter S e ⊔ M

theorem actual_conjugate_square_root_data (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M H₀ : Subgroup H) [M.Normal]
    (hM : (S : Subgroup H) ⊓ M = modelY S e)
    (hcentral : modelCenter S e ≤ Subgroup.center H) (h : H)
    (hS₀ : (S : Subgroup H).map (MulAut.conj h).toMonoidHom ≤ H₀) :
    ActualConjugateSquareRootData n S e M H₀ h :=
  ⟨conjugateRoot_eq_generators S e h, conjugateRoot_mem_conjugate_sylow S e h,
    conjugateRoot_mem_of_conjugate_sylow_le S e h H₀ hS₀,
    conjugateRoot_sq S e h hcentral, conjugateRoot_pow_modulus n (by omega) S e h hcentral,
    conjugateRoot_orderOf n hn S e h,
    conjugateRoot_not_mem_center_sup_normal n hn S e M hM hcentral h⟩

end CFSG.Wreathed.WreathCentralSquare
