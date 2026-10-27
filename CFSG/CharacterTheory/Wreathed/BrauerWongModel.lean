module

public import CFSG.CharacterTheory.Wreathed.SimpleFusion

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

theorem swap_isConj_iff (m : ℕ) (a b c d : ZMod m) :
    IsConj (element m a b 1) (element m c d 1) ↔ a + b = c + d := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨⟨u, v, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    change element m u v f * element m a b 1 * (element m u v f)⁻¹ = element m c d 1 at hg
    rcases swap_exponent_cases f with rfl | rfl
    · rw [conjugate_swap_by_base, element_eq_iff] at hg
      obtain ⟨h1, h2, -⟩ := hg
      rw [← h1, ← h2]
      abel
    · rw [conjugate_swap_by_swap, element_eq_iff] at hg
      obtain ⟨h1, h2, -⟩ := hg
      rw [← h1, ← h2]
      abel
  · intro h
    refine ⟨element m (c - a) 0 0, ?_⟩
    rw [conjugate_swap_by_base, element_eq_iff]
    refine ⟨by abel, ?_, rfl⟩
    linear_combination h

theorem element_swap_sq_mem_Z (n : ℕ) (hn : 1 ≤ n) (a b : ZMod (2 ^ n)) :
    element (2 ^ n) a b 1 ^ 2 ∈ Original.Z (2 ^ n) := by
  rw [element_swap_sq, Original.Z_eq _ (Nat.one_lt_two_pow (by omega)),
    element_mem_center_iff _ (Nat.one_lt_two_pow (by omega))]
  exact ⟨rfl, rfl⟩

theorem half_add_half (n : ℕ) (hn : 1 ≤ n) :
    ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) + ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) = 0 := by
  rw [← Nat.cast_add, ← two_mul, Nat.mul_div_cancel' (dvd_pow_self 2 (by omega)),
    ZMod.natCast_self]

theorem neg_half (n : ℕ) (hn : 1 ≤ n) :
    -((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) = ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) := by
  linear_combination -(half_add_half n hn)

theorem half_ne_zero (n : ℕ) (hn : 1 ≤ n) : ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.mul_div_cancel _ two_pos, ← pow_succ]
  exact half_residue_ne_zero k

theorem two_smul_eq_zero_iff_half (n : ℕ) (hn : 1 ≤ n) (c : ZMod (2 ^ n)) :
    c + c = 0 ↔ c = 0 ∨ c = ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ, Nat.mul_div_cancel _ two_pos],
    ← two_smul_eq_zero_iff k c, two_nsmul]

theorem element_base_sq_eq_one_iff (n : ℕ) (hn : 1 ≤ n) (a b : ZMod (2 ^ n)) :
    element (2 ^ n) a b 0 ^ 2 = 1 ↔
      (a = 0 ∨ a = ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) ∧
        (b = 0 ∨ b = ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) := by
  rw [element_base_pow, element_base_eq_one_iff, two_nsmul, two_nsmul,
    two_smul_eq_zero_iff_half n hn, two_smul_eq_zero_iff_half n hn]

theorem x_eq_element (n : ℕ) :
    Original.x (2 ^ n) = element (2 ^ n) ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))
      ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) 0 := Original.x_eq _

theorem x2_eq_element (n : ℕ) :
    Original.x2 (2 ^ n) = element (2 ^ n) ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) 0 0 :=
  Original.x2_eq _

theorem t_half_eq_element (n : ℕ) :
    Original.t (2 ^ n) ^ (2 ^ n / 2) =
      element (2 ^ n) 0 ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) 0 := by
  simp [Original.t, element_base_pow, nsmul_eq_mul]

theorem mem_closure_x_x2_iff (n : ℕ) (hn : 1 ≤ n) (w : Wreath (2 ^ n)) :
    w ∈ Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)} ↔
      w ∈ baseSubgroup (2 ^ n) ∧ w ^ 2 = 1 := by
  let O : Subgroup (Wreath (2 ^ n)) := (baseOmega (2 ^ n)).map (baseSubgroup (2 ^ n)).subtype
  have hO (w : Wreath (2 ^ n)) : w ∈ O ↔ w ∈ baseSubgroup (2 ^ n) ∧ w ^ 2 = 1 := by
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, by simpa using congrArg Subtype.val ((mem_baseOmega _ b).mp hb)⟩
    · rintro ⟨hw, hsq⟩
      refine ⟨⟨w, hw⟩, (mem_baseOmega _ _).mpr (Subtype.ext (by simpa using hsq)), rfl⟩
  rw [← hO]
  constructor
  · intro hw
    have hle : Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)} ≤ O := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · rw [SetLike.mem_coe, hO, x_eq_element, element_mem_base, element_base_sq_eq_one_iff n hn]
        exact ⟨rfl, Or.inr rfl, Or.inr rfl⟩
      · rw [SetLike.mem_coe, hO, x2_eq_element, element_mem_base,
          element_base_sq_eq_one_iff n hn]
        exact ⟨rfl, Or.inr rfl, Or.inl rfl⟩
    exact hle hw
  · intro hw
    rw [hO] at hw
    obtain ⟨hwU, hsq⟩ := hw
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
    change element _ a b e ∈ baseSubgroup _ at hwU
    change element _ a b e ∈ _
    rw [element_mem_base] at hwU
    subst hwU
    change element _ a b 0 ^ 2 = 1 at hsq
    rw [element_base_sq_eq_one_iff n hn] at hsq
    have hx : Original.x (2 ^ n) ∈
        Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)} :=
      Subgroup.subset_closure (by simp)
    have hx2 : Original.x2 (2 ^ n) ∈
        Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)} :=
      Subgroup.subset_closure (by simp)
    have ht2 : element (2 ^ n) 0 ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) 0 ∈
        Subgroup.closure {Original.x (2 ^ n), Original.x2 (2 ^ n)} := by
      have hprod : Original.x2 (2 ^ n) * Original.x (2 ^ n) =
          element (2 ^ n) 0 ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) 0 := by
        rw [x2_eq_element, x_eq_element, element_base_mul, half_add_half n hn, zero_add]
      rw [← hprod]
      exact Subgroup.mul_mem _ hx2 hx
    obtain ⟨ha | ha, hb | hb⟩ := hsq <;> subst ha <;> subst hb
    · rw [element_zero]
      exact Subgroup.one_mem _
    · exact ht2
    · rw [← x2_eq_element]
      exact hx2
    · rw [← x_eq_element]
      exact hx

theorem mem_V_iff (m : ℕ) (hm : 4 ∣ m) (a b : ZMod m) (e : ZMod 2) :
    element m a b e ∈ Original.V m ↔ a - b = 0 ∨ a - b = ((m / 2 : ℕ) : ZMod m) := by
  obtain ⟨l, rfl⟩ := hm
  rw [Original.V_atQuarter, element_mem_v, show 4 * l / 2 = 2 * l by omega]

theorem four_dvd_two_pow (n : ℕ) (hn : 2 ≤ n) : 4 ∣ 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact ⟨2 ^ k, by ring⟩

theorem mem_Z_iff (m : ℕ) (hm : 1 < m) (a b : ZMod m) (e : ZMod 2) :
    element m a b e ∈ Original.Z m ↔ e = 0 ∧ a = b := by
  rw [Original.Z_eq m hm, element_mem_center_iff m hm]

theorem V_sq_mem_Z (n : ℕ) (hn : 2 ≤ n) (v : Wreath (2 ^ n)) (hv : v ∈ Original.V (2 ^ n)) :
    v ^ 2 ∈ Original.Z (2 ^ n) := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective v
  change element _ a b e ∈ _ at hv
  change element _ a b e ^ 2 ∈ _
  rcases swap_exponent_cases e with rfl | rfl
  · rw [mem_V_iff _ (four_dvd_two_pow n hn)] at hv
    rw [element_base_pow, mem_Z_iff _ hm, two_nsmul, two_nsmul]
    refine ⟨rfl, ?_⟩
    rcases hv with h | h
    · rw [sub_eq_zero.mp h]
    · have hab : a = b + ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) := by rw [← h]; abel
      rw [hab]
      linear_combination half_add_half n (by omega)
  · exact element_swap_sq_mem_Z n (by omega) a b

theorem V_inf_base (n : ℕ) (hn : 2 ≤ n) (v : Wreath (2 ^ n)) (hv : v ∈ Original.V (2 ^ n))
    (hvU : v ∈ baseSubgroup (2 ^ n)) :
    v ∈ Original.Z (2 ^ n) ∨ (Original.x2 (2 ^ n))⁻¹ * v ∈ Original.Z (2 ^ n) := by
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective v
  change element _ a b e ∈ _ at hv hvU
  change element _ a b e ∈ _ ∨ _ * element _ a b e ∈ _
  rw [element_mem_base] at hvU
  subst hvU
  rw [mem_V_iff _ (four_dvd_two_pow n hn)] at hv
  rcases hv with h | h
  · left
    exact (mem_Z_iff _ hm _ _ _).mpr ⟨rfl, sub_eq_zero.mp h⟩
  · right
    rw [x2_eq_element, element_base_inv, element_base_mul, mem_Z_iff _ hm]
    refine ⟨rfl, ?_⟩
    rw [← h]
    abel

theorem V_orderOf_ne (n : ℕ) (hn : 2 ≤ n) (v : Wreath (2 ^ n)) (hv : v ∈ Original.V (2 ^ n)) :
    orderOf v ≠ 2 * 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective v
  change element _ a b e ∈ _ at hv
  change orderOf (element _ a b e) ≠ _
  intro hord
  obtain ⟨-, hodd⟩ := (element_maximal_order_iff k a b e).mp hord
  rw [mem_V_iff _ (four_dvd_two_pow (k + 1) hn)] at hv
  have heven : Even (a + b).val := by
    rw [← half_modulus_smul_eq_zero_iff]
    have hab : a + b = (a - b) + (b + b) := by abel
    have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ, Nat.mul_div_cancel _ two_pos]
    rw [hhalf] at hv
    have hbb : (2 ^ k) • (b + b) = 0 := by
      rw [← two_nsmul, smul_smul, show 2 ^ k * 2 = 2 ^ (k + 1) by ring, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, show ((2 : ZMod (2 ^ (k + 1))) ^ (k + 1)) =
          ((2 ^ (k + 1) : ℕ) : ZMod _) by push_cast; ring, ZMod.natCast_self, zero_mul]
    rw [hab, smul_add, hbb, add_zero]
    rcases hv with h | h
    · rw [h, smul_zero]
    · rw [h, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow 2 (by omega)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem swap_conj_base (m : ℕ) (a b : ZMod m) :
    (Original.z m)⁻¹ * element m a b 0 * Original.z m = element m b a 0 := by
  have hzinv : (Original.z m)⁻¹ = element m 0 0 1 := by
    rw [Original.z, element_swap_inv, neg_zero]
  rw [hzinv, Original.z, conjugate_base_by_swap' m a b]
  where
    conjugate_base_by_swap' (m : ℕ) (a b : ZMod m) :
        element m 0 0 1 * element m a b 0 * element m 0 0 1 = element m b a 0 := by
      have h := conjugate_base_by_swap m a b 0 0
      rwa [element_swap_inv, neg_zero] at h

section Ambient

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem wreathModelHom_mem (w : Wreath (2 ^ n)) : wreathModelHom S e w ∈ (S : Subgroup G) :=
  (e.symm w).property

theorem exists_wreathModelHom_eq {x : G} (hx : x ∈ (S : Subgroup G)) :
    ∃ w : Wreath (2 ^ n), wreathModelHom S e w = x := by
  rw [← wreathModelHom_range S e] at hx
  exact hx

theorem mem_modelBase_iff (w : Wreath (2 ^ n)) :
    wreathModelHom S e w ∈ modelBase S e ↔ w ∈ baseSubgroup (2 ^ n) := by
  constructor
  · rintro ⟨w', hw', heq⟩
    rwa [← wreathModelHom_injective S e heq]
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem mem_modelCenter_iff (w : Wreath (2 ^ n)) :
    wreathModelHom S e w ∈ modelCenter S e ↔ w ∈ Original.Z (2 ^ n) := by
  constructor
  · rintro ⟨w', hw', heq⟩
    rwa [← wreathModelHom_injective S e heq]
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem mem_modelV_iff (w : Wreath (2 ^ n)) :
    wreathModelHom S e w ∈ modelV S e ↔ w ∈ Original.V (2 ^ n) := by
  constructor
  · rintro ⟨w', hw', heq⟩
    rwa [← wreathModelHom_injective S e heq]
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem modelCenter_eq_zpowers :
    modelCenter S e = Subgroup.zpowers (wreathModelHom S e (Original.a (2 ^ n))) := by
  rw [modelCenter, Original.Z, MonoidHom.map_zpowers]

theorem modelCenter_le_modelBase (hn : 1 ≤ n) : modelCenter S e ≤ modelBase S e := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_modelBase_iff]
  have hm : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  change element _ a b f ∈ Original.Z (2 ^ n) at hw
  change element _ a b f ∈ baseSubgroup (2 ^ n)
  rw [mem_Z_iff _ hm] at hw
  rw [element_mem_base]
  exact hw.1

theorem modelCenter_le_modelV (hn : 2 ≤ n) : modelCenter S e ≤ modelV S e := by
  apply Subgroup.map_mono
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).central_product]
  exact le_sup_left

theorem modelCenter_le_sylow : modelCenter S e ≤ (S : Subgroup G) := by
  rintro _ ⟨w, -, rfl⟩
  exact wreathModelHom_mem S e w

theorem modelCenter_conj (hn : 2 ≤ n) {c s : G} (hc : c ∈ modelCenter S e)
    (hs : s ∈ (S : Subgroup G)) : s⁻¹ * c * s = c := by
  obtain ⟨v, hv, rfl⟩ := hc
  exact model_center_sylow_conjugation n hn S e v hv s hs

theorem modelBase_conj_mem {x s : G} (hx : x ∈ modelBase S e) (hs : s ∈ (S : Subgroup G)) :
    s⁻¹ * x * s ∈ modelBase S e :=
  (Subgroup.mem_normalizer_iff''.mp (sylow_le_modelBase_normalizer S e hs) x).mp hx

theorem modelBase_conj_mem_iff {x s : G} (hs : s ∈ (S : Subgroup G)) :
    s⁻¹ * x * s ∈ modelBase S e ↔ x ∈ modelBase S e :=
  (Subgroup.mem_normalizer_iff''.mp (sylow_le_modelBase_normalizer S e hs) x).symm

theorem modelBase_involution_cases (hn : 1 ≤ n) {x : G} (hx : x ∈ modelBase S e)
    (h2 : orderOf x = 2) :
    x = wreathModelHom S e (Original.x (2 ^ n)) ∨
      x = wreathModelHom S e (Original.x2 (2 ^ n)) ∨
      x = wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [orderOf_injective _ (wreathModelHom_injective S e)] at h2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective w
  change element _ a b f ∈ baseSubgroup _ at hw
  change orderOf (element _ a b f) = 2 at h2
  change wreathModelHom S e (element _ a b f) = _ ∨ wreathModelHom S e (element _ a b f) = _ ∨
    wreathModelHom S e (element _ a b f) = _
  rw [element_mem_base] at hw
  subst hw
  have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ, Nat.mul_div_cancel _ two_pos]
  rw [x_eq_element, x2_eq_element, t_half_eq_element, hhalf]
  rcases (element_base_involution_iff k a b).mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Ambient

end CFSG.Wreathed.BrauerWong
