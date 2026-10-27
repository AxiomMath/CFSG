module

public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.BrauerWongOmega

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem mem_squareSubgroup_of_pow_half (hn : 1 ≤ n) (c : modelBase S e)
    (hc : c ^ 2 ^ (n - 1) = 1) : c ∈ squareSubgroup (modelBase S e) := by
  obtain ⟨w, hw, hwc⟩ := c.property
  obtain ⟨⟨i, j, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  change element _ i j f ∈ baseSubgroup _ at hw
  rw [element_mem_base] at hw
  subst hw
  have hval : wreathModelHom S e (element (2 ^ n) i j 0) ^ 2 ^ (n - 1) = 1 := by
    have h := congrArg Subtype.val hc
    rw [Subgroup.coe_pow, ← hwc] at h
    exact h
  rw [← map_pow, element_base_pow] at hval
  have h0 := (element_base_eq_one_iff _ _ _).mp
    (wreathModelHom_injective S e (hval.trans (map_one _).symm))
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega] at h0
  obtain ⟨p, hp⟩ := (half_modulus_smul_eq_zero_iff k i).mp h0.1
  obtain ⟨q, hq⟩ := (half_modulus_smul_eq_zero_iff k j).mp h0.2
  let d : modelBase S e := ⟨wreathModelHom S e (element _ (p : ZMod _) (q : ZMod _) 0),
    (mem_modelBase_iff S e _).mpr (by rw [element_mem_base])⟩
  apply Subgroup.subset_closure
  refine ⟨d, Subtype.ext ?_⟩
  change wreathModelHom S e (element _ (p : ZMod _) (q : ZMod _) 0) ^ 2 = c.val
  rw [← hwc, ← map_pow, element_base_pow]
  congr 1
  change element _ _ _ 0 = element _ i j 0
  rw [element_eq_iff]
  refine ⟨?_, ?_, rfl⟩
  · rw [← ZMod.natCast_zmod_val i, hp, two_nsmul]
    push_cast
    ring
  · rw [← ZMod.natCast_zmod_val j, hq, two_nsmul]
    push_cast
    ring

variable [Finite G]

theorem mem_centralizer_of_fixes_involutions (hn : 2 ≤ n) {k : G}
    (hk : k ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hJ : k * wreathModelHom S e (Original.x (2 ^ n)) * k⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)))
    (hJ₁ : k * wreathModelHom S e (Original.x2 (2 ^ n)) * k⁻¹ =
      wreathModelHom S e (Original.x2 (2 ^ n))) :
    k ∈ Subgroup.centralizer (modelBase S e : Set G) := by
  have hn1 : 1 ≤ n := by omega
  have hOmega : modelOmega S e ≤ Subgroup.centralizer {k} := by
    rw [modelOmega, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hJ).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hJ₁).symm
  have hfix : ∀ y ∈ modelBase S e, y ^ 2 = 1 → k * y * k⁻¹ = y := by
    intro y hy hy2
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (hOmega ((mem_modelOmega_iff S e hn1 y).mpr ⟨hy, hy2⟩))
    rw [← h]
    group
  have hexp : ∀ y ∈ modelBase S e, y ^ 2 ^ n = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨⟨i, j, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
    change element _ i j f ∈ baseSubgroup _ at hw
    rw [element_mem_base] at hw
    subst hw
    rw [← map_pow]
    change wreathModelHom S e (element _ i j 0 ^ 2 ^ n) = 1
    rw [element_base_pow_modulus, map_one]
  have hact : modelBaseSquareAction n S e ⟨k, hk⟩ = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      change (QuotientGroup.mk' (squareSubgroup (modelBase S e)))
          ((modelBase S e).normalizerMonoidHom ⟨k, hk⟩ b) =
        (QuotientGroup.mk' (squareSubgroup (modelBase S e))) b
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      apply mem_squareSubgroup_of_pow_half S e hn1
      apply Subtype.ext
      set x := (modelBase S e).normalizerMonoidHom ⟨k, hk⟩ b
      have hx : (x : G) = k * b * k⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
      have hcomm : Commute x⁻¹ b := by
        apply Subtype.ext
        exact modelBase_commute S e _ _ (x⁻¹).property b.property
      rw [hcomm.mul_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_inv,
        hx, inv_pow, conj_pow, Subgroup.coe_one]
      have hsq : ((b : G) ^ 2 ^ (n - 1)) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega]
        exact hexp _ b.property
      rw [hfix _ ((modelBase S e).pow_mem b.property _) hsq, inv_mul_cancel]
  have hker : (⟨k, hk⟩ : Subgroup.normalizer (modelBase S e : Set G)) ∈
      (modelBaseSquareAction n S e).ker := hact
  rw [modelBaseSquareAction_ker n hn1 S e] at hker
  exact hker

section Involutions

variable {S e}

omit [Finite G] in
theorem base_inv_mul_table (hn : 2 ≤ n) :
    let J := wreathModelHom S e (Original.x (2 ^ n))
    let J₁ := wreathModelHom S e (Original.x2 (2 ^ n))
    let J₂ := wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))
    J * J₁ = J₂ ∧ J₁ * J = J₂ ∧ J₁ * J₂ = J ∧ J₂ * J₁ = J ∧ J * J₂ = J₁ ∧ J₂ * J = J₁ := by
  intro J J₁ J₂
  have h1 : J * J₁ = J₂ := modelHom_x_mul_x2 S e (by omega)
  have h2 : J₁ * J₂ = J := modelHom_x2_mul_t_half S e
  have hc : ∀ x y : G, x ∈ modelBase S e → y ∈ modelBase S e → x * y = y * x :=
    modelBase_commute S e
  have hJ2 : J₂ ∈ modelBase S e := by
    rw [← h1]
    exact (modelBase S e).mul_mem (modelHom_x_mem_modelBase S e) (modelHom_x2_mem_modelBase S e)
  have hJ : J ∈ modelBase S e := modelHom_x_mem_modelBase S e
  have hJ1 : J₁ ∈ modelBase S e := modelHom_x2_mem_modelBase S e
  have hsq : J * J = 1 := by
    have hstr := wreath_center_involution_and_quaternion_coordinates n hn
    have h := pow_orderOf_eq_one (Original.x (2 ^ n))
    rw [hstr.involution_orders.1, pow_two] at h
    change wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x (2 ^ n)) = 1
    rw [← map_mul, h, map_one]
  have h3 : J * J₂ = J₁ := by rw [← h1, ← mul_assoc, hsq, one_mul]
  exact ⟨h1, by rw [hc _ _ hJ1 hJ, h1], h2, by rw [hc _ _ hJ2 hJ1, h2], h3,
    by rw [hc _ _ hJ2 hJ, h3]⟩

end Involutions

theorem eq_one_of_conj_fixed (hn : 2 ≤ n) {k : G}
    (hk : k ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hk3 : k ^ 3 ∈ Subgroup.centralizer (modelBase S e : Set G))
    (hk1 : k ∉ Subgroup.centralizer (modelBase S e : Set G)) {x : G}
    (hx : x ∈ modelBase S e) (hfix : k * x * k⁻¹ = x) : x = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h1', h2, h2', h3, h3'⟩ := base_inv_mul_table (S := S) (e := e) hn
  set J := wreathModelHom S e (Original.x (2 ^ n))
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n))
  set J₂ := wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))
  have hcube : ∀ y ∈ modelBase S e, k ^ 3 * y * (k ^ 3)⁻¹ = y := by
    intro y hy
    have h := Subgroup.mem_centralizer_iff.mp hk3 y hy
    rw [← h]
    group
  have hconj_mul : ∀ y y' : G, k * (y * y') * k⁻¹ = (k * y * k⁻¹) * (k * y' * k⁻¹) := by
    intro y y'
    group
  have hcube' : ∀ y : G, k ^ 3 * y * (k ^ 3)⁻¹ = k * (k * (k * y * k⁻¹) * k⁻¹) * k⁻¹ := by
    intro y
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hinj : ∀ y y' : G, k * y * k⁻¹ = k * y' * k⁻¹ → y = y' := by
    intro y y' h
    simpa using h
  have hcases : ∀ y : G, y = J ∨ y = J₁ ∨ y = J₂ →
      k * y * k⁻¹ = J ∨ k * y * k⁻¹ = J₁ ∨ k * y * k⁻¹ = J₂ := by
    intro y hy
    have hyB : y ∈ modelBase S e := by
      rcases hy with rfl | rfl | rfl
      · exact modelHom_x_mem_modelBase S e
      · exact modelHom_x2_mem_modelBase S e
      · rw [← h1]
        exact (modelBase S e).mul_mem (modelHom_x_mem_modelBase S e)
          (modelHom_x2_mem_modelBase S e)
    have hy2 : orderOf y = 2 := by
      have hstr := wreath_center_involution_and_quaternion_coordinates n hn
      rcases hy with rfl | rfl | rfl
      · rw [orderOf_injective _ (wreathModelHom_injective S e)]
        exact hstr.involution_orders.1
      · rw [orderOf_injective _ (wreathModelHom_injective S e)]
        exact hstr.involution_orders.2.1
      · rw [orderOf_injective _ (wreathModelHom_injective S e)]
        have h := hstr.x2_class (Original.t (2 ^ n) ^ (2 ^ n / 2))
        obtain ⟨c, hc⟩ := isConj_iff.mp (h.mpr (Or.inr rfl))
        rw [← hc, show c * Original.x2 (2 ^ n) * c⁻¹ = (MulAut.conj c) (Original.x2 (2 ^ n)) by
          simp, MulEquiv.orderOf_eq]
        exact hstr.involution_orders.2.1
    have hkyB : k * y * k⁻¹ ∈ modelBase S e := (Subgroup.mem_normalizer_iff.mp hk y).mp hyB
    have hky2 : orderOf (k * y * k⁻¹) = 2 := by
      rw [show k * y * k⁻¹ = (MulAut.conj k) y by simp, MulEquiv.orderOf_eq, hy2]
    exact modelBase_involution_cases S e (by omega) hkyB hky2
  have hJne1 : J ≠ J₁ := modelHom_x_ne_x2 S e (by omega)
  have hJne2 : J ≠ J₂ := modelHom_x_ne_t_half S e (by omega)
  have hJ1ne2 : J₁ ≠ J₂ := modelHom_x2_ne_t_half S e (by omega)
  have hJB : J ∈ modelBase S e := modelHom_x_mem_modelBase S e
  have hJ1B : J₁ ∈ modelBase S e := modelHom_x2_mem_modelBase S e
  have hJ2B : J₂ ∈ modelBase S e := by
    rw [← h1]
    exact (modelBase S e).mul_mem hJB hJ1B
  by_contra hx1
  obtain ⟨r, hr⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨x, modelBase_le_sylow S e hx⟩
  rw [Subgroup.orderOf_mk] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hr
    exact hx1 hr
  have hord0 : orderOf x ≠ 0 := by rw [hr]; positivity
  have h2dvd : 2 ∣ orderOf x := by rw [hr]; exact dvd_pow_self 2 hr0
  set x' := x ^ (orderOf x / 2)
  have hx'2 : orderOf x' = 2 := orderOf_pow_orderOf_div hord0 h2dvd
  have hx'B : x' ∈ modelBase S e := (modelBase S e).pow_mem hx _
  have hx'fix : k * x' * k⁻¹ = x' := by
    change k * x ^ (orderOf x / 2) * k⁻¹ = x ^ (orderOf x / 2)
    rw [← conj_pow, hfix]
  apply hk1
  rcases modelBase_involution_cases S e (by omega) hx'B hx'2 with hx' | hx' | hx' <;>
    rw [hx'] at hx'fix
  ·
    rcases hcases J₁ (Or.inr (Or.inl rfl)) with hy | hy | hy
    · exact absurd (hinj _ _ (hy.trans hx'fix.symm)) hJne1.symm
    · exact mem_centralizer_of_fixes_involutions S e hn hk hx'fix hy
    · exfalso
      have hJ2 : k * J₂ * k⁻¹ = J₁ := by rw [← h1, hconj_mul, hx'fix, hy, h3]
      have := hcube J₁ hJ1B
      rw [hcube', hy, hJ2, hy] at this
      exact hJ1ne2 this.symm
  ·
    rcases hcases J (Or.inl rfl) with hy | hy | hy
    · exact mem_centralizer_of_fixes_involutions S e hn hk hy hx'fix
    · exact absurd (hinj _ _ (hy.trans hx'fix.symm)) hJne1
    · exfalso
      have hJ2 : k * J₂ * k⁻¹ = J := by rw [← h1, hconj_mul, hy, hx'fix, h2']
      have := hcube J hJB
      rw [hcube', hy, hJ2, hy] at this
      exact hJne2 this.symm
  ·
    rcases hcases J (Or.inl rfl) with hy | hy | hy
    · have hJ1 : k * J₁ * k⁻¹ = J₁ := by rw [← h3, hconj_mul, hy, hx'fix, h3]
      exact mem_centralizer_of_fixes_involutions S e hn hk hy hJ1
    · exfalso
      have hJ1 : k * J₁ * k⁻¹ = J := by rw [← h3, hconj_mul, hy, hx'fix, h2]
      have := hcube J hJB
      rw [hcube', hy, hJ1, hy] at this
      exact hJne1 this.symm
    · exact absurd (hinj _ _ (hy.trans hx'fix.symm)) hJne2

theorem mul_conj_mul_conj_eq_one (hn : 2 ≤ n) {k : G}
    (hk : k ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hk3 : k ^ 3 ∈ Subgroup.centralizer (modelBase S e : Set G))
    (hk1 : k ∉ Subgroup.centralizer (modelBase S e : Set G)) {x : G}
    (hx : x ∈ modelBase S e) :
    x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) = 1 := by
  have hk2 : k ^ 2 ∈ Subgroup.normalizer (modelBase S e : Set G) :=
    (Subgroup.normalizer _).pow_mem hk 2
  have hx1 : k * x * k⁻¹ ∈ modelBase S e := (Subgroup.mem_normalizer_iff.mp hk x).mp hx
  have hx2 : k ^ 2 * x * (k ^ 2)⁻¹ ∈ modelBase S e :=
    (Subgroup.mem_normalizer_iff.mp hk2 x).mp hx
  apply eq_one_of_conj_fixed S e hn hk hk3 hk1
  · exact (modelBase S e).mul_mem ((modelBase S e).mul_mem hx hx1) hx2
  · have hcube : k ^ 3 * x * (k ^ 3)⁻¹ = x := by
      have h := Subgroup.mem_centralizer_iff.mp hk3 x hx
      rw [← h]
      group
    have hc := modelBase_commute S e
    calc
      k * (x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹)) * k⁻¹ =
          (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) * (k ^ 3 * x * (k ^ 3)⁻¹) := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) * x := by rw [hcube]
      _ = x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) := by
        rw [hc _ x ((modelBase S e).mul_mem hx1 hx2) hx, ← mul_assoc]

end CFSG.Wreathed.AdaptedBaseFusion
