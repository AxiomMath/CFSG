module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionGenerators
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseNormalizer

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u

variable {G : Type u} [Group G]

structure IsAdaptedBase (U : Subgroup G) (a w σ υ g : G) : Prop where
  left_mem : σ ∈ U
  right_mem : υ ∈ U
  closure_eq : Subgroup.closure {σ, υ} = U
  mul_eq : σ * υ = a
  conj_swap : w⁻¹ * σ * w = υ
  conj_left : g⁻¹ * σ * g = υ
  conj_right : g⁻¹ * υ * g = a⁻¹
  mem_normalizer : g ∈ Subgroup.normalizer (U : Set G)
  orderOf_conj : orderOf (U.normalizerMonoidHom ⟨g, mem_normalizer⟩) = 3

variable [Finite G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem exists_isAdaptedBase [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hn : 2 ≤ n) :
    ∃ σ υ g : G, IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) σ υ g := by
  obtain ⟨h1, h1', h2, h2', h3, h3'⟩ := base_inv_mul_table (S := S) (e := e) hn
  have hbase := modelBaseNormalizerQuotient_sym3_of_simple hnonab n hn S e
  obtain ⟨Y, hYN, hY1, hY2, hY3⟩ := exists_base_three_cycle hn S e hbase
  obtain ⟨k, rfl⟩ : ∃ k : G, Y = k⁻¹ := ⟨Y⁻¹, (inv_inv Y).symm⟩
  rw [inv_inv] at hY1 hY2 hY3
  set φ := wreathModelHom S e
  set J := φ (Original.x (2 ^ n))
  set J₁ := φ (Original.x2 (2 ^ n))
  set J₂ := φ (Original.t (2 ^ n) ^ (2 ^ n / 2))
  set T := φ (Original.z (2 ^ n))
  set aG := φ (Original.a (2 ^ n))
  set B := modelBase S e
  have hkN : k ∈ Subgroup.normalizer (B : Set G) := by
    have h := (Subgroup.normalizer (B : Set G)).inv_mem hYN
    rwa [inv_inv] at h
  have hJne1 : J ≠ J₁ := modelHom_x_ne_x2 S e (by omega)
  have hJne2 : J ≠ J₂ := modelHom_x_ne_t_half S e (by omega)
  have hJ1ne2 : J₁ ≠ J₂ := modelHom_x2_ne_t_half S e (by omega)
  have hJB : J ∈ B := modelHom_x_mem_modelBase S e
  have haB : aG ∈ B := (mem_modelBase_iff S e _).mpr (by rw [Original.a_eq, element_mem_base])
  have hcube_conj : ∀ y : G, k ^ 3 * y * (k ^ 3)⁻¹ = k * (k * (k * y * k⁻¹) * k⁻¹) * k⁻¹ := by
    intro y
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have hkcube : k ^ 3 ∈ Subgroup.centralizer (B : Set G) := by
    apply mem_centralizer_of_fixes_involutions S e hn ((Subgroup.normalizer _).pow_mem hkN 3)
    · rw [hcube_conj, hY1, hY2, hY3]
    · rw [hcube_conj, hY2, hY3, hY1]
  have hc3 : ∀ y ∈ B, k * (k * (k * y * k⁻¹) * k⁻¹) * k⁻¹ = y := by
    intro y hy
    have h := Subgroup.mem_centralizer_iff.mp hkcube y hy
    rw [← hcube_conj, ← h, mul_inv_cancel_right]
  have hknot : k ∉ Subgroup.centralizer (B : Set G) := by
    intro hk
    have h := Subgroup.mem_centralizer_iff.mp hk J hJB
    apply hJne1
    rw [← hY1, ← h, mul_inv_cancel_right]
  have hTS : T ∈ (S : Subgroup G) := wreathModelHom_mem S e _
  have hTinv : T⁻¹ = T := by
    rw [← map_inv]
    congr 1
    rw [Original.z, element_swap_inv, neg_zero]
  have hTJ : T * J * T⁻¹ = J := by
    have h := modelHom_x_central S e hn ((S : Subgroup G).inv_mem hTS)
    rwa [inv_inv] at h
  have hTJ1 : T * J₁ * T⁻¹ = J₂ := by
    have h := modelHom_swap_conj_x2 S e
    rw [hTinv] at h ⊢
    exact h
  have hTJ2 : T * J₂ * T⁻¹ = J₁ := by
    have h := modelHom_swap_conj_t_half S e
    rw [hTinv] at h ⊢
    exact h
  have hTa : T⁻¹ * aG * T = aG :=
    modelCenter_conj S e hn
      (⟨Original.a (2 ^ n), Subgroup.mem_zpowers _, rfl⟩ : aG ∈ modelCenter S e) hTS
  have hTkN : T * k ∈ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normalizer _).mul_mem (sylow_le_modelBase_normalizer S e hTS) hkN
  have hsq_conj : ∀ y : G, (T * k) ^ 2 * y * ((T * k) ^ 2)⁻¹ =
      T * (k * (T * (k * y * k⁻¹) * T⁻¹) * k⁻¹) * T⁻¹ := by
    intro y
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have hTk2 : (T * k) ^ 2 ∈ Subgroup.centralizer (B : Set G) := by
    apply mem_centralizer_of_fixes_involutions S e hn
      ((Subgroup.normalizer _).pow_mem hTkN 2)
    · rw [hsq_conj, hY1, hTJ1, hY3, hTJ]
    · rw [hsq_conj, hY2, hTJ2, hY2, hTJ2]
  have hkaB : k * aG * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hkN aG).mp haB
  have hk2aB : k * (k * aG * k⁻¹) * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hkN _).mp hkaB
  have hinner : T * (k * aG * k⁻¹) * T⁻¹ = k * (k * aG * k⁻¹) * k⁻¹ := by
    have hc' := Subgroup.mem_centralizer_iff.mp hTk2 aG haB
    rw [pow_two] at hc'
    have hsq : (T * k) * aG * (T * k)⁻¹ = (T * k)⁻¹ * aG * (T * k) := by
      calc
        (T * k) * aG * (T * k)⁻¹ = (T * k)⁻¹ * ((T * k) * (T * k) * aG) * (T * k)⁻¹ := by
          simp only [mul_assoc, mul_inv_rev, inv_mul_cancel_left]
        _ = (T * k)⁻¹ * (aG * ((T * k) * (T * k))) * (T * k)⁻¹ := by rw [hc']
        _ = (T * k)⁻¹ * aG * (T * k) := by
          simp only [mul_assoc, mul_inv_cancel, mul_one]
    calc
      T * (k * aG * k⁻¹) * T⁻¹ = (T * k) * aG * (T * k)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
      _ = (T * k)⁻¹ * aG * (T * k) := hsq
      _ = k⁻¹ * (T⁻¹ * aG * T) * k := by simp only [mul_inv_rev, mul_assoc]
      _ = k⁻¹ * aG * k := by rw [hTa]
      _ = k⁻¹ * (k * (k * (k * aG * k⁻¹) * k⁻¹) * k⁻¹) * k := by rw [hc3 aG haB]
      _ = k * (k * aG * k⁻¹) * k⁻¹ := by
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have hsum := mul_conj_mul_conj_eq_one S e hn hkN hkcube hknot haB
  rw [show k ^ 2 * aG * (k ^ 2)⁻¹ = k * (k * aG * k⁻¹) * k⁻¹ by
    simp only [pow_two, mul_inv_rev, mul_assoc]] at hsum
  have hc := modelBase_commute S e
  refine ⟨(k * aG * k⁻¹)⁻¹, (k * (k * aG * k⁻¹) * k⁻¹)⁻¹, k⁻¹, B.inv_mem hkaB,
    B.inv_mem hk2aB, ?_, ?_, ?_, ?_, ?_, hYN, ?_⟩
  ·
    have hσhalf : ((k * aG * k⁻¹)⁻¹) ^ 2 ^ (n - 1) = J₁ := by
      have haJ : aG ^ 2 ^ (n - 1) = J := by
        rw [← map_pow]
        congr 1
        rw [Original.x, WreathGenerators.half_eq (by omega)]
      rw [inv_pow, conj_pow, haJ, hY1]
      have hJ1sq : J₁ * J₁ = 1 := by
        have hstr := wreath_center_involution_and_quaternion_coordinates n hn
        have h := pow_orderOf_eq_one (Original.x2 (2 ^ n))
        rw [hstr.involution_orders.2.1, pow_two] at h
        change φ (Original.x2 (2 ^ n)) * φ (Original.x2 (2 ^ n)) = 1
        rw [← map_mul, h, map_one]
      exact inv_eq_of_mul_eq_one_right hJ1sq
    have hυhalf : ((k * (k * aG * k⁻¹) * k⁻¹)⁻¹) ^ 2 ^ (n - 1) = J₂ := by
      have h : (k * (k * aG * k⁻¹) * k⁻¹)⁻¹ = T * (k * aG * k⁻¹)⁻¹ * T⁻¹ := by
        rw [← hinner]
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [h, conj_pow, hσhalf, hTJ1]
    apply closure_pair_eq_modelBase_of_pow_half S e hn (B.inv_mem hkaB) (B.inv_mem hk2aB)
    · rw [hσhalf]
      intro h
      have := h1
      rw [h, mul_one] at this
      exact hJne2 this
    · rw [hυhalf]
      intro h
      have := h2
      rw [h, mul_one] at this
      exact hJne1 this.symm
    · rw [hσhalf, hυhalf]
      exact hJ1ne2
  ·
    have hprod : (k * aG * k⁻¹) * (k * (k * aG * k⁻¹) * k⁻¹) = aG⁻¹ := by
      rw [← mul_one aG⁻¹, ← hsum]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_inv_rev, hc _ _ hk2aB hkaB, hprod, inv_inv]
  ·
    rw [← hinner, show T⁻¹ * (k * aG * k⁻¹)⁻¹ * T = (T⁻¹ * (k * aG * k⁻¹) * T)⁻¹ by
      simp only [mul_inv_rev, inv_inv, mul_assoc], hTinv]
  ·
    rw [inv_inv]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  ·
    rw [inv_inv, show k * (k * (k * aG * k⁻¹) * k⁻¹)⁻¹ * k⁻¹ =
      (k * (k * (k * aG * k⁻¹) * k⁻¹) * k⁻¹)⁻¹ by simp only [mul_inv_rev, inv_inv, mul_assoc],
      hc3 aG haB]
  ·
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hY3' : (⟨k⁻¹, hYN⟩ : Subgroup.normalizer (B : Set G)) ^ 3 ∈
          (B.normalizerMonoidHom).ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        change k⁻¹ ^ 3 ∈ Subgroup.centralizer (B : Set G)
        rw [inv_pow]
        exact (Subgroup.centralizer _).inv_mem hkcube
      exact hY3'
    · intro h1Y
      have h := DFunLike.congr_fun h1Y ⟨J, hJB⟩
      have hval := congrArg Subtype.val h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
      change k⁻¹ * J * k⁻¹⁻¹ = J at hval
      rw [inv_inv] at hval
      have hYJ : k⁻¹ * J * k = J₂ := by
        rw [← hY3]
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      exact hJne2 (hval.symm.trans hYJ)

end CFSG.Wreathed.AdaptedBaseFusion
