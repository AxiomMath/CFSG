module

public import CFSG.Quasithin.H13.L32NLem14333c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L14333

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)
include c

theorem sq_mem_V_of_X_F4 : ∀ y ∈ conjClosure (centerOf (fsuU T V)) L, y * y ∈ V := by
  refine sq_mem_of_closure rfl c.X_comm_F4 ?_
  rintro _ ⟨l, hl, w, hw, rfl⟩
  have hw2 : w * w ∈ fsuV1 T V := c.ctx.sq w (Subgroup.mem_inf.mp hw).1
  have e : l * w * l⁻¹ * (l * w * l⁻¹) = l * (w * w) * l⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (c.L_le_normV_F4 hl) _).mp (Subgroup.mem_inf.mp hw2).1

theorem indep_F4 {i j k : ℕ} (hi : i < 2) (hj : j < 2) (hk : k < 2)
    (h : z ^ i * a ^ j * b ^ k = 1) : i = 0 ∧ j = 0 ∧ k = 0 := by
  have hzV₂ : z ∈ V₂ := c.ctx.plane.2 c.z_mem
  have haV₂ := c.ctx.aV₂
  interval_cases i <;> interval_cases j <;> interval_cases k <;> simp at h ⊢
  · exact c.b_nmem (h ▸ one_mem _)
  · exact c.ctx.a1 (h ▸ one_mem _)
  · apply c.b_nmem
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem haV₂
  · exact c.z_ne h
  · apply c.b_nmem
    have : b = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem hzV₂
  · apply c.ctx.a1
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem c.z_mem
  · apply c.b_nmem
    have : b = (z * a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (mul_mem hzV₂ haV₂)

theorem isZ4Cube_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    HSType.IsZ4Cube ↥(pCoreOf 2 L) := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq_F4 hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  rw [hP] at hcard ⊢
  set X := conjClosure (centerOf (fsuU T V)) L
  obtain ⟨s₁, hs₁, hs₁z⟩ := c.exists_sq_F4 hVe z c.z_mem_V_F4
  obtain ⟨s₂, hs₂, hs₂a⟩ := c.exists_sq_F4 hVe a c.a_mem_V_F4
  obtain ⟨s₃, hs₃, hs₃b⟩ := c.exists_sq_F4 hVe b c.b_mem
  have h4 : ∀ (s v : G), s * s = v → v ∈ V → s ^ 4 = 1 := by
    intro s v hsv hv
    calc s ^ 4 = (s * s) * (s * s) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hsv]; exact c.mul_self_V_F4 hv
  have hsq2 : ∀ (s v : G), s * s = v → ∀ n : ℕ, s ^ (2 * n) = v ^ n := by
    intro s v hsv n
    rw [pow_mul, pow_two, hsv]
  have hv2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by rw [pow_two]; exact c.mul_self_V_F4 hv
  refine isZ4Cube_of c.X_comm_F4 hs₁ hs₂ hs₃ (h4 _ _ hs₁z c.z_mem_V_F4) (h4 _ _ hs₂a c.a_mem_V_F4)
    (h4 _ _ hs₃b c.b_mem) (fun i j k hi hj hk h => ?_) hcard

  have hcomm : ∀ (i j : ℕ) (u w : G), u ∈ X → w ∈ X → u ^ i * w ^ j = w ^ j * u ^ i :=
    fun i j u w hu hw => c.X_comm_F4 _ (X.pow_mem hu i) _ (X.pow_mem hw j)
  have hsq : (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k) =
      z ^ i * a ^ j * b ^ k := by
    have e1 : (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k) =
        (s₁ ^ i * s₁ ^ i) * (s₂ ^ j * s₂ ^ j) * (s₃ ^ k * s₃ ^ k) := by
      have c1 := hcomm i j s₁ s₂ hs₁ hs₂
      have c2 := hcomm i k s₁ s₃ hs₁ hs₃
      have c3 := hcomm j k s₂ s₃ hs₂ hs₃
      calc (s₁ ^ i * s₂ ^ j * s₃ ^ k) * (s₁ ^ i * s₂ ^ j * s₃ ^ k)
          = s₁ ^ i * s₂ ^ j * (s₃ ^ k * s₁ ^ i) * s₂ ^ j * s₃ ^ k := by group
        _ = s₁ ^ i * s₂ ^ j * (s₁ ^ i * s₃ ^ k) * s₂ ^ j * s₃ ^ k := by rw [c2]
        _ = s₁ ^ i * (s₂ ^ j * s₁ ^ i) * (s₃ ^ k * s₂ ^ j) * s₃ ^ k := by group
        _ = s₁ ^ i * (s₁ ^ i * s₂ ^ j) * (s₂ ^ j * s₃ ^ k) * s₃ ^ k := by rw [c1, c3]
        _ = (s₁ ^ i * s₁ ^ i) * (s₂ ^ j * s₂ ^ j) * (s₃ ^ k * s₃ ^ k) := by group
    rw [e1, ← pow_add, ← pow_add, ← pow_add, ← two_mul, ← two_mul, ← two_mul, hsq2 _ _ hs₁z,
      hsq2 _ _ hs₂a, hsq2 _ _ hs₃b]
  have h1 : z ^ (i % 2) * a ^ (j % 2) * b ^ (k % 2) = 1 := by
    rw [← pow_eq_pow_mod_two (hv2 z c.z_mem_V_F4), ← pow_eq_pow_mod_two (hv2 a c.a_mem_V_F4),
      ← pow_eq_pow_mod_two (hv2 b c.b_mem), ← hsq, h, one_mul]
  obtain ⟨ei, ej, ek⟩ := c.indep_F4 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h1
  obtain ⟨i', rfl⟩ : ∃ i', i = 2 * i' := ⟨i / 2, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' := ⟨j / 2, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
  rw [hsq2 _ _ hs₁z, hsq2 _ _ hs₂a, hsq2 _ _ hs₃b] at h
  obtain ⟨e1, e2, e3⟩ := c.indep_F4 (by omega) (by omega) (by omega) h
  omega

theorem isXSectionIso₂_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    IsXSectionIso₂ L (pCoreOf 2 L) V V ⊥ := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq_F4 hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  rw [hP] at hcard ⊢
  exact isXSectionIso₂_of_sq c.X_comm_F4 (c.V_le_X_F4 hVe) (fun v hv => c.mul_self_V_F4 hv)
    c.sq_mem_V_of_X_F4 (c.exists_sq_F4 hVe) (by rw [hcard, c.card_V_F4])

end Ctx_F4

end L14333

end CFSG.Quasithin.H13
