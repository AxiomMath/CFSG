module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

namespace CFSG.OddStandard.SmallF3.Omega

open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fg_pi_comm (t : OGroup Q) : piOrth Q * t = t * piOrth Q :=
  (Subgroup.mem_center_iff.mp piOrth_mem_center t).symm

private theorem fg_toProj_eq_or {a b : OGroup Q} (h : toProj Q a = toProj Q b) :
    a = b ∨ a = piOrth Q * b := by
  have hmem : a / b ∈ piGroup Q := by
    refine (QuotientGroup.eq_iff_div_mem (N := piGroup Q)).mp ?_
    change toProj Q a = toProj Q b
    exact h
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · left
    rw [div_eq_mul_inv] at h1
    exact mul_inv_eq_one.mp h1
  · right
    rw [div_eq_mul_inv] at h1
    rw [← h1]
    group

private theorem fg_comm_central_left {G : Type*} [Group G] {z : G}
    (hz : ∀ g : G, z * g = g * z) (x y : G) : ⁅z * x, y⁆ = ⁅x, y⁆ := by
  have h := hz (x * y * x⁻¹)
  calc ⁅z * x, y⁆ = (z * (x * y * x⁻¹)) * z⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ((x * y * x⁻¹) * z) * z⁻¹ * y⁻¹ := by rw [h]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

private theorem fg_comm_central_right {G : Type*} [Group G] {z : G}
    (hz : ∀ g : G, z * g = g * z) (x y : G) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  have h := hz (x * y * x⁻¹ * y⁻¹)
  calc ⁅x, z * y⁆ = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (z * x) * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hz x]
    _ = (z * (x * y * x⁻¹ * y⁻¹)) * z⁻¹ := by group
    _ = ((x * y * x⁻¹ * y⁻¹) * z) * z⁻¹ := by rw [h]
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem fg_projSimActO_eq_of_perfect (P : Subgroup (OGroup Q)) (hperf : Group.IsPerfect ↥P)
    (x : ProjSim Q) (hx : ∀ j ∈ P, toProj Q (projSimActO Q x j) = toProj Q j) :
    ∀ j ∈ P, projSimActO Q x j = j := by
  let φ : ↥P →* OGroup Q := (projSimActO Q x).toMonoidHom.comp P.subtype
  let K : Subgroup ↥P := MonoidHom.eqLocus φ P.subtype
  have hz : ∀ t : OGroup Q, piOrth Q * t = t * piOrth Q :=
    fg_pi_comm
  have hcomm : ⁅(⊤ : Subgroup ↥P), ⊤⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    show φ ⁅a, b⁆ = P.subtype ⁅a, b⁆
    rw [map_commutatorElement φ a b, map_commutatorElement P.subtype a b]
    show ⁅projSimActO Q x (a : OGroup Q), projSimActO Q x (b : OGroup Q)⁆ =
      ⁅(a : OGroup Q), (b : OGroup Q)⁆
    have ha := fg_toProj_eq_or (hx a a.2)
    have hb := fg_toProj_eq_or (hx b b.2)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · rw [fg_comm_central_right hz]
    · rw [fg_comm_central_left hz]
    · rw [fg_comm_central_left hz, fg_comm_central_right hz]
  have hK : K = ⊤ := by
    have h1 : ⁅(⊤ : Subgroup ↥P), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    rw [h1] at hcomm
    exact top_le_iff.mp hcomm
  intro j hj
  have hmem : (⟨j, hj⟩ : ↥P) ∈ K := by rw [hK]; exact Subgroup.mem_top _
  exact hmem

theorem fg_projSimActO_eq_of_pow_three (hpos : 0 < Module.finrank (ZMod 3) V) (x : ProjSim Q)
    {j : OGroup Q} (hj : j ^ 3 = 1) (hx : toProj Q (projSimActO Q x j) = toProj Q j) :
    projSimActO Q x j = j := by
  rcases fg_toProj_eq_or hx with h | h
  · exact h
  · exfalso
    have h3 : (projSimActO Q x j) ^ 3 = 1 := by rw [← map_pow, hj, map_one]
    rw [h] at h3
    have hc : Commute (piOrth Q) j := fg_pi_comm j
    rw [hc.mul_pow, hj, mul_one] at h3
    have hpi3 : piOrth Q ^ 3 = piOrth Q := by
      rw [pow_succ, pow_two, piOrth_mul_self, one_mul]
    rw [hpi3] at h3
    exact piOrth_ne_one (Q := Q) hpos h3

theorem fg_apply_comm_of_simAct (γ : simGroup Q) {t : OGroup Q} (h : simAct Q γ t = t) (v : V) :
    (γ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v) =
      (t : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) := by
  have h1 := congrArg (fun s : OGroup Q => (s : V ≃ₗ[ZMod 3] V)) h
  simp only [coe_simAct] at h1
  exact congrArg (fun s : V ≃ₗ[ZMod 3] V => s v) (mul_inv_eq_iff_eq_mul.mp h1)

end CFSG.OddStandard.SmallF3.Omega
