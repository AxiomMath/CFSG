module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NU
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NW1
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NK

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S}

theorem wV_inv (I : Inst S) (v : V4) : (I.wV v)⁻¹ = I.wV v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact I.sq_eq_one (I.wV_mem _))

theorem x_mat (I : Inst S) (H : Hyp S R) : I.Mat S.x xCols :=
  ⟨I.R_le H (H.le (x_mem_TE S)), I.x_cols _⟩

variable {H : Hyp S R} (P : I.Pre6 H)

namespace Pre6

theorem d_cube_commute {q : X} (hq : q ∈ P.Q₁) : P.d ^ 3 * q = q * P.d ^ 3 := by
  obtain ⟨a, ha⟩ := P.d_pow
  have hd3C : P.d ^ 3 ∈ centralizer (I.E : Set X) := by
    apply Mat.mem_centralizer
    have := P.d_mat.mul (P.d_mat.mul P.d_mat)
    rwa [show comp dCols (comp dCols dCols) = bas from funext dCols_cube, ← pow_three] at this
  have hK : P.d ^ 3 ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)) := by
    refine I.mem_K_of_odd hd3C ?_
    have hdvd : orderOf (P.d ^ 3) ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, ha, one_pow])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
    rw [hj]
    exact Odd.pow (by decide)
  exact I.commute_of_mem_K P.isPGroup_Q₁ P.Q₁_le_N hK (pow_mem P.d_Q₁ 3) hq

theorem w_struct {ε : Fin 2} {v w w₂ : X} (hvM : I.Mat v vC)
    (hvd : v * P.d = P.d * v) (hwT : w ∈ R) (hwM : I.Mat w (M1C ε)) {α : Fin 2}
    (hvw : v * w * v⁻¹ * w⁻¹ = I.wV (α, 0, 0, ε * α)) (hw₂ : w₂ = P.d * w * P.d⁻¹) :
    ∃ s1 s4 : Fin 2, w ^ 2 = I.wV (s1, 0, 0, s4) ∧
      ∃ γ : V4, w * w₂ * w⁻¹ * w₂⁻¹ = I.wV γ ∧
      ∃ e : V4, P.d * w₂ * P.d⁻¹ = w * w₂ * I.wV e ∧ e.2.2.1 = 0 ∧
        γ = (0, 0, 0, s4) ∧ e.1 = s1 ∧ e.2.1 = s1 ∧ (ε = 1 → s1 = 0) := by
  have hdM := P.d_mat
  have hddM : I.Mat (P.d * P.d) ddCols := hdM.mul hdM
  have hdiM : I.Mat P.d⁻¹ ddCols := hdM.inv dCols_ddCols
  have hw₂M : I.Mat w₂ (M2C ε) := hw₂ ▸ (hdM.mul hwM).mul hdiM
  have hw₃M : I.Mat (P.d * w₂ * P.d⁻¹) (M3C ε) := (hdM.mul hw₂M).mul hdiM
  have hw₁₂M : I.Mat (w * w₂) (M3C ε) := by
    have := hwM.mul hw₂M
    rwa [M1C_M2C] at this
  have hwQ : w ∈ P.Q₁ := P.mem_Q₁_of_Mat (P.T₁_le hwT) hwM (M1C_transl ε)
  have hw₂Q : w₂ ∈ P.Q₁ := hw₂ ▸ P.d_mem_Q₁ hwQ
  have hw₃Q : P.d * w₂ * P.d⁻¹ ∈ P.Q₁ := P.d_mem_Q₁ hw₂Q
  have hsE : w ^ 2 ∈ I.E := P.mem_E_of_mem_Q₁ (pow_mem hwQ 2) (Mat.mem_centralizer (by
    have := hwM.mul hwM
    rwa [show comp (M1C ε) (M1C ε) = bas from funext (M1C_sq ε), ← pow_two] at this))
  obtain ⟨sv, hsv⟩ := I.eq_wV hsE
  have hs1 : lin (M1C ε) sv = sv := by
    have h : w * w ^ 2 * w⁻¹ = w ^ 2 := by simp only [pow_two]; group
    rw [hsv, hwM.conj] at h
    exact I.wV_injective h
  have hsx : lin xCols sv = sv := by
    obtain ⟨a, b, hab⟩ := H.commutator_mem (H.le (x_mem_TE S)) hwT
    obtain ⟨p, q, hpq⟩ := I.zk_eq_wV a b
    rw [hpq] at hab
    have hxw : S.x * w * S.x⁻¹ = I.wV (p, 0, 0, q) * w := by
      calc S.x * w * S.x⁻¹ = (S.x * w * S.x⁻¹ * w⁻¹) * w := by group
        _ = I.wV (p, 0, 0, q) * w := by rw [hab]
    have hcw : w * I.wV (p, 0, 0, q) * w⁻¹ = I.wV (p, 0, 0, q) := by
      rw [hwM.conj, M1C_fix_zk]
    have h : S.x * w ^ 2 * S.x⁻¹ = w ^ 2 := by
      calc S.x * w ^ 2 * S.x⁻¹ = (S.x * w * S.x⁻¹) * (S.x * w * S.x⁻¹) := by
            simp only [pow_two]; group
        _ = I.wV (p, 0, 0, q) * w * (I.wV (p, 0, 0, q) * w) := by rw [hxw]
        _ = I.wV (p, 0, 0, q) * (w * I.wV (p, 0, 0, q) * w⁻¹) * (w * w) := by group
        _ = w ^ 2 := by
            rw [hcw, ← pow_two w, ← pow_two (I.wV _), I.sq_eq_one (I.wV_mem _), one_mul]
    rw [hsv, (I.x_mat H).conj] at h
    exact I.wV_injective h
  obtain ⟨hs2, hs3⟩ := M1C_fix ε sv hs1 hsx
  obtain ⟨s1, s2, s3, s4⟩ := sv
  simp only at hs2 hs3
  subst hs2 hs3
  have hγE : w * w₂ * w⁻¹ * w₂⁻¹ ∈ I.E := by
    refine P.mem_E_of_mem_Q₁ (mul_mem (mul_mem (mul_mem hwQ hw₂Q) (inv_mem hwQ)) (inv_mem hw₂Q))
      (Mat.mem_centralizer ?_)
    have := ((hwM.mul hw₂M).mul (hwM.inv (M1C_sq ε))).mul (hw₂M.inv (M2C_sq ε))
    rwa [show comp (comp (comp (M1C ε) (M2C ε)) (M1C ε)) (M2C ε) = bas from
      funext (comm_M1C_M2C ε)] at this
  obtain ⟨γ, hγ⟩ := I.eq_wV hγE
  have heE : (w * w₂)⁻¹ * (P.d * w₂ * P.d⁻¹) ∈ I.E :=
    P.mem_E_of_mem_Q₁ (mul_mem (inv_mem (mul_mem hwQ hw₂Q)) hw₃Q)
      (hw₁₂M.inv_mul_mem_centralizer hw₃M)
  obtain ⟨ev, hev⟩ := I.eq_wV heE
  have hw₃ : P.d * w₂ * P.d⁻¹ = w * w₂ * I.wV ev := by rw [← hev]; group
  have E2 : addV (s1, 0, 0, s4) (lin (M2C ε) (s1, 0, 0, s4)) =
      addV (lin (M1C ε) γ) γ := by
    have hid : w ^ 2 * w₂ * (w ^ 2)⁻¹ * w₂⁻¹ =
        w * (w * w₂ * w⁻¹ * w₂⁻¹) * w⁻¹ * (w * w₂ * w⁻¹ * w₂⁻¹) := by simp only [pow_two]; group
    have hl : w ^ 2 * w₂ * (w ^ 2)⁻¹ * w₂⁻¹ =
        I.wV (addV (s1, 0, 0, s4) (lin (M2C ε) (s1, 0, 0, s4))) := by
      rw [hsv, I.wV_inv, I.wV_add, ← hw₂M.conj]; group
    rw [hl, hγ, hwM.conj, ← I.wV_add] at hid
    exact I.wV_injective hid
  have E5 : lin ddCols (s1, 0, 0, s4) = addV (addV (addV (addV (lin (M3C ε) ev)
      (lin (M1C ε) γ)) (s1, 0, 0, s4)) (lin dCols (s1, 0, 0, s4))) ev := by
    have hsq3 : (P.d * w₂ * P.d⁻¹) ^ 2 = I.wV (lin ddCols (s1, 0, 0, s4)) := by
      have e1 : P.d * w₂ * P.d⁻¹ = (P.d * P.d) * w * (P.d * P.d)⁻¹ := by rw [hw₂]; group
      rw [e1, conj_pow, hsv, hddM.conj]
    have hs₂ : w₂ ^ 2 = I.wV (lin dCols (s1, 0, 0, s4)) := by rw [hw₂, conj_pow, hsv, hdM.conj]
    have hγi : w₂ * w * w₂⁻¹ * w⁻¹ = I.wV γ := by
      rw [← I.wV_inv, ← hγ]; group
    have hid : (w * w₂ * I.wV ev) ^ 2 = ((w * w₂) * I.wV ev * (w * w₂)⁻¹) *
        (w * (w₂ * w * w₂⁻¹ * w⁻¹) * w⁻¹) * w ^ 2 * w₂ ^ 2 * I.wV ev := by
      simp only [pow_two]; group
    rw [hw₁₂M.conj, ← hw₃, hsq3, hγi, hsv, hs₂, hwM.conj, ← I.wV_add, ← I.wV_add,
      ← I.wV_add, ← I.wV_add] at hid
    exact I.wV_injective hid
  have E7 : lin ddCols (α, 0, 0, ε * α) = addV (α, 0, 0, ε * α)
      (lin (M1C ε) (addV (lin dCols (α, 0, 0, ε * α)) (lin (M2C ε) (addV (lin vC ev) ev)))) := by
    have hvdd : v * (P.d * P.d) = (P.d * P.d) * v := by
      calc v * (P.d * P.d) = (v * P.d) * P.d := by group
        _ = (P.d * v) * P.d := by rw [hvd]
        _ = P.d * (v * P.d) := by group
        _ = P.d * (P.d * v) := by rw [hvd]
        _ = P.d * P.d * v := by group
    have hv3 : v * (P.d * w₂ * P.d⁻¹) * v⁻¹ * (P.d * w₂ * P.d⁻¹)⁻¹ =
        I.wV (lin ddCols (α, 0, 0, ε * α)) := by
      have e1 : P.d * w₂ * P.d⁻¹ = (P.d * P.d) * w * (P.d * P.d)⁻¹ := by rw [hw₂]; group
      rw [e1, comm_conj_of_commute hvdd, hvw, hddM.conj]
    have hv2 : v * w₂ * v⁻¹ * w₂⁻¹ = I.wV (lin dCols (α, 0, 0, ε * α)) := by
      rw [hw₂, comm_conj_of_commute hvd, hvw, hdM.conj]
    have hve : v * I.wV ev * v⁻¹ * (I.wV ev)⁻¹ = I.wV (addV (lin vC ev) ev) := by
      rw [hvM.conj, I.wV_inv, ← I.wV_add]
    have hid : v * (w * w₂ * I.wV ev) * v⁻¹ * (w * w₂ * I.wV ev)⁻¹ =
        (v * w * v⁻¹ * w⁻¹) *
          (w * ((v * w₂ * v⁻¹ * w₂⁻¹) * (w₂ * (v * I.wV ev * v⁻¹ * (I.wV ev)⁻¹) * w₂⁻¹)) *
            w⁻¹) := by
      group
    rw [← hw₃, hv3, hvw, hv2, hve, hw₂M.conj, ← I.wV_add, hwM.conj, ← I.wV_add] at hid
    exact I.wV_injective hid
  have E8 : addV (addV (addV (lin (M1C ε) γ) (lin dCols (s1, 0, 0, s4))) ev) (lin dCols ev) =
      (0, 0, 0, 0) := by
    have h3 : P.d * (P.d * w₂ * P.d⁻¹) * P.d⁻¹ = w := by
      have e1 : P.d * (P.d * w₂ * P.d⁻¹) * P.d⁻¹ = P.d ^ 3 * w * (P.d ^ 3)⁻¹ := by
        rw [hw₂]; simp only [pow_succ, pow_zero, one_mul]; group
      rw [e1, P.d_cube_commute hwQ]; group
    have hs₂ : w₂ ^ 2 = I.wV (lin dCols (s1, 0, 0, s4)) := by rw [hw₂, conj_pow, hsv, hdM.conj]
    have hγi : w₂ * w = I.wV γ * (w * w₂) := by
      have : w * w₂ = I.wV γ * (w₂ * w) := by rw [← hγ]; group
      rw [this, ← mul_assoc, ← pow_two, I.sq_eq_one (I.wV_mem _), one_mul]
    have hid : P.d * (P.d * w₂ * P.d⁻¹) * P.d⁻¹ =
        I.wV γ * w * w₂ ^ 2 * I.wV ev * (P.d * I.wV ev * P.d⁻¹) := by
      rw [hw₃]
      calc P.d * (w * w₂ * I.wV ev) * P.d⁻¹ =
          (P.d * w * P.d⁻¹) * (P.d * w₂ * P.d⁻¹) * (P.d * I.wV ev * P.d⁻¹) := by group
        _ = w₂ * (w * w₂ * I.wV ev) * (P.d * I.wV ev * P.d⁻¹) := by rw [← hw₂, hw₃]
        _ = (w₂ * w) * w₂ * I.wV ev * (P.d * I.wV ev * P.d⁻¹) := by group
        _ = I.wV γ * w * w₂ ^ 2 * I.wV ev * (P.d * I.wV ev * P.d⁻¹) := by
            rw [hγi, pow_two]; group
    rw [h3, hs₂, hdM.conj] at hid
    have hid2 : w⁻¹ * I.wV γ * w * I.wV (lin dCols (s1, 0, 0, s4)) * I.wV ev *
        I.wV (lin dCols ev) = 1 := by
      calc w⁻¹ * I.wV γ * w * I.wV (lin dCols (s1, 0, 0, s4)) * I.wV ev * I.wV (lin dCols ev) =
          w⁻¹ * (I.wV γ * w * I.wV (lin dCols (s1, 0, 0, s4)) * I.wV ev *
            I.wV (lin dCols ev)) := by group
        _ = 1 := by rw [← hid]; group
    have hwi : w⁻¹ * I.wV γ * w⁻¹⁻¹ = I.wV (lin (M1C ε) γ) := (hwM.inv (M1C_sq ε)).conj γ
    rw [inv_inv] at hwi
    rw [hwi, ← I.wV_add, ← I.wV_add, ← I.wV_add, ← I.wV_zero] at hid2
    exact I.wV_injective hid2
  have he := (w_key₇ ε α ev).resolve_left (not_not.mpr E7)
  have key := (w_key ε s1 s4 γ ev).resolve_left (not_not.mpr (by
    simp only [Prod.mk.injEq]; exact ⟨he, E2, E5, E8⟩))
  simp only [Prod.mk.injEq] at key
  obtain ⟨h1, h2, h3, h4⟩ := key
  refine ⟨s1, s4, hsv, γ, hγ, ev, hw₃, he, h1, h2, h3, fun h => ?_⟩
  rw [h, one_mul] at h4
  exact h4

end Pre6

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
