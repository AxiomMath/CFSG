module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

theorem fzc_commute_t_E (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, Commute t e := by
  intro e he
  rw [baseGrp] at he
  refine Subgroup.closure_induction (p := fun e _ => Commute t e) ?_ ?_ ?_ ?_ he
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hs.t_comm₁
    · exact hs.t_comm₂
  · exact Commute.one_right t
  · intro y z _ _ hy hz
    exact hy.mul_right hz
  · intro y _ hy
    exact hy.inv_right

private theorem fzc_zpow_t (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {n : ℤ} :
    t ^ n = 1 ∨ t ^ n = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by simpa using hs.t_sq
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem fzc_mem_zpowers_t (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {q : G}
    (hq : q ∈ zpowers t) : q = 1 ∨ q = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  exact fzc_zpow_t hs

private theorem fzc_commute_zpowers_t_E (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ q ∈ zpowers t, ∀ e ∈ baseGrp x₁ x₂, Commute q e := by
  intro q hq e he
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  exact (fzc_commute_t_E hs e he).zpow_left n

private theorem fzc_comm_E_zpowers (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, ∀ q ∈ zpowers t, e * q = q * e := by
  intro e he q hq
  exact (fzc_commute_zpowers_t_E hs q hq e he).symm.eq

theorem fzc_eq_mul_t (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {w : G}
    (htw : t * w ∈ baseGrp x₁ x₂) : w = (t * w) * t := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  have h : t * (t * w) = w := by rw [← mul_assoc, ht2, one_mul]
  calc w = t * (t * w) := h.symm
    _ = (t * w) * t := (fzc_commute_t_E hs (t * w) htw).eq

private theorem fzc_inv_eq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {w : G}
    (htw : t * w ∈ baseGrp x₁ x₂) : w⁻¹ = t * (t * w)⁻¹ := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  calc w⁻¹ = ((t * w) * t)⁻¹ := by
        conv_lhs => rw [fzc_eq_mul_t hs htw]
    _ = t⁻¹ * (t * w)⁻¹ := by rw [mul_inv_rev]
    _ = t * (t * w)⁻¹ := by rw [htinv]

private theorem fzc_zpowers_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {q : G}
    (hq : q ∈ zpowers t) : q ^ 2 = 1 := by
  rcases fzc_mem_zpowers_t hs hq with hq1 | hq1
  · rw [hq1, one_pow]
  · rw [hq1]; exact hs.t_sq

private theorem fzc_zpowers_pow_four (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {q : G}
    (hq : q ∈ zpowers t) : q ^ 4 = 1 := by
  rcases fzc_mem_zpowers_t hs hq with hq1 | hq1
  · rw [hq1, one_pow]
  · rw [hq1, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs.t_sq, one_pow]

private theorem fzc_commute_zpowers (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {q₁ q₂ : G}
    (h₁ : q₁ ∈ zpowers t) (h₂ : q₂ ∈ zpowers t) : Commute q₁ q₂ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₁
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₂
  exact (Commute.refl t).zpow_zpow m n

theorem Wp_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {w : G} :
    w ∈ Wp ↔ w ∈ baseGrp x₁ x₂ ∨ t * w ∈ baseGrp x₁ x₂ := by
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  rw [hs.Wp_eq, mem_sup_iff_of_commute (fzc_comm_E_zpowers hs)]
  constructor
  · rintro ⟨e, he, q, hq, rfl⟩
    rcases fzc_mem_zpowers_t hs hq with hq1 | hq1
    · left
      rw [hq1, mul_one]
      exact he
    · right
      rw [hq1]
      have h : t * (e * t) = e := by
        rw [← mul_assoc, (fzc_commute_t_E hs e he).eq, mul_assoc, ht2, mul_one]
      rw [h]
      exact he
  · rintro (hw | htw)
    · exact ⟨w, hw, 1, Subgroup.one_mem _, (mul_one w).symm⟩
    · exact ⟨t * w, htw, t, Subgroup.mem_zpowers t, fzc_eq_mul_t hs htw⟩

theorem Wp_E (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ u ∈ Wp, ∀ v ∈ Wp, u ∉ baseGrp x₁ x₂ → v ∉ baseGrp x₁ x₂ → u * v⁻¹ ∈ baseGrp x₁ x₂ := by
  intro u hu v hv hue hve
  have ht2 : t * t = 1 := by simpa [pow_two] using hs.t_sq
  have htu : t * u ∈ baseGrp x₁ x₂ := ((Wp_mem hs).mp hu).resolve_left hue
  have htv : t * v ∈ baseGrp x₁ x₂ := ((Wp_mem hs).mp hv).resolve_left hve
  rw [fzc_eq_mul_t hs htu, fzc_inv_eq hs htv]
  have h : ((t * u) * t) * (t * (t * v)⁻¹) = (t * u) * (t * v)⁻¹ := by
    rw [mul_assoc, ← mul_assoc t t ((t * v)⁻¹), ht2, one_mul]
  rw [h]
  exact mul_mem htu (inv_mem htv)

theorem Wp_comm (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ u ∈ Wp, ∀ v ∈ Wp, u * v = v * u := by
  intro u hu v hv
  obtain ⟨e₁, he₁, q₁, hq₁, rfl⟩ :=
    (mem_sup_iff_of_commute (fzc_comm_E_zpowers hs)).mp (hs.Wp_eq ▸ hu)
  obtain ⟨e₂, he₂, q₂, hq₂, rfl⟩ :=
    (mem_sup_iff_of_commute (fzc_comm_E_zpowers hs)).mp (hs.Wp_eq ▸ hv)
  have hc : Commute (e₁ * q₁) (e₂ * q₂) :=
    ((show Commute e₁ e₂ from hs.E_comm e₁ he₁ e₂ he₂).mul_right
        (fzc_commute_zpowers_t_E hs q₂ hq₂ e₁ he₁).symm).mul_left
      ((fzc_commute_zpowers_t_E hs q₁ hq₁ e₂ he₂).mul_right
        (fzc_commute_zpowers hs hq₁ hq₂))
  exact hc.eq

theorem Wp_exp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : ∀ w ∈ Wp, w ^ 4 = 1 := by
  intro w hw
  obtain ⟨e, he, q, hq, rfl⟩ :=
    (mem_sup_iff_of_commute (fzc_comm_E_zpowers hs)).mp (hs.Wp_eq ▸ hw)
  rw [(fzc_commute_zpowers_t_E hs q hq e he).symm.mul_pow 4, hs.E_exp e he,
    fzc_zpowers_pow_four hs hq, mul_one]

theorem Wp_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ w ∈ Wp, w ^ 2 ∈ fourGrp x₁ x₂ := by
  intro w hw
  obtain ⟨e, he, q, hq, rfl⟩ :=
    (mem_sup_iff_of_commute (fzc_comm_E_zpowers hs)).mp (hs.Wp_eq ▸ hw)
  rw [(fzc_commute_zpowers_t_E hs q hq e he).symm.mul_pow 2, fzc_zpowers_sq hs hq, mul_one]
  exact hs.E_sq e he

theorem Wp_rank (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : S4A.RankLE Wp 3 := by
  rw [hs.Wp_eq]
  have h := S4A.RankLE.sup (fzc_comm_E_zpowers hs) (hs.E_rank)
    (S4A.RankLE.of_isCyclic (K := zpowers t))
  simpa using h

theorem nrm (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ u ∈ U, ∀ w ∈ Wp, u * w * u⁻¹ ∈ Wp := by
  intro u hu w hw
  by_cases hwE : w ∈ baseGrp x₁ x₂
  · exact hs.E_le_Wp (hs.nrm_E u hu w hwE)
  · have htw : t * w ∈ baseGrp x₁ x₂ := ((Wp_mem hs).mp hw).resolve_left hwE
    have htWp : t ∈ Wp := by
      rw [hs.Wp_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hute : u * t * u⁻¹ ∈ Wp := by
      have h1 : u * t * u⁻¹ * t ∈ baseGrp x₁ x₂ := hs.conj_t u hu
      have h2 : u * t * u⁻¹ = (u * t * u⁻¹ * t) * t⁻¹ := by group
      rw [h2]
      exact mul_mem (hs.E_le_Wp h1) (Wp.inv_mem htWp)
    rw [fzc_eq_mul_t hs htw]
    have h3 : u * ((t * w) * t) * u⁻¹ =
        (u * (t * w) * u⁻¹) * (u * t * u⁻¹) := by group
    rw [h3]
    exact mul_mem (hs.E_le_Wp (hs.nrm_E u hu (t * w) htw)) hute

theorem chain (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    Wp ≤ F ∧ F ≤ P ∧ P ≤ U ∧ F ≤ M₂ ∧ M₂ ≤ U ∧ F ≤ M₃ ∧ M₃ ≤ U := by
  have hWpF : Wp ≤ F := by rw [hs.F_eq]; exact le_sup_left
  have hFP : F ≤ P := by rw [hs.P_eq]; exact le_sup_left
  have hPU : P ≤ U := by rw [hs.U_eq]; exact le_sup_left
  have hFM₂ : F ≤ M₂ := by rw [hs.M₂_eq]; exact le_sup_left
  have hFM₃ : F ≤ M₃ := by rw [hs.M₃_eq]; exact le_sup_left
  have hcU : c ∈ U := by
    rw [hs.U_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hbU : b ∈ U := by
    rw [hs.U_eq]
    exact Subgroup.mem_sup_left (by
      rw [hs.P_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  refine ⟨hWpF, hFP, hPU, hFM₂, ?_, hFM₃, ?_⟩
  · rw [hs.M₂_eq]
    exact sup_le (hFP.trans hPU) (Subgroup.zpowers_le.mpr hcU)
  · rw [hs.M₃_eq]
    exact sup_le (hFP.trans hPU) (Subgroup.zpowers_le.mpr (mul_mem hbU hcU))

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
