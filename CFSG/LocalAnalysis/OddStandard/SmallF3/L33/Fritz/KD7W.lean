module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD7Two

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD}

abbrev Bzt (S : KDBase A C) : Subgroup X := zpowers S.z ⊔ zpowers t

theorem Bzt_comm (S : KDBase A C) {g : X} (hg : g ∈ A.T) {b : X} (hb : b ∈ Bzt S) :
    g * b = b * g := by
  have hle : Bzt S ≤ centralizer ({g} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S hg).symm
    · exact (A.commute_t hg).symm
  exact (mem_centralizer_singleton_iff.mp (hle hb)).symm

theorem Bzt_le_T (S : KDBase A C) : Bzt S ≤ A.T :=
  sup_le (zpowers_le.mpr (z_mem_T S)) (zpowers_le.mpr A.t_mem_T)

theorem elemAbelianTwo_Bzt (S : KDBase A C) : ElemAbelianTwo (Bzt S) :=
  Sec7.elemAbelianTwo_sup (elemAbelianTwo_z S) (SD.t_sq (A := A)) fun _ ha =>
    comm_zpowers_z S A.t_mem_T ha

namespace Setup

variable {S : KDBase A C} (P : Setup S)

theorem u_form : ∃ b ∈ Bzt S, P.D.u = b * (P.F.xF * P.F.yF) := by
  have hz : S.z ∈ Bzt S := mem_sup_left (mem_zpowers _)
  have ht : t ∈ Bzt S := mem_sup_right (mem_zpowers _)
  rcases P.D.u_eq with h | h <;> rcases P.hui with h' | h'
  · exact ⟨1, one_mem _, by rw [h, h', one_mul]⟩
  · exact ⟨S.z, hz, by rw [h, h']⟩
  · exact ⟨t, ht, by rw [h, h']⟩
  · exact ⟨t * S.z, mul_mem ht hz, by rw [h, h', mul_assoc]⟩

theorem u_mem_T : P.D.u ∈ A.T := by
  obtain ⟨b, hb, hu⟩ := P.u_form
  rw [hu]
  exact mul_mem (Bzt_le_T S hb) P.F.xyF_mem_R.1

theorem u_mul_u : P.D.u * P.D.u = 1 := by
  obtain ⟨b, hb, hu⟩ := P.u_form
  have hbc := Bzt_comm S P.F.xyF_mem_R.1 hb
  rw [hu, show b * (P.F.xF * P.F.yF) * (b * (P.F.xF * P.F.yF)) =
      (b * b) * ((P.F.xF * P.F.yF) * (P.F.xF * P.F.yF)) by
    rw [mul_assoc, ← mul_assoc (P.F.xF * P.F.yF), hbc]; group,
    ← pow_two, ← pow_two, (elemAbelianTwo_Bzt S).sq_eq_one b hb, P.F.xyF_sq, one_mul]

theorem u_inv : P.D.u⁻¹ = P.D.u := inv_eq_of_mul_eq_one_right P.u_mul_u

theorem u_comm_t : P.D.u * t = t * P.D.u := A.commute_t P.u_mem_T

theorem kF_comm_u : P.F.kF * P.D.u = P.D.u * P.F.kF := by
  obtain ⟨b, hb, hu⟩ := P.u_form
  have hle : Bzt S ≤ centralizer ({P.F.kF} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact P.F.kF_comm_z.symm
    · exact P.F.kF_comm_t.symm
  have hb' := mem_centralizer_singleton_iff.mp (hle hb)
  rw [hu, ← mul_assoc, ← hb', mul_assoc, P.F.kF_comm P.F.xyF_mem_R, ← mul_assoc]

theorem u_comm_zk {c : X} (hc : c ∈ zpowers S.z ⊔ zpowers P.F.kF) : P.D.u * c = c * P.D.u := by
  have hle : (zpowers S.z ⊔ zpowers P.F.kF : Subgroup X) ≤ centralizer ({P.D.u} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S P.u_mem_T).symm
    · exact P.kF_comm_u
  exact (mem_centralizer_singleton_iff.mp (hle hc)).symm

theorem u_y : P.D.u * P.F.yF * P.D.u⁻¹ = S.z * P.F.yF := by
  obtain ⟨b, hb, hu⟩ := P.u_form
  rw [hu, show b * (P.F.xF * P.F.yF) * P.F.yF * (b * (P.F.xF * P.F.yF))⁻¹ =
      b * (P.F.xF * (P.F.yF * P.F.yF * P.F.yF⁻¹) * P.F.xF⁻¹) * b⁻¹ by group,
    mul_inv_cancel_right, P.F.xF_conj_yF]
  exact Sec7.conj_eq_of_comm (Bzt_comm S (mul_mem (z_mem_T S) P.F.yF_mem_T) hb).symm

theorem u_conj_Q₀ {a : X} (ha : a ∈ P.Q₀) : P.D.u * a * P.D.u⁻¹ ∈ P.Q₀ := by
  have huS : P.D.u ∈ P.D.S₁ := by rw [P.D.S₁_eq]; exact mem_sup_right (mem_zpowers _)
  have hq : P.D.q0 = .homocyclic ∨ P.D.q0 = .e4q8 ∨ P.D.q0 = .exceptional := Or.inr P.hq
  have hQ₁ : P.D.u ∈ normalizer (P.D.Q₁ : Set X) :=
    Sec7.mem_normalizer_of_map_eq (P.D.Q₁_char hq P.D.u (le_normalizer huS))
  have hE : P.D.u ∈ normalizer (S.E P.F.yF : Set X) := P.D.S₁_le huS
  exact Sec7.conj_mem_of_map_eq (P.D.Q0_invariant P.D.u ⟨hE, hQ₁⟩) ha

theorem mem_zk_of_mem_E0 {e : X} (he : e ∈ P.E₀) (hfix : P.D.u * e * P.D.u⁻¹ = e) :
    e ∈ (zpowers S.z ⊔ zpowers P.F.kF : Subgroup X) := by
  have he' : e ∈ S.E0 P.F.yF P.F.kF := he
  rw [P.F.E0_eq'] at he'
  rcases Sec7.mem_or_of_mem_sup P.F.elemAbelianTwo_zk P.F.yF_sq
      (fun _ hb => P.F.yF_comm_zk hb) he' with h | h
  · exact h
  · exfalso
    set c := e * P.F.yF with hc
    have hec : e = c * P.F.yF := by rw [hc, mul_assoc, P.F.yF_yF, mul_one]
    have : P.D.u * e * P.D.u⁻¹ = S.z * e := by
      rw [hec, show P.D.u * (c * P.F.yF) * P.D.u⁻¹ = (P.D.u * c * P.D.u⁻¹) *
          (P.D.u * P.F.yF * P.D.u⁻¹) by group, P.u_y, P.u_comm_zk h, mul_inv_cancel_right,
        ← mul_assoc, P.F.elemAbelianTwo_zk.comm c h S.z (mem_sup_left (mem_zpowers _)),
        mul_assoc]
    rw [hfix] at this
    exact z_ne_one S (by simpa using this.symm)

theorem u_conj_E0 {e : X} (he : e ∈ P.E₀) : P.D.u * e * P.D.u⁻¹ ∈ P.E₀ := by
  have he' : e ∈ S.E0 P.F.yF P.F.kF := he
  rw [P.F.E0_eq'] at he'
  rcases Sec7.mem_or_of_mem_sup P.F.elemAbelianTwo_zk P.F.yF_sq
      (fun _ hb => P.F.yF_comm_zk hb) he' with h | h
  · rw [Sec7.conj_eq_of_comm (P.u_comm_zk h)]; exact he
  · have hec : e = (e * P.F.yF) * P.F.yF := by rw [mul_assoc, P.F.yF_yF, mul_one]
    rw [hec, Sec7.conj_mul_eq, Sec7.conj_eq_of_comm (P.u_comm_zk h), P.u_y]
    exact mul_mem (mul_mem he P.F.yF_mem_E0) (mul_mem P.F.z_mem_E0 P.F.yF_mem_E0)

theorem mul_u_conj_mem {g : X} (hg : g ∈ P.E₀) :
    g * (P.D.u * g * P.D.u⁻¹) = 1 ∨ g * (P.D.u * g * P.D.u⁻¹) = S.z := by
  have hg' : g ∈ S.E0 P.F.yF P.F.kF := hg
  rw [P.F.E0_eq'] at hg'
  rcases Sec7.mem_or_of_mem_sup P.F.elemAbelianTwo_zk P.F.yF_sq
      (fun _ hb => P.F.yF_comm_zk hb) hg' with h | h
  · left
    rw [Sec7.conj_eq_of_comm (P.u_comm_zk h), ← pow_two, P.F.elemAbelianTwo_zk.sq_eq_one g h]
  · right
    set c := g * P.F.yF with hc
    have hgc : g = c * P.F.yF := by rw [hc, mul_assoc, P.F.yF_yF, mul_one]
    rw [hgc, Sec7.conj_mul_eq, Sec7.conj_eq_of_comm (P.u_comm_zk h), P.u_y]
    have hcy : P.F.yF * c = c * P.F.yF := P.F.yF_comm_zk h
    have hzy : P.F.yF * S.z = S.z * P.F.yF := P.F.z_comm_yF.symm
    calc c * P.F.yF * (c * (S.z * P.F.yF)) = (c * c) * S.z * (P.F.yF * P.F.yF) := by
          rw [show c * P.F.yF * (c * (S.z * P.F.yF)) = c * (P.F.yF * c) * S.z * P.F.yF by
            group, hcy, ← mul_assoc, mul_assoc (c * c) P.F.yF, hzy]
          group
      _ = S.z := by
          rw [← pow_two, P.F.elemAbelianTwo_zk.sq_eq_one c h, P.F.yF_yF, one_mul, mul_one]

end Setup

end KD7

end CFSG.OddStandard.SmallF3.L33.KD
