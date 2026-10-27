module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N3

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_t_conj_zpowers (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.z) :
    d.t * w * d.t⁻¹ = w := by
  have h := hd.L_comm_t (s56_E_le_L d (hd.s56_zpowers_le_E hw))
  rw [← h]; group

theorem Hyp.s56_E_comm_B_mem (hd : d.Hyp) {e b : G} (he : e ∈ d.E) (hb : b ∈ d.B) :
    e * b * e⁻¹ * b⁻¹ ∈ zpowers d.z := by
  have het : e * d.t = d.t * e := hd.L_comm_t (s56_E_le_L d he)
  have key : ∀ f ∈ d.F, e * f * e⁻¹ * f⁻¹ ∈ zpowers d.z := fun f hf => by
    have h := hd.s56_J_comm_E (s56_F_le_J d hf) he
    have e1 : e * f * e⁻¹ * f⁻¹ = (f * e * f⁻¹ * e⁻¹)⁻¹ := by group
    rw [e1]; exact inv_mem h
  rcases (hd.s56_mem_B_iff).1 hb with hf | hf
  · exact key b hf
  · have hb' : b = d.t * (d.t * b) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
    have e2 : e * b * e⁻¹ * b⁻¹ = d.t * (e * (d.t * b) * e⁻¹ * (d.t * b)⁻¹) * d.t⁻¹ := by
      conv_lhs => rw [hb']
      calc e * (d.t * (d.t * b)) * e⁻¹ * (d.t * (d.t * b))⁻¹
          = (e * d.t * e⁻¹) * (e * (d.t * b) * e⁻¹) * (d.t * b)⁻¹ * d.t⁻¹ := by group
        _ = d.t * (e * (d.t * b) * e⁻¹ * (d.t * b)⁻¹) * d.t⁻¹ := by
            rw [show e * d.t * e⁻¹ = d.t by rw [het]; group]
            group
    rw [e2, hd.s56_t_conj_zpowers (key _ hf)]
    exact key _ hf

theorem Hyp.s56_E_cent_B_iff (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    (∀ b ∈ d.B, e * b = b * e) ↔ e ∈ d.F := by
  have het : e * d.t = d.t * e := hd.L_comm_t (s56_E_le_L d he)
  constructor
  · intro h
    exact (hd.s56_pv7_comm_iff he).1 (h _ (s56_F_le_B d hd.s56_pv7_mem_F)).symm
  · intro hF b hb
    have hcF : ∀ f ∈ d.F, e * f = f * e := fun f hf => hd.s56_F_comm hF hf
    rcases (hd.s56_mem_B_iff).1 hb with hf | hf
    · exact hcF b hf
    · have hb' : b = d.t * (d.t * b) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
      rw [hb']
      calc e * (d.t * (d.t * b)) = (e * d.t) * (d.t * b) := by group
        _ = d.t * (e * (d.t * b)) := by rw [het]; group
        _ = d.t * ((d.t * b) * e) := by rw [hcF _ hf]
        _ = d.t * (d.t * b) * e := by group

theorem Hyp.s56_E_axis_B (hd : d.Hyp) {e : G} (he : e ∈ d.E) (heF : e ∉ d.F) {b : G}
    (hb : b ∈ d.B) : e * b = b * e ↔ b ∈ d.A := by
  have het : e * d.t = d.t * e := hd.L_comm_t (s56_E_le_L d he)
  constructor
  · intro h
    have key : ∀ f ∈ d.F, e * f = f * e → f ∈ d.E := fun f hf hef => by
      rcases Hyp.s56_F_cases d hf with hfE | hfE
      · exact hfE
      · exfalso
        apply heF
        have hef' : Commute e f := hef
        have hev : Commute e (d.pv 7 * f) := hd.s56_E_comm he hfE
        have h7 : Commute e (d.pv 7) := by
          have := hev.mul_right hef'.inv_right
          simpa using this
        exact (hd.s56_pv7_comm_iff he).1 h7.symm.eq
    rcases (hd.s56_mem_B_iff).1 hb with hf | hf
    · exact (hd.s56_mem_A_iff).2 (Or.inl (key b hf h))
    · refine (hd.s56_mem_A_iff).2 (Or.inr (key _ hf ?_))
      calc e * (d.t * b) = (e * d.t) * b := by group
        _ = d.t * (e * b) := by rw [het]; group
        _ = d.t * (b * e) := by rw [h]
        _ = (d.t * b) * e := by group
  · intro hA
    have hAc := congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm
      ⟨e, s56_E_le_A d he⟩ ⟨b, hA⟩)
    exact hAc

theorem Hyp.s56_pv7_comm_pv8 (hd : d.Hyp) :
    d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ * (d.pv 8)⁻¹ = d.z := by
  have h := s56_pv7_conj_pv8 d
  have hc := hd.s56_E_comm (s56_pv8_mem_E d) hd.s56_z_mem_E
  rw [h, hc]; group

theorem Hyp.s56_pv8_comm_pv7 (hd : d.Hyp) :
    d.pv 8 * d.pv 7 * (d.pv 8)⁻¹ * (d.pv 7)⁻¹ = d.z := by
  have h := hd.s56_pv7_comm_pv8
  have e : d.pv 8 * d.pv 7 * (d.pv 8)⁻¹ * (d.pv 7)⁻¹ =
      (d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ * (d.pv 8)⁻¹)⁻¹ := by group
  rw [e, h]
  exact inv_eq_of_mul_eq_one_right hd.s56_z_sq

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
