module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Six
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Y

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_pv7_conj_A (hd : d.Hyp) {a : G} (ha : a ∈ d.A) :
    d.pv 7 * a * (d.pv 7)⁻¹ * a⁻¹ ∈ zpowers d.z := by
  rcases (hd.s56_mem_A_iff).1 ha with h | h
  · exact hd.s56_pv7_conj_E h
  · obtain ⟨e, he, rfl⟩ : ∃ e ∈ d.E, a = d.t * e :=
      ⟨d.t * a, h, by rw [← mul_assoc, hd.t_mul_self, one_mul]⟩
    have hv := hd.s56_pv7_comm_t
    have hz := hd.s56_pv7_conj_E he
    have hzc : ∀ w ∈ zpowers d.z, d.t * w = w * d.t := fun w hw =>
      (hd.L_comm_t (s56_E_le_L d (hd.s56_zpowers_le_E hw))).symm
    have e1 : d.pv 7 * (d.t * e) * (d.pv 7)⁻¹ * (d.t * e)⁻¹ =
        d.t * (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * d.t⁻¹ := by
      have : d.pv 7 * d.t * (d.pv 7)⁻¹ = d.t := by rw [hv]; group
      calc d.pv 7 * (d.t * e) * (d.pv 7)⁻¹ * (d.t * e)⁻¹
          = (d.pv 7 * d.t * (d.pv 7)⁻¹) * (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * d.t⁻¹ := by group
        _ = d.t * (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * d.t⁻¹ := by rw [this]
    rw [e1, hzc _ hz]
    simpa using hz

theorem s56_pv11_mem_E (d : Data G) : d.pv 11 ∈ d.E :=
  mem_liftSub.2 ⟨_, Model.parrottV_eleven_mem_hatE,
    s56_hatE_le_titsD Model.parrottV_eleven_mem_hatE, rfl⟩

theorem Hyp.s56_pv11_not_mem (hd : d.Hyp) : d.pv 11 ∉ zpowers d.z := by
  intro h
  have h11 : Model.parrottV 11 ∈ titsD := s56_hatE_le_titsD Model.parrottV_eleven_mem_hatE
  rcases hd.s56_mem_zpowers_z h with h1 | h1
  · have := d.lift_inj h11 (one_mem _) (by rw [d.lift_one]; exact h1)
    exact (Model.parrottV_ne_one (by norm_num) (by norm_num)) this
  · have := d.lift_inj h11 titsZ_mem_titsD (by rw [d.lift_titsZ]; exact h1)
    exact Model.parrottV_eleven_not_mem_zpowers (this ▸ mem_zpowers _)

theorem Hyp.s56_z_mem_F (hd : d.Hyp) : d.z ∈ d.F := by
  have h12 : Model.parrottV 12 ∈ Model.parrottF := Model.parrottV_mem_parrottF (by simp)
  have hD : Model.parrottV 12 ∈ titsD := Model.parrottF_le_titsD h12
  have h := (mem_liftSub (d := d)).2 ⟨_, h12, hD, rfl⟩
  rw [Model.parrottV_twelve, d.lift_titsZ] at h
  exact h


theorem Hyp.s56_pv7_inv_C (hd : d.Hyp) {c : G} (hc : c ∈ centralizer (d.A : Set G))
    (h : d.pv 7 * c * (d.pv 7)⁻¹ = c⁻¹) : c ∈ d.A ∧ d.pv 7 * c = c * d.pv 7 := by
  have hAA : ∀ a ∈ d.A, a * a = 1 := fun a ha => by
    have := hd.A_facts.2.2.1.2 a ha
    simpa [pow_two] using this
  have hAcomm : ∀ a ∈ d.A, ∀ b ∈ d.A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have key : ∀ c ∈ d.A, d.pv 7 * c * (d.pv 7)⁻¹ = c⁻¹ → d.pv 7 * c = c * d.pv 7 := by
    intro c hcA hcc
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hAA c hcA)
    rw [hci] at hcc
    calc d.pv 7 * c = d.pv 7 * c * (d.pv 7)⁻¹ * d.pv 7 := by group
      _ = c * d.pv 7 := by rw [hcc]
  rcases hd.s56_C_cases with hCA | ⟨y, hyy, hCy, hyA', hyx, hyA, hyv, hcov, hyt⟩
  · rw [hCA] at hc
    exact ⟨hc, key c hc h⟩
  · rcases hcov c hc with hcA | ⟨a, ha, rfl⟩
    · exact ⟨hcA, key c hcA h⟩
    · exfalso
      have hu := s56_pv11_mem_E d
      have huA := s56_E_le_A d hu
      have hzA := s56_E_le_A d hd.s56_z_mem_E
      obtain ⟨hw⟩ : Nonempty (d.pv 7 * a * (d.pv 7)⁻¹ * a⁻¹ ∈ zpowers d.z) :=
        ⟨hd.s56_pv7_conj_A ha⟩
      set w := d.pv 7 * a * (d.pv 7)⁻¹ * a⁻¹ with hwdef
      have hwA : w ∈ d.A := s56_E_le_A d (hd.s56_zpowers_le_E hw)
      have hvav : d.pv 7 * a * (d.pv 7)⁻¹ = w * a := by rw [hwdef]; group
      have hv7 := s56_pv7_inv d
      have hvy : d.pv 7 * y * (d.pv 7)⁻¹ = d.pv 11 * y := by
        have h1 : d.pv 7 * (y * d.pv 7 * y⁻¹) = d.pv 11 := by
          rw [hyv, ← mul_assoc, s56_pv7_mul_self, one_mul]
        calc d.pv 7 * y * (d.pv 7)⁻¹ = d.pv 7 * y * d.pv 7 := by rw [hv7]
          _ = (d.pv 7 * (y * d.pv 7 * y⁻¹)) * y := by group
          _ = d.pv 11 * y := by rw [h1]
      have hyinv : y⁻¹ = y * d.z := by
        have hzz := hd.s56_z_sq
        refine inv_eq_of_mul_eq_one_right ?_
        calc y * (y * d.z) = (y * y) * d.z := by group
          _ = d.z * d.z := by rw [hyy]
          _ = 1 := hzz
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAA a ha)
      have hya := hyA' a ha
      have hyu := hyA' _ huA
      have hyw := hyA' _ hwA
      have hyz' := hyA' _ hzA
      have h1 : d.pv 11 * y * (w * a) = a * (y * d.z) := by
        have e1 : d.pv 7 * (y * a) * (d.pv 7)⁻¹ = d.pv 11 * y * (w * a) := by
          rw [show d.pv 7 * (y * a) * (d.pv 7)⁻¹ =
            (d.pv 7 * y * (d.pv 7)⁻¹) * (d.pv 7 * a * (d.pv 7)⁻¹) by group, hvy, hvav]
        have e2 : (y * a)⁻¹ = a * (y * d.z) := by
          rw [mul_inv_rev, hai, hyinv]
        rw [← e1, ← e2]
        exact h
      have h2 : d.pv 11 * w = d.z := by
        have hcomm1 : d.pv 11 * y * (w * a) = y * (d.pv 11 * w * a) := by
          rw [show d.pv 11 * y * (w * a) = (d.pv 11 * y) * (w * a) from rfl, ← hyu]; group
        have hcomm2 : a * (y * d.z) = y * (d.z * a) := by
          calc a * (y * d.z) = (a * y) * d.z := by group
            _ = (y * a) * d.z := by rw [hya]
            _ = y * (a * d.z) := by group
            _ = y * (d.z * a) := by rw [hAcomm a ha d.z hzA]
        rw [hcomm1, hcomm2] at h1
        have h3 := mul_left_cancel h1
        have h4 : d.pv 11 * w * a = d.z * a := h3
        exact mul_right_cancel h4
      apply hd.s56_pv11_not_mem
      have : d.pv 11 = d.z * w⁻¹ := by
        rw [← h2]; group
      rw [this]
      exact mul_mem (mem_zpowers _) (inv_mem hw)

theorem Hyp.s56_pv7_mem_F (hd : d.Hyp) : d.pv 7 ∈ d.F :=
  mem_liftSub.2 ⟨_, Model.parrottV_mem_parrottF (by simp), Model.parrottF_le_titsD
    (Model.parrottV_mem_parrottF (by simp)), rfl⟩

theorem Hyp.s56_conj_mem_B (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q0)
    (hε : d.s56Eps q ∈ d.F) {b : G} (hb : b ∈ d.B) : q * b * q⁻¹ ∈ d.B := by
  have hqM := hd.s56_Q0_le_M h49 hq
  have hFB : d.F ≤ d.B := le_sup_left
  have hz := hd.s56_z_mem_F
  have htB : d.t ∈ d.B := mem_sup_right (mem_zpowers _)
  have hEF : ∀ e ∈ d.E, e ∈ d.F → q * e * q⁻¹ ∈ d.F := by
    intro e he heF
    have h := ((hd.s56_mem_Q0_iff h49).1 hq).2 e he
    have h' : q * e * q⁻¹ = (q * e * q⁻¹ * e⁻¹) * e := by group
    rw [h']
    refine mul_mem ?_ heF
    rcases hd.s56_mem_zpowers_z h with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hz
  have hqv : q * d.pv 7 * q⁻¹ ∈ d.B := by
    have hc := (hd.s56_comm_pv7_mem_C_iff h49 hq).2 hε
    set c := q * d.pv 7 * q⁻¹ * (d.pv 7)⁻¹ with hcdef
    have hcv : q * d.pv 7 * q⁻¹ = c * d.pv 7 := by rw [hcdef]; group
    have hinv : d.pv 7 * c * (d.pv 7)⁻¹ = c⁻¹ := by
      have hsq : (c * d.pv 7) * (c * d.pv 7) = 1 := by
        rw [← hcv]
        calc q * d.pv 7 * q⁻¹ * (q * d.pv 7 * q⁻¹) = q * (d.pv 7 * d.pv 7) * q⁻¹ := by group
          _ = 1 := by rw [s56_pv7_mul_self]; group
      have hv7 := s56_pv7_inv d
      calc d.pv 7 * c * (d.pv 7)⁻¹ = d.pv 7 * c * d.pv 7 := by rw [hv7]
        _ = c⁻¹ := by
          have h1 : c * (d.pv 7 * c * d.pv 7) = 1 := by
            calc c * (d.pv 7 * c * d.pv 7) = (c * d.pv 7) * (c * d.pv 7) := by group
              _ = 1 := hsq
          exact (eq_inv_of_mul_eq_one_right h1)
    obtain ⟨hcA, hcv'⟩ := hd.s56_pv7_inv_C hc hinv
    have hcB : c ∈ d.B := (hd.s56_pv7_comm_A_iff hcA).1 hcv'
    rw [hcv]
    exact mul_mem hcB (hFB (hd.s56_pv7_mem_F))
  rcases (hd.s56_mem_B_iff).1 hb with hf | hf
  ·
    rcases Hyp.s56_F_cases d hf with he | he
    · exact hFB (hEF b he hf)
    ·
      have hvF := hd.s56_pv7_mem_F
      have heF : d.pv 7 * b ∈ d.F := mul_mem hvF hf
      have hb' : b = d.pv 7 * (d.pv 7 * b) := by
        rw [← mul_assoc, s56_pv7_mul_self, one_mul]
      rw [hb']
      have e1 : q * (d.pv 7 * (d.pv 7 * b)) * q⁻¹ =
          (q * d.pv 7 * q⁻¹) * (q * (d.pv 7 * b) * q⁻¹) := by group
      rw [e1]
      exact mul_mem hqv (hFB (hEF _ he heF))
  ·
    have hb' : b = d.t * (d.t * b) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
    have hqt : q * d.t * q⁻¹ = d.t * d.s56Eps q := hd.s56_conj_t q
    have hFq : q * (d.t * b) * q⁻¹ ∈ d.B := by
      rcases Hyp.s56_F_cases d hf with he | he
      · exact hFB (hEF _ he hf)
      · have hvF := hd.s56_pv7_mem_F
        have heF : d.pv 7 * (d.t * b) ∈ d.F := mul_mem hvF hf
        have hb'' : d.t * b = d.pv 7 * (d.pv 7 * (d.t * b)) := by
          rw [← mul_assoc, s56_pv7_mul_self, one_mul]
        rw [hb'']
        have e1 : q * (d.pv 7 * (d.pv 7 * (d.t * b))) * q⁻¹ =
            (q * d.pv 7 * q⁻¹) * (q * (d.pv 7 * (d.t * b)) * q⁻¹) := by group
        rw [e1]
        exact mul_mem hqv (hFB (hEF _ he heF))
    have e : q * b * q⁻¹ = (q * d.t * q⁻¹) * (q * (d.t * b) * q⁻¹) := by
      conv_lhs => rw [hb']
      group
    rw [e, hqt]
    exact mul_mem (mul_mem htB (hFB hε)) hFq

theorem Hyp.s56_mem_N_iff_eps (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G}
    (hq : q ∈ d.s56Q0) : q ∈ d.N ↔ d.s56Eps q ∈ d.F := by
  have hqM := hd.s56_Q0_le_M h49 hq
  refine ⟨fun hN => hd.s56_eps_mem_F_of_mem_N hqM hN, fun hε => ?_⟩
  have hz := hd.s56_z_mem_F
  have hε' : d.s56Eps q⁻¹ ∈ d.F := by
    have hqinv := inv_mem hq
    have h1 := hd.s56_eps_mul q⁻¹ q
    rw [inv_mul_cancel, hd.s56_eps_one] at h1
    have hw := ((hd.s56_mem_Q0_iff h49).1 hqinv).2 _ (hd.s56_eps_mem_E hqM)
    have h2 : d.s56Eps q⁻¹ = (q⁻¹ * d.s56Eps q * q)⁻¹ := by
      have := mul_eq_one_iff_eq_inv.1 h1.symm
      simpa using this
    rw [h2]
    refine inv_mem ?_
    have e : q⁻¹ * d.s56Eps q * q = (q⁻¹ * d.s56Eps q * q * (d.s56Eps q)⁻¹) * d.s56Eps q := by
      group
    rw [e]
    refine mul_mem ?_ hε
    have hw' : q⁻¹ * d.s56Eps q * q * (d.s56Eps q)⁻¹ ∈ zpowers d.z := by simpa using hw
    rcases hd.s56_mem_zpowers_z hw' with h3 | h3
    · rw [h3]; exact one_mem _
    · rw [h3]; exact hz
  rw [Data.N, mem_normalizer_iff]
  intro b
  constructor
  · exact fun hb => hd.s56_conj_mem_B h49 hq hε hb
  · intro hb
    have h := hd.s56_conj_mem_B h49 (inv_mem hq) hε' hb
    have e : q⁻¹ * (q * b * q⁻¹) * q⁻¹⁻¹ = b := by group
    rwa [e] at h

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
