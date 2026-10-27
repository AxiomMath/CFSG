module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Coord
public import CFSG.LocalAnalysis.EvenBN.Tits.S56J
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.SixModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem s56_pv7_mem_J (d : Data G) : d.pv 7 ∈ d.s56J := s56_pv_mem_J d (by simp)

theorem s56_pv7_mem_L (d : Data G) : d.pv 7 ∈ d.L := d.lift_mem _

theorem Hyp.s56_pv7_mem_M (hd : d.Hyp) : d.pv 7 ∈ d.M := hd.s56_J_le_M (s56_pv7_mem_J d)

theorem Hyp.s56_pv7_mem_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.pv 7 ∈ d.s56Q0 :=
  hd.s56_J_le_Q0 h49 (s56_pv7_mem_J d)

theorem s56_pv7_mul_self (d : Data G) : d.pv 7 * d.pv 7 = 1 := by
  have h7 : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD (Model.parrottV_mem_parrottF
    (by simp))
  rw [pv, ← d.lift_mul h7 h7, Model.parrottV_seven_sq, d.lift_one]

theorem Hyp.s56_pv7_comm_t (hd : d.Hyp) : d.pv 7 * d.t = d.t * d.pv 7 :=
  hd.L_comm_t (s56_pv7_mem_L d)

theorem s56_pv7_inv (d : Data G) : (d.pv 7)⁻¹ = d.pv 7 :=
  inv_eq_of_mul_eq_one_right (s56_pv7_mul_self d)

theorem Hyp.s56_F_le_M (hd : d.Hyp) : d.F ≤ d.M := (s56_F_le_J d).trans hd.s56_J_le_M

theorem s56_F_le_L (d : Data G) : d.F ≤ d.L := d.liftSub_le _

theorem Hyp.s56_mem_B_iff (hd : d.Hyp) {x : G} : x ∈ d.B ↔ x ∈ d.F ∨ d.t * x ∈ d.F :=
  (hd.tSup_facts (s56_F_le_L d)).1 x

theorem Hyp.s56_B_inf_L (hd : d.Hyp) {x : G} (hx : x ∈ d.B) (hxL : x ∈ d.L) : x ∈ d.F :=
  (hd.tSup_facts (s56_F_le_L d)).2.1 x hx hxL

theorem Hyp.s56_E_inf_B (hd : d.Hyp) {e : G} (he : e ∈ d.E) (hB : e ∈ d.B) : e ∈ d.F :=
  hd.s56_B_inf_L hB (s56_E_le_L d he)

theorem Hyp.s56_pv7_conj_E (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹ ∈ zpowers d.z :=
  hd.s56_J_comm_E (s56_pv7_mem_J d) he

theorem Hyp.s56_pv7_comm_iff (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    d.pv 7 * e = e * d.pv 7 ↔ e ∈ d.F := by
  obtain ⟨ê, hê, hêD, rfl⟩ := mem_liftSub.1 he
  have h7 : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD (Model.parrottV_mem_parrottF
    (by simp))
  rw [pv, d.lift_comm_iff h7 hêD, Model.parrottV_seven_comm_iff hê]
  constructor
  · intro hF
    exact mem_liftSub.2 ⟨ê, hF, hêD, rfl⟩
  · intro hF
    obtain ⟨f, hf, hfD, hfe⟩ := mem_liftSub.1 hF
    rwa [d.lift_inj hfD hêD hfe] at hf

theorem s56_hatE_le_titsD : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD

theorem s56_pv8_mem_E (d : Data G) : d.pv 8 ∈ d.E :=
  mem_liftSub.2 ⟨_, Model.parrottV_eight_mem_hatE,
    s56_hatE_le_titsD Model.parrottV_eight_mem_hatE, rfl⟩

theorem Hyp.s56_orderOf_z (hd : d.Hyp) : orderOf d.z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hd.s56_z_sq) hd.s56_z_ne_one

theorem Hyp.s56_mem_zpowers_z (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.z) : w = 1 ∨ w = d.z :=
  (Model.mem_zpowers_of_orderOf_two hd.s56_orderOf_z).1 hw

theorem s56_pv7_conj_pv8 (d : Data G) : d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ = d.pv 8 * d.z := by
  have h7 : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD (Model.parrottV_mem_parrottF
    (by simp))
  have h8 : Model.parrottV 8 ∈ titsD := s56_hatE_le_titsD Model.parrottV_eight_mem_hatE
  have := d.lift_conj h7 h8
  rw [Model.parrottV_seven_conj_eight, d.lift_mul h8 titsZ_mem_titsD, d.lift_titsZ] at this
  exact this.symm

theorem Hyp.s56_pv8_not_mem_F (hd : d.Hyp) : d.pv 8 ∉ d.F := by
  intro hF
  have hc := (hd.s56_pv7_comm_iff (s56_pv8_mem_E d)).2 hF
  have h := s56_pv7_conj_pv8 d
  rw [hc, mul_assoc, mul_inv_cancel, mul_one] at h
  exact hd.s56_z_ne_one ((mul_eq_left.1 h.symm))

theorem Hyp.s56_E_cases (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    e ∈ d.F ∨ d.pv 8 * e ∈ d.F := by
  by_cases hc : d.pv 7 * e = e * d.pv 7
  · exact Or.inl ((hd.s56_pv7_comm_iff he).1 hc)
  · right
    have hz := hd.s56_pv7_conj_E he
    have hw : d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹ = d.z := by
      rcases hd.s56_mem_zpowers_z hz with h | h
      · exfalso
        apply hc
        calc d.pv 7 * e = (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * e * d.pv 7 := by group
          _ = e * d.pv 7 := by rw [h]; group
      · exact h
    have hconj : d.pv 7 * e * (d.pv 7)⁻¹ = d.z * e := by
      calc d.pv 7 * e * (d.pv 7)⁻¹ = (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * e := by group
        _ = d.z * e := by rw [hw]
    have hmE : d.pv 8 * e ∈ d.E := mul_mem (s56_pv8_mem_E d) he
    refine (hd.s56_pv7_comm_iff hmE).1 ?_
    have hzc8 : d.pv 8 * d.z = d.z * d.pv 8 :=
      hd.s56_E_comm (s56_pv8_mem_E d) hd.s56_z_mem_E
    have hzce : d.z * e = e * d.z := hd.s56_E_comm hd.s56_z_mem_E he
    have hv := s56_pv7_conj_pv8 d
    have hzz := hd.s56_z_sq
    have hconj' : d.pv 7 * (d.pv 8 * e) * (d.pv 7)⁻¹ = d.pv 8 * e := by
      calc d.pv 7 * (d.pv 8 * e) * (d.pv 7)⁻¹
          = (d.pv 7 * d.pv 8 * (d.pv 7)⁻¹) * (d.pv 7 * e * (d.pv 7)⁻¹) := by group
        _ = (d.pv 8 * d.z) * (d.z * e) := by rw [hv, hconj]
        _ = d.pv 8 * (d.z * d.z) * e := by group
        _ = d.pv 8 * e := by rw [hzz]; group
    calc d.pv 7 * (d.pv 8 * e) = d.pv 7 * (d.pv 8 * e) * (d.pv 7)⁻¹ * d.pv 7 := by group
      _ = (d.pv 8 * e) * d.pv 7 := by rw [hconj']

theorem Hyp.s56_F_cases (d : Data G) {f : G} (hf : f ∈ d.F) : f ∈ d.E ∨ d.pv 7 * f ∈ d.E := by
  obtain ⟨fp, hfp, hfpD, rfl⟩ := mem_liftSub.1 hf
  have h7 : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD (Model.parrottV_mem_parrottF
    (by simp))
  rcases Model.parrottF_cases hfp with h | h
  · exact Or.inl (mem_liftSub.2 ⟨fp, h, hfpD, rfl⟩)
  · refine Or.inr ?_
    rw [pv, ← d.lift_mul h7 hfpD]
    exact mem_liftSub.2 ⟨_, h, mul_mem h7 hfpD, rfl⟩

theorem Hyp.s56_mem_centralizer_A_iff (hd : d.Hyp) {g : G} :
    g ∈ centralizer (d.A : Set G) ↔ (∀ e ∈ d.E, e * g = g * e) ∧ g * d.t = d.t * g := by
  constructor
  · intro h
    rw [mem_centralizer_iff] at h
    exact ⟨fun e he => h e (s56_E_le_A d he), (h d.t d.s56_t_mem_A).symm⟩
  · rintro ⟨hE, ht⟩
    rw [mem_centralizer_iff]
    intro a ha
    rcases (hd.s56_mem_A_iff).1 ha with h | h
    · exact hE a h
    · have hta : a = d.t * (d.t * a) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
      have := hE _ h
      calc a * g = d.t * (d.t * a) * g := by rw [← hta]
        _ = d.t * ((d.t * a) * g) := by group
        _ = d.t * (g * (d.t * a)) := by rw [this]
        _ = (d.t * g) * (d.t * a) := by group
        _ = (g * d.t) * (d.t * a) := by rw [ht]
        _ = g * (d.t * (d.t * a)) := by group
        _ = g * a := by rw [← hta]

theorem Hyp.s56_pv7_comm_A_iff (hd : d.Hyp) {a : G} (ha : a ∈ d.A) :
    d.pv 7 * a = a * d.pv 7 ↔ a ∈ d.B := by
  have htL := hd.t_not_mem
  rcases (hd.s56_mem_A_iff).1 ha with h | h
  · rw [hd.s56_pv7_comm_iff h, hd.s56_mem_B_iff]
    constructor
    · exact Or.inl
    · rintro (h' | h')
      · exact h'
      · exfalso
        apply htL
        have e : d.t = (d.t * a) * a⁻¹ := by group
        rw [e]
        exact mul_mem (s56_F_le_L d h') (inv_mem (s56_E_le_L d h))
  · obtain ⟨e, he, rfl⟩ : ∃ e ∈ d.E, a = d.t * e :=
      ⟨d.t * a, h, by rw [← mul_assoc, hd.t_mul_self, one_mul]⟩
    have hte : d.t * (d.t * e) = e := by rw [← mul_assoc, hd.t_mul_self, one_mul]
    have hcomm : d.pv 7 * (d.t * e) = (d.t * e) * d.pv 7 ↔ d.pv 7 * e = e * d.pv 7 := by
      have h1 : d.pv 7 * (d.t * e) = d.t * (d.pv 7 * e) := by
        rw [← mul_assoc, hd.s56_pv7_comm_t, mul_assoc]
      have h2 : d.t * e * d.pv 7 = d.t * (e * d.pv 7) := by rw [mul_assoc]
      rw [h1, h2]
      exact ⟨fun hc => mul_left_cancel hc, fun hc => by rw [hc]⟩
    rw [hcomm, hd.s56_pv7_comm_iff he, hd.s56_mem_B_iff, hte]
    constructor
    · intro hF
      exact Or.inr hF
    · rintro (h' | h')
      · exfalso
        apply htL
        have e' : d.t = (d.t * e) * e⁻¹ := by group
        rw [e']
        exact mul_mem (s56_F_le_L d h') (inv_mem (s56_E_le_L d he))
      · exact h'

theorem Hyp.s56_comm_pv7_mem_C_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G}
    (hq : q ∈ d.s56Q0) :
    q * d.pv 7 * q⁻¹ * (d.pv 7)⁻¹ ∈ centralizer (d.A : Set G) ↔ d.s56Eps q ∈ d.F := by
  have hv := hd.s56_pv7_mem_Q0 h49
  obtain ⟨hct, hb⟩ := hd.s56_comm_t h49 hv hd.s56_pv7_comm_t hq
  have hqM := hd.s56_Q0_le_M h49 hq
  have hεE := hd.s56_eps_mem_E hqM
  set c₀ := d.pv 7 * q * (d.pv 7)⁻¹ * q⁻¹ with hc₀
  have hc₀Q2 : c₀ ∈ d.s56Q2 := hd.s56_Q0_comm_mem_Q2 h49 hv hq
  have hc : q * d.pv 7 * q⁻¹ * (d.pv 7)⁻¹ = c₀⁻¹ := by rw [hc₀]; group
  rw [hc]
  have hbF : (d.pv 7 * d.s56Eps q * (d.pv 7)⁻¹ * (d.s56Eps q)⁻¹ = 1) ↔ d.s56Eps q ∈ d.F := by
    rw [← hd.s56_pv7_comm_iff hεE]
    constructor
    · intro h
      calc d.pv 7 * d.s56Eps q = (d.pv 7 * d.s56Eps q * (d.pv 7)⁻¹ * (d.s56Eps q)⁻¹) *
            d.s56Eps q * d.pv 7 := by group
        _ = d.s56Eps q * d.pv 7 := by rw [h]; group
    · intro h
      calc d.pv 7 * d.s56Eps q * (d.pv 7)⁻¹ * (d.s56Eps q)⁻¹
          = (d.pv 7 * d.s56Eps q) * (d.s56Eps q * d.pv 7)⁻¹ := by group
        _ = 1 := by rw [h]; group
  rw [← hbF]
  have hc₀E : ∀ e ∈ d.E, e * c₀ = c₀ * e := fun e he =>
    ((s56_mem_Q2_iff).1 hc₀Q2).2 e he |>.symm.symm
  rw [Subgroup.inv_mem_iff, hd.s56_mem_centralizer_A_iff]
  constructor
  · rintro ⟨-, ht⟩
    have h1 : c₀ * d.t * c₀⁻¹ = d.t := by rw [ht]; group
    rw [hc₀, h1] at hct
    exact mul_left_cancel (a := d.t) (by rw [mul_one]; exact hct.symm.trans (by rfl) |>.symm.symm)
  · intro hb1
    refine ⟨hc₀E, ?_⟩
    rw [hb1, mul_one] at hct
    calc c₀ * d.t = (c₀ * d.t * c₀⁻¹) * c₀ := by group
      _ = d.t * c₀ := by rw [hc₀, hct]

theorem Hyp.s56_eps_mem_F_of_mem_N (hd : d.Hyp) {q : G} (hqM : q ∈ d.M) (hqN : q ∈ d.N) :
    d.s56Eps q ∈ d.F := by
  have htB : d.t ∈ d.B := mem_sup_right (mem_zpowers _)
  have h1 : q * d.t * q⁻¹ ∈ d.B := (mem_normalizer_iff.1 hqN _).1 htB
  rw [hd.s56_conj_t q] at h1
  have h2 : d.s56Eps q ∈ d.B := by
    have := mul_mem htB h1
    rwa [← mul_assoc, hd.t_mul_self, one_mul] at this
  exact hd.s56_E_inf_B (hd.s56_eps_mem_E hqM) h2

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
