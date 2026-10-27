module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56SixTwo
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Sum

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_Q2_sq_mem_C (hd : d.Hyp) {m : G} (hm : m ∈ d.s56Q2) :
    m * m ∈ centralizer (d.A : Set G) := by
  obtain ⟨hmM, hmE⟩ := (s56_mem_Q2_iff).1 hm
  rw [hd.s56_mem_centralizer_A_iff]
  refine ⟨fun e he => ?_, ?_⟩
  · calc e * (m * m) = (e * m) * m := by group
      _ = (m * e) * m := by rw [hmE e he]
      _ = m * (e * m) := by group
      _ = m * (m * e) := by rw [hmE e he]
      _ = m * m * e := by group
  · have hε := hd.s56_conj_t m
    have hεE := hd.s56_eps_mem_E hmM
    have h0 : m * d.s56Eps m = d.s56Eps m * m := (hmE _ hεE).symm
    have hε2 := hd.s56_E_sq hεE
    have hmt : m * d.t = d.t * d.s56Eps m * m := by
      calc m * d.t = (m * d.t * m⁻¹) * m := by group
        _ = d.t * d.s56Eps m * m := by rw [hε]
    calc m * m * d.t = m * (m * d.t) := by group
      _ = m * (d.t * d.s56Eps m * m) := by rw [hmt]
      _ = (m * d.t) * d.s56Eps m * m := by group
      _ = d.t * d.s56Eps m * m * d.s56Eps m * m := by rw [hmt]
      _ = d.t * d.s56Eps m * (m * d.s56Eps m) * m := by group
      _ = d.t * d.s56Eps m * (d.s56Eps m * m) * m := by rw [h0]
      _ = d.t * (d.s56Eps m * d.s56Eps m) * (m * m) := by group
      _ = d.t * (m * m) := by rw [hε2, mul_one]

theorem Hyp.s56_pv7_not_mem_E (hd : d.Hyp) : d.pv 7 ∉ d.E := by
  intro h
  have hc := hd.s56_E_comm h (s56_pv8_mem_E d)
  have h1 := s56_pv7_conj_pv8 d
  rw [hc, mul_assoc, mul_inv_cancel, mul_one] at h1
  exact hd.s56_z_ne_one (mul_eq_left.1 h1.symm)

theorem Hyp.s56_N_conj_F (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G} (hm : m ∈ d.N) {f : G}
    (hf : f ∈ d.F) : m * f * m⁻¹ ∈ d.F := by
  obtain ⟨-, hnorm, -⟩ := hd.thm51 h49 (D := d.B) (Or.inr rfl)
  have hfB : f ∈ d.B := (show d.F ≤ d.B from le_sup_left) hf
  have hm' := hnorm hm
  have hf' : f ∈ (d.B ⊓ d.L : Subgroup G) := mem_inf.2 ⟨hfB, s56_F_le_L d hf⟩
  have := (mem_normalizer_iff.1 hm' f).1 hf'
  exact hd.s56_B_inf_L (mem_inf.1 this).1 (mem_inf.1 this).2

theorem Hyp.s56_pv7_conj_N (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G} (hmM : m ∈ d.M)
    (hmN : m ∈ d.N) : d.pv 7 * (m * d.pv 7 * m⁻¹) ∈ d.E := by
  have hF : m * d.pv 7 * m⁻¹ ∈ d.F := hd.s56_N_conj_F h49 hmN hd.s56_pv7_mem_F
  rcases Hyp.s56_F_cases d hF with h | h
  · exfalso
    apply hd.s56_pv7_not_mem_E
    have h2 := (mem_normalizer_iff.1 (hd.s56_ME (inv_mem hmM)) _).1 h
    have e : m⁻¹ * (m * d.pv 7 * m⁻¹) * m⁻¹⁻¹ = d.pv 7 := by group
    rwa [e] at h2
  · exact h

theorem Hyp.s56_sq_comm_pv7 (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G} (hm : m ∈ d.s56Q2)
    (hmN : m ∈ d.N) : d.pv 7 * (m * m) = (m * m) * d.pv 7 := by
  obtain ⟨hmM, hmE⟩ := (s56_mem_Q2_iff).1 hm
  have he₁ := hd.s56_pv7_conj_N h49 hmM hmN
  set e₁ := d.pv 7 * (m * d.pv 7 * m⁻¹) with he₁def
  have hv := s56_pv7_inv d
  have hvv := s56_pv7_mul_self d
  have hc : m * d.pv 7 * m⁻¹ = d.pv 7 * e₁ := by
    rw [he₁def, ← mul_assoc, hvv, one_mul]
  have hee := hd.s56_E_sq he₁
  have hme : m * e₁ * m⁻¹ = e₁ := by
    rw [← hmE e₁ he₁]; group
  have h1 : m * m * d.pv 7 * (m * m)⁻¹ = d.pv 7 := by
    calc m * m * d.pv 7 * (m * m)⁻¹ = m * (m * d.pv 7 * m⁻¹) * m⁻¹ := by group
      _ = m * (d.pv 7 * e₁) * m⁻¹ := by rw [hc]
      _ = (m * d.pv 7 * m⁻¹) * (m * e₁ * m⁻¹) := by group
      _ = (d.pv 7 * e₁) * e₁ := by rw [hc, hme]
      _ = d.pv 7 * (e₁ * e₁) := by group
      _ = d.pv 7 := by rw [hee, mul_one]
  have h2 : (m * m) * d.pv 7 = d.pv 7 * (m * m) := by
    calc (m * m) * d.pv 7 = (m * m * d.pv 7 * (m * m)⁻¹) * (m * m) := by group
      _ = d.pv 7 * (m * m) := by rw [h1]
  exact h2.symm

theorem Hyp.s56_C_sq_mem_E (hd : d.Hyp) {c : G} (hc : c ∈ centralizer (d.A : Set G)) :
    c * c ∈ d.E := by
  have hAA : ∀ a ∈ d.A, a * a = 1 := fun a ha => by
    have := hd.A_facts.2.2.1.2 a ha
    simpa [pow_two] using this
  rcases hd.s56_C_cases with hCA | ⟨y, hyy, hCy, hyA', hyx, hyA, hyv, hcov, hyt⟩
  · rw [hCA] at hc
    rw [hAA c hc]; exact one_mem _
  · rcases hcov c hc with hcA | ⟨a, ha, rfl⟩
    · rw [hAA c hcA]; exact one_mem _
    · have hya := hyA' a ha
      have e : y * a * (y * a) = d.z := by
        calc y * a * (y * a) = y * (a * y) * a := by group
          _ = y * (y * a) * a := by rw [← hya]
          _ = (y * y) * (a * a) := by group
          _ = d.z := by rw [hyy, hAA a ha, mul_one]
      rw [e]; exact hd.s56_z_mem_E

theorem Hyp.s56_pv7_comm_C (hd : d.Hyp) {c : G} (hc : c ∈ centralizer (d.A : Set G))
    (h : d.pv 7 * c = c * d.pv 7) : c ∈ d.A := by
  have hAA : ∀ a ∈ d.A, a * a = 1 := fun a ha => by
    have := hd.A_facts.2.2.1.2 a ha
    simpa [pow_two] using this
  have hAcomm : ∀ a ∈ d.A, ∀ b ∈ d.A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rcases hd.s56_C_cases with hCA | ⟨y, hyy, hCy, hyA', hyx, hyA, hyv, hcov, hyt⟩
  · rw [hCA] at hc; exact hc
  · rcases hcov c hc with hcA | ⟨a, ha, rfl⟩
    · exact hcA
    · exfalso
      have hu := s56_pv11_mem_E d
      have huA := s56_E_le_A d hu
      have hw := hd.s56_pv7_conj_A ha
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
      have hya := hyA' a ha
      have hyu := hyA' _ huA
      have hyw := hyA' _ hwA
      have h1 : d.pv 11 * y * (w * a) = y * a := by
        have e1 : d.pv 7 * (y * a) * (d.pv 7)⁻¹ = d.pv 11 * y * (w * a) := by
          rw [show d.pv 7 * (y * a) * (d.pv 7)⁻¹ =
            (d.pv 7 * y * (d.pv 7)⁻¹) * (d.pv 7 * a * (d.pv 7)⁻¹) by group, hvy, hvav]
        rw [← e1]
        calc d.pv 7 * (y * a) * (d.pv 7)⁻¹ = (y * a) * d.pv 7 * (d.pv 7)⁻¹ := by rw [h]
          _ = y * a := by group
      have h2 : d.pv 11 * w = 1 := by
        have hcomm1 : d.pv 11 * y * (w * a) = y * (d.pv 11 * w * a) := by
          calc d.pv 11 * y * (w * a) = (d.pv 11 * y) * (w * a) := rfl
            _ = (y * d.pv 11) * (w * a) := by rw [← hyu]
            _ = y * (d.pv 11 * w * a) := by group
        rw [hcomm1] at h1
        have h3 : d.pv 11 * w * a = a := mul_left_cancel h1
        have h4 : d.pv 11 * w * a = 1 * a := by rw [one_mul]; exact h3
        exact mul_right_cancel h4
      apply hd.s56_pv11_not_mem
      have : d.pv 11 = w⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [this]
      exact inv_mem hw

theorem Hyp.s56_sq_mem_E_of_mem_N (h49 : d.Thm49Statement) (hd : d.Hyp) {m : G}
    (hm : m ∈ d.s56Q2) (hmN : m ∈ d.N) : m * m ∈ d.E := by
  have hC := hd.s56_Q2_sq_mem_C hm
  have hA : m * m ∈ d.A := hd.s56_pv7_comm_C hC (hd.s56_sq_comm_pv7 h49 hm hmN)
  rcases (hd.s56_mem_A_iff).1 hA with h | h
  · exact h
  · exfalso
    obtain ⟨hmM, hmE⟩ := (s56_mem_Q2_iff).1 hm
    have h1 := hmE _ h
    have hmt : m * d.t = d.t * m := by
      have e : m * d.t * (m * m) = d.t * m * (m * m) := by
        calc m * d.t * (m * m) = m * (d.t * (m * m)) := by group
          _ = (d.t * (m * m)) * m := h1.symm
          _ = d.t * m * (m * m) := by group
      exact mul_right_cancel e
    have hmC : m ∈ centralizer (d.A : Set G) :=
      (hd.s56_mem_centralizer_A_iff).2 ⟨fun e he => hmE e he, hmt⟩
    have hsq := hd.s56_C_sq_mem_E hmC
    apply hd.t_not_mem
    have e : d.t = (d.t * (m * m)) * (m * m)⁻¹ := by group
    rw [e]
    exact mul_mem (s56_E_le_L d h) (inv_mem (s56_E_le_L d hsq))

theorem Hyp.s56_Q2_le_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Q2 ≤ d.s56Q0 :=
  (hd.s56_structure_M h49).2.2.2.2.2.2

theorem Hyp.s56_Q2_conj_mem (hd : d.Hyp) {g q : G} (hg : g ∈ d.M) (hq : q ∈ d.s56Q2) :
    g * q * g⁻¹ ∈ d.s56Q2 := by
  obtain ⟨hqM, hqE⟩ := (s56_mem_Q2_iff).1 hq
  refine (s56_mem_Q2_iff).2 ⟨mul_mem (mul_mem hg hqM) (inv_mem hg), fun e he => ?_⟩
  have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hd.s56_ME (inv_mem hg)) e).1 he
  have h := hqE _ he'
  have h' : g⁻¹ * e * g * q = q * (g⁻¹ * e * g) := by simpa using h
  calc e * (g * q * g⁻¹) = g * ((g⁻¹ * e * g) * q) * g⁻¹ := by group
    _ = g * (q * (g⁻¹ * e * g)) * g⁻¹ := by rw [h']
    _ = g * q * g⁻¹ * e := by group

theorem Hyp.s56_Q2_sq_mem_E_all (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∀ m ∈ d.s56Q2, m * m ∈ d.E := by
  intro m hm
  obtain ⟨hmM, hmE⟩ := (s56_mem_Q2_iff).1 hm
  have hεE := hd.s56_eps_mem_E hmM
  have hxM := hd.s56_x5_mem_M
  have hx5 : d.x₅ ^ 5 = 1 := by rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _
  have hvM := hd.s56_pv7_mem_M
  obtain ⟨i, -, hi⟩ := S56.exists_conj_comm_of_five (E := d.E) (x := d.x₅) (v := d.pv 7)
    (z := d.z) hx5 (hd.s56_ME hxM) (fun a ha b hb => hd.s56_E_comm ha hb) hd.s56_z_mem_E
    hd.s56_z_sq hd.s56_z_ne_one (hd.s56_M_comm_z hvM)
    (fun n hn hnx => (hd.s56_M_comm_zpowers hvM (hd.s56_E_cent_x5 hn hnx)).symm)
    (fun e he => by
      have h := hd.s56_pv7_conj_E he
      rcases hd.s56_mem_zpowers_z h with h1 | h1
      · left
        calc d.pv 7 * e * (d.pv 7)⁻¹ = (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * e := by group
          _ = e := by rw [h1, one_mul]
      · right
        calc d.pv 7 * e * (d.pv 7)⁻¹ = (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹) * e := by group
          _ = d.z * e := by rw [h1]) hεE
  set g := (d.x₅ ^ i)⁻¹ with hg
  have hgM : g ∈ d.M := inv_mem (pow_mem hxM i)
  have hgt : g * d.t = d.t * g := by
    have h1 : d.x₅ ^ i * d.t = d.t * d.x₅ ^ i := (Commute.pow_left (show Commute d.x₅ d.t from
      hd.s56_x5_comm_t) i).eq
    rw [hg]
    exact ((show Commute (d.x₅ ^ i) d.t from h1).inv_left).eq
  set m' := g * m * g⁻¹ with hm'
  have hm'Q2 : m' ∈ d.s56Q2 := hd.s56_Q2_conj_mem hgM hm
  have hεm' : d.s56Eps m' = g * d.s56Eps m * g⁻¹ := hd.s56_eps_conj hgt m
  have hgE : g * d.s56Eps m * g⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hd.s56_ME hgM) _).1 hεE
  have hF : d.s56Eps m' ∈ d.F := by
    rw [hεm']
    have hi' : d.pv 7 * (g * d.s56Eps m * g⁻¹) = (g * d.s56Eps m * g⁻¹) * d.pv 7 := by
      rw [hg, inv_inv]; exact hi
    exact (hd.s56_pv7_comm_iff hgE).1 hi'
  have hm'N : m' ∈ d.N :=
    (hd.s56_mem_N_iff_eps h49 (hd.s56_Q2_le_Q0 h49 hm'Q2)).2 hF
  have hsq := hd.s56_sq_mem_E_of_mem_N h49 hm'Q2 hm'N
  have e : m * m = g⁻¹ * (m' * m') * g⁻¹⁻¹ := by rw [hm']; group
  rw [e]
  exact (mem_normalizer_iff.1 (hd.s56_ME (inv_mem hgM)) _).1 hsq

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
