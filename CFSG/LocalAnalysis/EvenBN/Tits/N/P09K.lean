module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56P517
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Kappa

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

section P09K

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node09K_pv9_mem_F (d : Data G) : d.pv 9 ∈ d.F :=
  Data.mem_liftSub.2 ⟨_, Model.parrottV_mem_parrottF (by simp), Model.parrottF_le_titsD
    (Model.parrottV_mem_parrottF (by simp)), rfl⟩

theorem node09K_pv9_mem_E (d : Data G) : d.pv 9 ∈ d.E := by
  have h : Model.parrottV 9 ∈ Model.hatE :=
    Model.parrottU_eight_le_hatE (subset_closure ⟨9, ⟨by norm_num, by norm_num⟩, rfl⟩)
  exact Data.mem_liftSub.2 ⟨_, h, Data.s56_hatE_le_titsD h, rfl⟩

theorem node09K_pv9_not_mem_U10 (d : Data G) : d.pv 9 ∉ d.s56U10 := by
  intro h
  rw [Data.s56U10_eq_liftSub] at h
  have h9 : Model.parrottV 9 ∈ titsD := Data.s56_parrottV_mem_titsD (i := 9) (by omega)
  have h' := (Data.s56_lift_mem_liftSub_iff
    (Model.parrottU_ten_le_parrottF.trans Model.parrottF_le_titsD) h9).1 h
  obtain ⟨hs9, -⟩ := Model.parrottF_short_nine
  have hmem : Model.parrottV 9 ∈ {f | ∃ n ∈ titsN, n * Model.parrottV 9 * n⁻¹ = f} :=
    ⟨1, one_mem _, by group⟩
  rw [← hs9] at hmem
  exact hmem.2.2 h'

@[expose] noncomputable def node09Z (h49 : d.Thm49Statement) (hd : d.Hyp) : Subgroup G where
  carrier := {p | p ∈ d.s56P10 ∧ ∀ f ∈ d.F, p * f * p⁻¹ * f⁻¹ ∈ d.s56U11}
  mul_mem' := by
    rintro g h ⟨hgP, hg⟩ ⟨hhP, hh⟩
    refine ⟨mul_mem hgP hhP, fun f hf => ?_⟩
    have e : g * h * f * (g * h)⁻¹ * f⁻¹ =
        g * (h * f * h⁻¹ * f⁻¹) * g⁻¹ * (g * f * g⁻¹ * f⁻¹) := by group
    rw [e]
    exact mul_mem (hd.s56_N_conj_U11 h49 (d.s56_P0_le_N (d.s56_P10_le_P0 hgP)) (hh f hf))
      (hg f hf)
  one_mem' := ⟨one_mem _, fun f _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgP, hg⟩
    refine ⟨inv_mem hgP, fun f hf => ?_⟩
    have e : g⁻¹ * f * g⁻¹⁻¹ * f⁻¹ = g⁻¹ * (g * f * g⁻¹ * f⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact hd.s56_N_conj_U11 h49 (inv_mem (d.s56_P0_le_N (d.s56_P10_le_P0 hgP)))
      (inv_mem (hg f hf))

theorem node09Z_conj (h49 : d.Thm49Statement) (hd : d.Hyp) {n z : G} (hn : n ∈ d.N)
    (hz : z ∈ node09Z h49 hd) : n * z * n⁻¹ ∈ node09Z h49 hd := by
  obtain ⟨hzP, hz'⟩ := hz
  refine ⟨hd.s56_N_conj_P10 h49 hn hzP, fun f hf => ?_⟩
  have hf' : n⁻¹ * f * n⁻¹⁻¹ ∈ d.F := hd.s56_N_conj_F h49 (inv_mem hn) hf
  have h := hd.s56_N_conj_U11 h49 hn (hz' _ hf')
  have e : n * (z * (n⁻¹ * f * n⁻¹⁻¹) * z⁻¹ * (n⁻¹ * f * n⁻¹⁻¹)⁻¹) * n⁻¹ =
      n * z * n⁻¹ * f * (n * z * n⁻¹)⁻¹ * f⁻¹ := by group
  rwa [e] at h

theorem node09K_mem_Z_of_eps (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {p : G} (hp : p ∈ d.s56P10) (hε : d.s56Eps p ∈ d.s56U10) : p ∈ node09Z h49 hd :=
  ⟨hp, hd.s56_P10_comm_F_of_comm_B h49 hz hp
    (hd.s56_comm_B_le_U10_of_eps h49 (d.s56_P10_le_P0 hp) hε)⟩

theorem node09K_eps_mul (h49 : d.Thm49Statement) (hd : d.Hyp) {p q : G} (hp : p ∈ d.s56P0)
    (hq : q ∈ d.N) : ∃ w ∈ d.s56U10, d.s56Eps (p * q) = w * (d.s56Eps p * d.s56Eps q) := by
  have hpF := hd.s56_eps_mem_F_of_N h49 (d.s56_P0_le_N hp)
  have hqF := hd.s56_eps_mem_F_of_N h49 hq
  have hw := hd.s56_P0_comm_F_le_U10 h49 hp hqF
  refine ⟨p * d.s56Eps q * p⁻¹ * (d.s56Eps q)⁻¹, hw, ?_⟩
  have hc : d.s56Eps p * (p * d.s56Eps q * p⁻¹ * (d.s56Eps q)⁻¹) =
      (p * d.s56Eps q * p⁻¹ * (d.s56Eps q)⁻¹) * d.s56Eps p :=
    hd.s56_F_comm hpF (d.s56_U10_le_F hw)
  rw [hd.s56_eps_mul]
  calc d.s56Eps p * (p * d.s56Eps q * p⁻¹)
      = (d.s56Eps p * (p * d.s56Eps q * p⁻¹ * (d.s56Eps q)⁻¹)) * d.s56Eps q := by group
    _ = ((p * d.s56Eps q * p⁻¹ * (d.s56Eps q)⁻¹) * d.s56Eps p) * d.s56Eps q := by rw [hc]
    _ = _ := by group

@[expose] noncomputable def node09T (h49 : d.Thm49Statement) (hd : d.Hyp) : Subgroup G where
  carrier := {f | f ∈ d.F ∧ ∃ z ∈ node09Z h49 hd, ∃ u ∈ d.s56U10, d.s56Eps z = u * f}
  mul_mem' := by
    rintro f f' ⟨hf, z, hz, u, hu, hzf⟩ ⟨hf', z', hz', u', hu', hzf'⟩
    refine ⟨mul_mem hf hf', z * z', mul_mem hz hz', ?_⟩
    obtain ⟨w, hw, hzz⟩ := node09K_eps_mul h49 hd (d.s56_P10_le_P0 hz.1)
      (d.s56_P0_le_N (d.s56_P10_le_P0 hz'.1))
    refine ⟨w * u * u', mul_mem (mul_mem hw hu) hu', ?_⟩
    have hc : f * u' = u' * f := hd.s56_F_comm hf (d.s56_U10_le_F hu')
    rw [hzz, hzf, hzf']
    calc w * (u * f * (u' * f')) = w * u * (f * u') * f' := by group
      _ = w * u * (u' * f) * f' := by rw [hc]
      _ = _ := by group
  one_mem' := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by rw [hd.s56_eps_one, one_mul]⟩
  inv_mem' := by
    rintro f ⟨hf, hfz⟩
    have h : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hd.s56_F_sq hf)
    rw [h]
    exact ⟨hf, hfz⟩

theorem node09K_eq_F_of_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {W : Subgroup G}
    (hWF : W ≤ d.F) (hUW : d.s56U10 ≤ W) {a : G} (haF : a ∈ d.F) (haU : a ∉ d.s56U10)
    (haW : a ∈ W) (hbW : d.s56Y * a * d.s56Y⁻¹ ∈ W) : W = d.F := by
  obtain ⟨hyNC, -, -, -, -, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hbU : d.s56Y * a * d.s56Y⁻¹ ∉ d.s56U10 := fun h => haU (by
    have := hd.s56_N_conj_U10 h49 (inv_mem hyN) h
    simpa [mul_assoc] using this)
  have hcomm : d.s56Y * a * d.s56Y⁻¹ * a⁻¹ ∉ d.s56U10 := Data.s56_Y_comm_not_mem haF haU
  have hd32 : Nat.card W ∣ 32 := by
    have := Subgroup.card_dvd_of_le hWF
    rwa [hd.B_facts.1] at this
  have hd8 : 8 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hUW
    rwa [Data.s56_card_U10] at this
  have hne8 : Nat.card W ≠ 8 := fun h8 => haU (by
    have := Subgroup.eq_of_le_of_card_ge hUW (by rw [h8, Data.s56_card_U10])
    rw [this]; exact haW)
  have hne16 : Nat.card W ≠ 16 := fun h16 => hcomm
    (mul_inv_mem_of_card_eq_two_mul hUW (by rw [h16, Data.s56_card_U10]) hbW haW hbU haU)
  have h32 : Nat.card W = 32 := by
    obtain ⟨m, hm⟩ := hd8
    rw [hm] at hd32 hne8 hne16 ⊢
    have hm4 : m ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) (by simpa using hd32)
    have hle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hWF (by rw [h32, hd.B_facts.1])

theorem node09K_exists_Z_pv9 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) : ∃ x ∈ node09Z h49 hd, d.s56Eps x = d.pv 9 := by
  obtain ⟨x, hxV, hxε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 9) (node09K_pv9_mem_E d)
  have hxQ0 : x ∈ d.s56Q0 := hd.s56_Q_le_Q0 hxV.1
  have hxN : x ∈ d.N :=
    (hd.s56_mem_N_iff_eps h49 hxQ0).2 (by rw [hxε]; exact node09K_pv9_mem_F d)
  have hxP0 : x ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hxV.2 hxN
  have hxP10 : x ∈ d.s56P10 :=
    (hd.s56_mem_P10_iff h49 hxP0).2 (Data.s56_V_comm_E hxV hd.s56_pv10_mem_E)
  exact ⟨x, ⟨hxP10, hκ x (mem_inf.2 ⟨hxV, hxN⟩)⟩, hxε⟩

theorem node09T_eq_F (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) : node09T h49 hd = d.F := by
  obtain ⟨x, hxZ, hxε⟩ := node09K_exists_Z_pv9 h49 hd hz hκ
  obtain ⟨hyNC, -, -, -, -, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hyt : d.s56Y * d.t = d.t * d.s56Y := mem_centralizer_singleton_iff.1 (mem_inf.1 hyNC).2
  refine node09K_eq_F_of_mem h49 hd (fun f hf => hf.1) (fun u hu => ⟨d.s56_U10_le_F hu, 1,
    one_mem _, u⁻¹, inv_mem hu, by rw [hd.s56_eps_one, inv_mul_cancel]⟩)
    (node09K_pv9_mem_F d) (node09K_pv9_not_mem_U10 d)
    ⟨node09K_pv9_mem_F d, x, hxZ, 1, one_mem _, by rw [hxε, one_mul]⟩ ?_
  refine ⟨hd.s56_N_conj_F h49 hyN (node09K_pv9_mem_F d), d.s56Y * x * d.s56Y⁻¹,
    node09Z_conj h49 hd hyN hxZ, 1, one_mem _, ?_⟩
  rw [hd.s56_eps_conj hyt, hxε, one_mul]

theorem node09_518 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) : ⁅d.s56P10, d.F⁆ ≤ d.s56U11 := by
  have hT := node09T_eq_F h49 hd hz hκ
  refine Subgroup.commutator_le.2 fun p hp f hf => ?_
  rw [commutatorElement_def]
  have hpN : p ∈ d.N := d.s56_P0_le_N (d.s56_P10_le_P0 hp)
  have hεF : d.s56Eps p ∈ d.F := hd.s56_eps_mem_F_of_N h49 hpN
  rw [← hT] at hεF
  obtain ⟨-, z, hzZ, u, hu, hzε⟩ := hεF
  have hzP : z ∈ d.s56P10 := hzZ.1
  obtain ⟨w, hw, hzp⟩ := node09K_eps_mul h49 hd (d.s56_P10_le_P0 hzP) hpN
  have hεp := hd.s56_F_sq (hd.s56_eps_mem_F_of_N h49 hpN)
  have hεzp : d.s56Eps (z * p) ∈ d.s56U10 := by
    rw [hzp, hzε, mul_assoc u, hεp, mul_one]
    exact mul_mem hw hu
  have hzpZ : z * p ∈ node09Z h49 hd :=
    node09K_mem_Z_of_eps h49 hd hz (mul_mem hzP hp) hεzp
  have hpZ : p ∈ node09Z h49 hd := by
    have := mul_mem (inv_mem hzZ) hzpZ
    rwa [inv_mul_cancel_left] at this
  exact hpZ.2 f hf

end P09K

end CFSG.LocalAnalysis.EvenBN.Tits.N
