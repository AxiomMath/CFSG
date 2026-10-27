module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56P11
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_Pe11_le_P11 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Pe11 ≤ d.s56P11 := by
  refine Subgroup.commutator_le.2 fun p hp n hn => ?_
  rw [commutatorElement_def]
  have e : p * n * p⁻¹ * n⁻¹ = p * (n * p⁻¹ * n⁻¹) := by group
  rw [e]
  exact mul_mem hp (hd.s56_N_conj_P11 h49 hn (inv_mem hp))

theorem Hyp.s56_Pe11_le_P (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Pe11 ≤ d.s56P :=
  (hd.s56_Pe11_le_P11 h49).trans (s56_P11_le_P d)

theorem Hyp.s56_eps_Pe11_surj (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ y : G}
    (hz : d.S56Z0 z₀) (hy : y ∈ d.N) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∀ a ∈ d.s56U11, ∃ w ∈ d.s56Pe11, d.s56Eps w = a := by
  obtain ⟨hα, -, -, hα2, hall⟩ := hd.s56_y_orbit h49 hy hy3 hy1
  have hz0P11 := hd.s56_z0_mem_P11 h49 hz
  have hz0P := s56_P11_le_P d hz0P11
  have hyy : y * y ∈ d.N := mul_mem hy hy
  have haF : y * d.z * y⁻¹ ∈ d.F := s56_U11_le_F d hα
  have haa : (y * d.z * y⁻¹) * (y * d.z * y⁻¹) = 1 := hd.s56_F_sq haF
  have hg : z₀ * (y * z₀⁻¹ * y⁻¹) ∈ d.s56Pe11 := by
    have h := Subgroup.commutator_mem_commutator hz0P11 hy
    rwa [commutatorElement_def, show z₀ * y * z₀⁻¹ * y⁻¹ = z₀ * (y * z₀⁻¹ * y⁻¹) by group] at h
  have hg' : z₀ * (y * y * z₀⁻¹ * (y * y)⁻¹) ∈ d.s56Pe11 := by
    have h := Subgroup.commutator_mem_commutator hz0P11 hyy
    rwa [commutatorElement_def,
      show z₀ * (y * y) * z₀⁻¹ * (y * y)⁻¹ = z₀ * (y * y * z₀⁻¹ * (y * y)⁻¹) by group] at h
  have hεg : d.s56Eps (z₀ * (y * z₀⁻¹ * y⁻¹)) = d.z * (y * d.z * y⁻¹) := by
    rw [hd.s56_eps_mul_P h49 hz0P (hd.s56_N_conj_P h49 hy (inv_mem hz0P)),
      hd.s56_eps_conj_N h49 hy (inv_mem hz0P), hd.s56_eps_inv_P h49 hz0P, hz.eps]
  have hεg' : d.s56Eps (z₀ * (y * y * z₀⁻¹ * (y * y)⁻¹)) = y * d.z * y⁻¹ := by
    rw [hd.s56_eps_mul_P h49 hz0P (hd.s56_N_conj_P h49 hyy (inv_mem hz0P)),
      hd.s56_eps_conj_N h49 hyy (inv_mem hz0P), hd.s56_eps_inv_P h49 hz0P, hz.eps]
    have e : y * y * d.z * (y * y)⁻¹ = y * (y * d.z * y⁻¹) * y⁻¹ := by group
    rw [e, hα2, ← mul_assoc, hd.s56_z_sq, one_mul]
  intro a ha
  rcases hall a ha with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, hd.s56_eps_one⟩
  · refine ⟨_, mul_mem hg hg', ?_⟩
    rw [hd.s56_eps_mul_P h49 (s56_Pe11_le_P h49 hd hg) (s56_Pe11_le_P h49 hd hg'), hεg, hεg',
      mul_assoc, haa, mul_one]
  · exact ⟨_, hg', hεg'⟩
  · exact ⟨_, hg, hεg⟩

theorem Hyp.s56_eps_Pe11_surj_Y (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) : ∀ a ∈ d.s56U11, ∃ w ∈ d.s56Pe11, d.s56Eps w = a := by
  obtain ⟨hyNC, -, hy3, hy1, -, -, -⟩ := hd.s56_Y_facts
  exact hd.s56_eps_Pe11_surj h49 hz (mem_inf.1 hyNC).1 hy3 hy1

theorem s56_P_le_P10 (d : Data G) : d.s56P ≤ d.s56P10 := by
  rw [s56P_def, s56P10_def]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (s56_U10_le_F d))

theorem Hyp.s56_comm_t_of_eps_eq_one (hd : d.Hyp) {c : G} (h : d.s56Eps c = 1) :
    c * d.t = d.t * c := by
  have h1 := hd.s56_conj_t c
  rw [h, mul_one] at h1
  calc c * d.t = c * d.t * c⁻¹ * c := by group
    _ = d.t * c := by rw [h1]

theorem Hyp.s56_comm_B_of_eps_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {p : G} (hp : p ∈ d.s56P10) (hε : d.s56Eps p ∈ d.s56U11) :
    ∀ b ∈ d.B, p * b * p⁻¹ * b⁻¹ ∈ d.s56U11 := by
  intro b hb
  have hU := hd.s56_eps_Pe11_surj_Y h49 hz
  obtain ⟨w, hw, hwε⟩ := hU _ hε
  have hwP11 := hd.s56_Pe11_le_P11 h49 hw
  have hwP : w ∈ d.s56P := s56_P11_le_P d hwP11
  have hwN : w ∈ d.N := s56_P_le_N d hwP
  have hpN : p ∈ d.N := s56_P0_le_N d (s56_P10_le_P0 d hp)
  have hεF : d.s56Eps p ∈ d.F := hd.s56_eps_mem_F_of_N h49 hpN
  have hεc : d.s56Eps (w⁻¹ * p) = 1 := by
    rw [hd.s56_eps_mul, hd.s56_eps_inv_P h49 hwP, hwε, s56_P_conj_F d (inv_mem hwP) hεF]
    exact hd.s56_F_sq hεF
  have hct : w⁻¹ * p * d.t = d.t * (w⁻¹ * p) := hd.s56_comm_t_of_eps_eq_one hεc
  have hc := hd.s56_comm_P10_CNt_B h49 (mul_mem (inv_mem (s56_P_le_P10 d hwP)) hp)
    (mem_centralizer_singleton_iff.2 hct) hb
  have e : p * b * p⁻¹ * b⁻¹ =
      w * (w⁻¹ * p * b * (w⁻¹ * p)⁻¹ * b⁻¹) * w⁻¹ * (w * b * w⁻¹ * b⁻¹) := by group
  rw [e]
  exact mul_mem (hd.s56_N_conj_U11 h49 hwN hc) (hwP11.2.2 b hb)

theorem s56_P10_conj_U10 (d : Data G) {q u : G} (hq : q ∈ d.s56P10) (hu : u ∈ d.s56U10) :
    q * u * q⁻¹ = u := by
  rw [s56P10_def] at hq
  have h : u * q = q * u := mem_centralizer_iff.1 (mem_inf.1 hq).2 u hu
  rw [← h]
  group

theorem Hyp.s56_comm_t_eq_eps (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} (hp : p ∈ d.N) :
    p * d.t * p⁻¹ * d.t⁻¹ = d.s56Eps p := by
  have hεF := hd.s56_eps_mem_F_of_N h49 hp
  have hεt : d.s56Eps p * d.t = d.t * d.s56Eps p := hd.L_comm_t (s56_F_le_L d hεF)
  rw [hd.s56_conj_t p]
  calc d.t * d.s56Eps p * d.t⁻¹ = (d.s56Eps p * d.t) * d.t⁻¹ := by rw [hεt]
    _ = d.s56Eps p := by group

theorem Hyp.s56_eps_mem_U10_of_comm_B (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G}
    (hp : p ∈ d.N) (hpB : ∀ b ∈ d.B, p * b * p⁻¹ * b⁻¹ ∈ d.s56U10) :
    d.s56Eps p ∈ d.s56U10 := by
  have h := hpB d.t (s56_t_mem_B d)
  rwa [hd.s56_comm_t_eq_eps h49 hp] at h

theorem Hyp.s56_comm_B_le_U10_of_eps (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G}
    (hp : p ∈ d.s56P0) (hε : d.s56Eps p ∈ d.s56U10) :
    ∀ b ∈ d.B, p * b * p⁻¹ * b⁻¹ ∈ d.s56U10 := by
  intro b hb
  rcases (hd.s56_mem_B_iff).1 hb with hf | hf
  · exact hd.s56_P0_comm_F_le_U10 h49 hp hf
  · obtain ⟨f, hfdef⟩ : ∃ f, f = d.t * b := ⟨_, rfl⟩
    rw [← hfdef] at hf
    have hb' : b = d.t * f := by rw [hfdef, ← mul_assoc, hd.t_mul_self, one_mul]
    have hw := hd.s56_P0_comm_F_le_U10 h49 hp hf
    have hwt : (p * f * p⁻¹ * f⁻¹) * d.t = d.t * (p * f * p⁻¹ * f⁻¹) :=
      hd.L_comm_t (s56_F_le_L d (s56_U10_le_F d hw))
    have e : p * (d.t * f) * p⁻¹ * (d.t * f)⁻¹ =
        (p * d.t * p⁻¹ * d.t⁻¹) * (p * f * p⁻¹ * f⁻¹) := by
      calc p * (d.t * f) * p⁻¹ * (d.t * f)⁻¹
          = (p * d.t * p⁻¹ * d.t⁻¹) * (d.t * (p * f * p⁻¹ * f⁻¹) * d.t⁻¹) := by group
        _ = _ := by rw [← hwt]; group
    rw [hb', e, hd.s56_comm_t_eq_eps h49 (s56_P0_le_N d hp)]
    exact mul_mem hε hw

theorem Hyp.s56_P0_comm_mul_F (h49 : d.Thm49Statement) (hd : d.Hyp) {p f f' : G}
    (hp : p ∈ d.s56P0) (hf : f ∈ d.F) (hf' : f' ∈ d.F) :
    p * (f * f') * p⁻¹ * (f * f')⁻¹ = (p * f * p⁻¹ * f⁻¹) * (p * f' * p⁻¹ * f'⁻¹) := by
  have hw := s56_U10_le_F d (hd.s56_P0_comm_F_le_U10 h49 hp hf')
  have hc : f * (p * f' * p⁻¹ * f'⁻¹) = (p * f' * p⁻¹ * f'⁻¹) * f := hd.s56_F_comm hf hw
  calc p * (f * f') * p⁻¹ * (f * f')⁻¹
      = (p * f * p⁻¹ * f⁻¹) * (f * (p * f' * p⁻¹ * f'⁻¹) * f⁻¹) := by group
    _ = (p * f * p⁻¹ * f⁻¹) * (p * f' * p⁻¹ * f'⁻¹) := by rw [hc]; group

theorem Hyp.s56_eps_mul_inv_P10 (hd : d.Hyp) {g h : G} (hg : g ∈ d.s56P10) (hh : h ∈ d.s56P10)
    (hεh : d.s56Eps h ∈ d.s56U10) : d.s56Eps (g * h⁻¹) = d.s56Eps g * (d.s56Eps h)⁻¹ := by
  have h1 := hd.s56_eps_mul h h⁻¹
  rw [mul_inv_cancel, hd.s56_eps_one] at h1
  have h2 : h * d.s56Eps h⁻¹ * h⁻¹ = (d.s56Eps h)⁻¹ :=
    (inv_eq_of_mul_eq_one_right h1.symm).symm
  have hq : g * h⁻¹ ∈ d.s56P10 := mul_mem hg (inv_mem hh)
  rw [hd.s56_eps_mul]
  congr 1
  calc g * d.s56Eps h⁻¹ * g⁻¹ = (g * h⁻¹) * (h * d.s56Eps h⁻¹ * h⁻¹) * (g * h⁻¹)⁻¹ := by group
    _ = (g * h⁻¹) * (d.s56Eps h)⁻¹ * (g * h⁻¹)⁻¹ := by rw [h2]
    _ = (d.s56Eps h)⁻¹ := s56_P10_conj_U10 d hq (inv_mem hεh)

theorem Hyp.s56_N_comm_U10_mem_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {n u : G}
    (hn : n ∈ d.N) (hnv : n * d.pv 10 = d.pv 10 * n) (hu : u ∈ d.s56U10) :
    n * u * n⁻¹ * u⁻¹ ∈ d.s56U11 := by
  rcases s56_U10_cases hu with hu | ⟨u₁, hu₁, rfl⟩
  · exact mul_mem (hd.s56_N_conj_U11 h49 hn hu) (inv_mem hu)
  · have hw : n * u₁ * n⁻¹ * u₁⁻¹ ∈ d.s56U11 :=
      mul_mem (hd.s56_N_conj_U11 h49 hn hu₁) (inv_mem hu₁)
    have hc := hd.s56_F_comm (s56_pv10_mem_F d) (s56_U11_le_F d hw)
    have hnv' : n * d.pv 10 * n⁻¹ = d.pv 10 := by rw [hnv]; group
    have e : n * (d.pv 10 * u₁) * n⁻¹ * (d.pv 10 * u₁)⁻¹ =
        d.pv 10 * (n * u₁ * n⁻¹ * u₁⁻¹) * (d.pv 10)⁻¹ := by
      calc n * (d.pv 10 * u₁) * n⁻¹ * (d.pv 10 * u₁)⁻¹
          = (n * d.pv 10 * n⁻¹) * (n * u₁ * n⁻¹ * u₁⁻¹) * (d.pv 10)⁻¹ := by group
        _ = _ := by rw [hnv']
    rw [e, hc]
    simpa using hw

theorem Hyp.s56_comm_conj_mem_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {p n f : G} (hp : p ∈ d.s56P10)
    (hεp : d.s56Eps p ∈ d.s56U10) (hn : n ∈ d.N) (hnt : n * d.t = d.t * n)
    (hnv : n * d.pv 10 = d.pv 10 * n) (hf : f ∈ d.F) :
    (p * (n * f * n⁻¹) * p⁻¹ * (n * f * n⁻¹)⁻¹) * (p * f * p⁻¹ * f⁻¹)⁻¹ ∈ d.s56U11 := by
  have hp0 : p ∈ d.s56P0 := s56_P10_le_P0 d hp
  have hn' : n⁻¹ ∈ d.N := inv_mem hn
  have hnt' : n⁻¹ * d.t = d.t * n⁻¹ := (Commute.inv_left (show Commute n d.t from hnt)).eq
  have hnv' : n⁻¹ * d.pv 10 = d.pv 10 * n⁻¹ :=
    (Commute.inv_left (show Commute n (d.pv 10) from hnv)).eq
  have hp' : n⁻¹ * p * n ∈ d.s56P10 := by
    have := hd.s56_N_conj_P10 h49 hn' hp
    rwa [inv_inv] at this
  have hq : (n⁻¹ * p * n) * p⁻¹ ∈ d.s56P10 := mul_mem hp' (inv_mem hp)
  have hεp' : d.s56Eps (n⁻¹ * p * n) = n⁻¹ * d.s56Eps p * n := by
    have := hd.s56_eps_conj hnt' p
    rwa [inv_inv] at this
  have hεq : d.s56Eps ((n⁻¹ * p * n) * p⁻¹) ∈ d.s56U11 := by
    rw [hd.s56_eps_mul_inv_P10 hp' hp hεp, hεp']
    have := hd.s56_N_comm_U10_mem_U11 h49 hn' hnv' hεp
    rwa [inv_inv] at this
  have hcomm := hd.s56_comm_B_of_eps_U11 h49 hz hq hεq f (s56_F_le_B d hf)
  have hu0 : p * f * p⁻¹ * f⁻¹ ∈ d.s56U10 := hd.s56_P0_comm_F_le_U10 h49 hp0 hf
  have hqu0 : ((n⁻¹ * p * n) * p⁻¹) * (p * f * p⁻¹ * f⁻¹) * ((n⁻¹ * p * n) * p⁻¹)⁻¹ =
      p * f * p⁻¹ * f⁻¹ := s56_P10_conj_U10 d hq hu0
  have key : p * (n * f * n⁻¹) * p⁻¹ * (n * f * n⁻¹)⁻¹ =
      (n * (p * f * p⁻¹ * f⁻¹) * n⁻¹) *
        (n * (((n⁻¹ * p * n) * p⁻¹) * f * ((n⁻¹ * p * n) * p⁻¹)⁻¹ * f⁻¹) * n⁻¹) := by
    calc p * (n * f * n⁻¹) * p⁻¹ * (n * f * n⁻¹)⁻¹
        = n * ((((n⁻¹ * p * n) * p⁻¹) * (p * f * p⁻¹ * f⁻¹) * ((n⁻¹ * p * n) * p⁻¹)⁻¹) *
            (((n⁻¹ * p * n) * p⁻¹) * f * ((n⁻¹ * p * n) * p⁻¹)⁻¹ * f⁻¹)) * n⁻¹ := by group
      _ = _ := by rw [hqu0]; group
  have hb := hd.s56_N_conj_U11 h49 hn hcomm
  have ha := hd.s56_N_comm_U10_mem_U11 h49 hn hnv hu0
  have hcF := hd.s56_F_comm (s56_U11_le_F d hb) (inv_mem (s56_U10_le_F d hu0))
  rw [key, mul_assoc, hcF, ← mul_assoc]
  exact mul_mem ha hb

theorem Hyp.s56_P10_comm_F_of_comm_B (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {p : G} (hp : p ∈ d.s56P10)
    (hpB : ∀ b ∈ d.B, p * b * p⁻¹ * b⁻¹ ∈ d.s56U10) :
    ∀ f ∈ d.F, p * f * p⁻¹ * f⁻¹ ∈ d.s56U11 := by
  intro f hf
  obtain ⟨hyNC, -, hy3, -, hy10, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hyt : d.s56Y * d.t = d.t * d.s56Y := mem_centralizer_singleton_iff.1 (mem_inf.1 hyNC).2
  have hp0 : p ∈ d.s56P0 := s56_P10_le_P0 d hp
  have hεp : d.s56Eps p ∈ d.s56U10 := hd.s56_eps_mem_U10_of_comm_B h49 (s56_P0_le_N d hp0) hpB
  have hfix : ∀ x ∈ d.F, d.s56Y * x * d.s56Y⁻¹ * x⁻¹ ∈ d.s56U10 → x ∈ d.s56U10 :=
    fun x hx h => by_contra fun hnot => s56_Y_comm_not_mem hx hnot h
  have hy3' : d.s56Y * d.s56Y * d.s56Y = 1 := by rw [← pow_three']; exact hy3
  generalize d.s56Y = y at hyN hyt hy3' hy10 hfix
  obtain ⟨f₁, hf₁def⟩ : ∃ f₁, f₁ = y * f * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨f₂, hf₂def⟩ : ∃ f₂, f₂ = y * f₁ * y⁻¹ := ⟨_, rfl⟩
  have hf₁ : f₁ ∈ d.F := hf₁def ▸ hd.s56_N_conj_F h49 hyN hf
  have hf₂ : f₂ ∈ d.F := hf₂def ▸ hd.s56_N_conj_F h49 hyN hf₁
  have hyf : y * f * y⁻¹ = f₁ := hf₁def.symm
  have hyf₁ : y * f₁ * y⁻¹ = f₂ := hf₂def.symm
  have hyf₂ : y * f₂ * y⁻¹ = f := by
    rw [hf₂def, hf₁def]
    calc y * (y * (y * f * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * f * (y * y * y)⁻¹ := by group
      _ = f := by rw [hy3']; group
  have hgF : f * f₁ * f₂ ∈ d.F := mul_mem (mul_mem hf hf₁) hf₂
  have hg : f * f₁ * f₂ ∈ d.s56U10 := by
    refine hfix _ hgF ?_
    have e : y * (f * f₁ * f₂) * y⁻¹ = f * f₁ * f₂ := by
      calc y * (f * f₁ * f₂) * y⁻¹ = (y * f * y⁻¹) * (y * f₁ * y⁻¹) * (y * f₂ * y⁻¹) := by group
        _ = f₁ * f₂ * f := by rw [hyf, hyf₁, hyf₂]
        _ = f * f₁ * f₂ := by
          rw [mul_assoc, hd.s56_F_comm hf₂ hf, ← mul_assoc, hd.s56_F_comm hf₁ hf, mul_assoc]
    rw [e, mul_inv_cancel]
    exact one_mem _
  have hpg : p * (f * f₁ * f₂) * p⁻¹ * (f * f₁ * f₂)⁻¹ = 1 := by
    rw [s56_P10_conj_U10 d hp hg]
    exact mul_inv_cancel _
  rw [hd.s56_P0_comm_mul_F h49 hp0 (mul_mem hf hf₁) hf₂,
    hd.s56_P0_comm_mul_F h49 hp0 hf hf₁] at hpg
  have hK := hd.s56_comm_conj_mem_U11 h49 hz hp hεp hyN hyt hy10 hf₁
  rw [hyf₁] at hK
  have hc2F : p * f₂ * p⁻¹ * f₂⁻¹ ∈ d.F :=
    s56_U10_le_F d (hd.s56_P0_comm_F_le_U10 h49 hp0 hf₂)
  have hc2sq := hd.s56_F_sq hc2F
  have h0 : (p * f * p⁻¹ * f⁻¹) * ((p * f₁ * p⁻¹ * f₁⁻¹) * (p * f₂ * p⁻¹ * f₂⁻¹)) = 1 := by
    rw [← mul_assoc]; exact hpg
  have hc0 : p * f * p⁻¹ * f⁻¹ = (p * f₂ * p⁻¹ * f₂⁻¹) * (p * f₁ * p⁻¹ * f₁⁻¹)⁻¹ := by
    rw [eq_inv_of_mul_eq_one_left h0, mul_inv_rev, inv_eq_of_mul_eq_one_right hc2sq]
  rw [hc0]
  exact hK

theorem Hyp.s56_pv10_mem_E (hd : d.Hyp) : d.pv 10 ∈ d.E :=
  hd.s56_vL_inter_A_le_E hd.s56_pv10_mem_Sg

theorem Hyp.s56_V_comm_pv7_mem_S (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {x : G} (hx : x ∈ d.s56V) :
    x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ d.E ⊔ zpowers z₀ := by
  have h := hd.s56_J_comm_Q2_mem h49 hz.mem_Q2 hz.eps hz.dich (s56_pv7_mem_J d) hx.2
  have e : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = (d.pv 7 * x * (d.pv 7)⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h

theorem Hyp.s56_V_comm_pv7_hom (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {x x' : G} (hx : x ∈ d.s56V) (hx' : x' ∈ d.s56V) :
    x * x' * d.pv 7 * (x * x')⁻¹ * (d.pv 7)⁻¹ =
      (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) * (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) := by
  have hS := hd.s56_V_comm_pv7_mem_S h49 hz hx
  have hS' := hd.s56_V_comm_pv7_mem_S h49 hz hx'
  have hxc : (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) * x = x * (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) :=
    hd.s56_S_comm_V h49 hz hS' hx
  have hcc : (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) * (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) =
      (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) * (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) :=
    hd.s56_S_comm_V h49 hz hS' (hd.s56_S_le_V h49 hz hS)
  calc x * x' * d.pv 7 * (x * x')⁻¹ * (d.pv 7)⁻¹
      = x * (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) * x⁻¹ * (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) := by group
    _ = (x' * d.pv 7 * x'⁻¹ * (d.pv 7)⁻¹) * (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) := by
      rw [← hxc]; group
    _ = _ := hcc

theorem Hyp.s56_V_comm_pv7_mem_zpowers (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) {x : G} (hx : x ∈ d.s56V) (hε : d.s56Eps x ∈ d.s56U11) :
    x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ ∈ zpowers d.z := by
  have hv10E := hd.s56_pv10_mem_E
  have hv7E := s56_pv7_mul_self d
  obtain ⟨x₀, hx₀V, hx₀ε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 10) hv10E
  have hx₀Q0 : x₀ ∈ d.s56Q0 := hd.s56_Q_le_Q0 hx₀V.1
  have hx₀N : x₀ ∈ d.N :=
    (hd.s56_mem_N_iff_eps h49 hx₀Q0).2 (by rw [hx₀ε]; exact s56_pv10_mem_F d)
  have hx₀P0 : x₀ ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hx₀V.2 hx₀N
  have hx₀P10 : x₀ ∈ d.s56P10 :=
    (hd.s56_mem_P10_iff h49 hx₀P0).2 (s56_V_comm_E hx₀V hv10E)
  have hx₀U10 : d.s56Eps x₀ ∈ d.s56U10 := by rw [hx₀ε]; exact s56_pv10_mem_U10 d
  have ha₀ : x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ ∈ d.s56U11 :=
    hd.s56_P10_comm_F_of_comm_B h49 hz hx₀P10
      (hd.s56_comm_B_le_U10_of_eps h49 hx₀P0 hx₀U10) (d.pv 7) hd.s56_pv7_mem_F
  obtain ⟨k, hkK, hk⟩ := hd.s56_exists_K_comm h49 hε
  have hkP0 : k ∈ d.s56P0 := hd.s56_K_le_P0 h49 hkK
  have hkC := hd.s56_K_le_CNt hkK
  have hkN : k ∈ d.N := (mem_inf.1 hkC).1
  have hkt : k * d.t = d.t * k := mem_centralizer_singleton_iff.1 (mem_inf.1 hkC).2
  have hkM : k ∈ d.M := hd.s56_CP0t_le_M hkP0 (mem_inf.1 hkC).2
  have hx₀'V : k * x₀ * k⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hkM hx₀V
  have hx₀'ε : d.s56Eps (k * x₀ * k⁻¹) = d.s56Eps x * d.pv 10 := by
    rw [hd.s56_eps_conj hkt, hx₀ε, hk]
  obtain ⟨e₀, he₀, hwe⟩ : ∃ e₀ ∈ d.E, k⁻¹ * d.pv 7 * k = d.pv 7 * e₀ := by
    have hwF : k⁻¹ * d.pv 7 * k ∈ d.F := by
      have := hd.s56_N_conj_F h49 (inv_mem hkN) hd.s56_pv7_mem_F
      rwa [inv_inv] at this
    rcases Hyp.s56_F_cases d hwF with hwE | hwE
    · exfalso
      apply hd.s56_pv7_not_mem_E
      have := (mem_normalizer_iff.1 (hd.s56_ME hkM) _).1 hwE
      have e : k * (k⁻¹ * d.pv 7 * k) * k⁻¹ = d.pv 7 := by group
      rwa [e] at this
    · refine ⟨d.pv 7 * (k⁻¹ * d.pv 7 * k), hwE, ?_⟩
      rw [← mul_assoc, hv7E, one_mul]
  have hcomm₀ : (k * x₀ * k⁻¹) * d.pv 7 * (k * x₀ * k⁻¹)⁻¹ * (d.pv 7)⁻¹ =
      x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ := by
    have e : (k * x₀ * k⁻¹) * d.pv 7 * (k * x₀ * k⁻¹)⁻¹ * (d.pv 7)⁻¹ =
        k * (x₀ * (k⁻¹ * d.pv 7 * k) * x₀⁻¹ * (k⁻¹ * d.pv 7 * k)⁻¹) * k⁻¹ := by group
    have hxe : x₀ * e₀ * x₀⁻¹ = e₀ := by rw [s56_V_comm_E hx₀V he₀]; group
    have e1 : x₀ * (d.pv 7 * e₀) * x₀⁻¹ * (d.pv 7 * e₀)⁻¹ =
        x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ := by
      calc x₀ * (d.pv 7 * e₀) * x₀⁻¹ * (d.pv 7 * e₀)⁻¹
          = (x₀ * d.pv 7 * x₀⁻¹) * (x₀ * e₀ * x₀⁻¹) * e₀⁻¹ * (d.pv 7)⁻¹ := by group
        _ = x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹ := by rw [hxe]; group
    rw [e, hwe, e1, hd.s56_P0_comm_U11 h49 hkP0 ha₀]
    group
  have hhom₀ := hd.s56_V_comm_pv7_hom h49 hz hx₀V (inv_mem hx₀V)
  have hhom₁ := hd.s56_V_comm_pv7_hom h49 hz hx₀'V (inv_mem hx₀V)
  have h1 : (x₀ * d.pv 7 * x₀⁻¹ * (d.pv 7)⁻¹) * (x₀⁻¹ * d.pv 7 * x₀⁻¹⁻¹ * (d.pv 7)⁻¹) = 1 := by
    rw [← hhom₀]; group
  rw [hcomm₀, h1] at hhom₁
  have hx₁V : k * x₀ * k⁻¹ * x₀⁻¹ ∈ d.s56V := mul_mem hx₀'V (inv_mem hx₀V)
  have hx₁ε : d.s56Eps (k * x₀ * k⁻¹ * x₀⁻¹) = d.s56Eps x := by
    rw [hd.s56_eps_mul_Q2' hx₀'V.2 (inv_mem hx₀V).2, hd.s56_eps_inv_Q2 hx₀V.2, hx₀'ε, hx₀ε,
      mul_assoc, hd.s56_E_sq hv10E, mul_one]
  have heV : x * (k * x₀ * k⁻¹ * x₀⁻¹)⁻¹ ∈ d.s56V := mul_mem hx (inv_mem hx₁V)
  have heE : x * (k * x₀ * k⁻¹ * x₀⁻¹)⁻¹ ∈ d.E := by
    refine (hd.s56_V_eps_eq_one_iff h49 heV).1 ?_
    rw [hd.s56_eps_mul_Q2' hx.2 (inv_mem hx₁V).2, hd.s56_eps_inv_Q2 hx₁V.2, hx₁ε]
    exact hd.s56_E_sq (s56_U11_le_E d hd hε)
  have hhom₂ := hd.s56_V_comm_pv7_hom h49 hz heV hx₁V
  rw [inv_mul_cancel_right, hhom₁, mul_one] at hhom₂
  generalize x * (k * x₀ * k⁻¹ * x₀⁻¹)⁻¹ = e at heE hhom₂
  rw [hhom₂]
  have h := inv_mem (hd.s56_pv7_conj_E heE)
  have e' : (d.pv 7 * e * (d.pv 7)⁻¹ * e⁻¹)⁻¹ = e * d.pv 7 * e⁻¹ * (d.pv 7)⁻¹ := by group
  rwa [e'] at h

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
