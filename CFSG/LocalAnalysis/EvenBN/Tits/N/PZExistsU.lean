module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Kappa
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P517
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N5

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.PZ

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open CFSG.LocalAnalysis.EvenBN.Tits.Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem comm_pv7_conj (h49 : d.Thm49Statement) (hd : d.Hyp) {k v : G} (hkM : k ∈ d.M)
    (hkN : k ∈ d.N) (hv : v ∈ d.s56V) :
    k * v * k⁻¹ * d.pv 7 * (k * v * k⁻¹)⁻¹ * (d.pv 7)⁻¹ =
      k * (v * d.pv 7 * v⁻¹ * (d.pv 7)⁻¹) * k⁻¹ := by
  obtain ⟨c, hc, hf⟩ : ∃ c ∈ d.E, k⁻¹ * d.pv 7 * k = d.pv 7 * c := by
    have hF : k⁻¹ * d.pv 7 * k⁻¹⁻¹ ∈ d.F := hd.s56_N_conj_F h49 (inv_mem hkN) hd.s56_pv7_mem_F
    rw [inv_inv] at hF
    refine ⟨d.pv 7 * (k⁻¹ * d.pv 7 * k), ?_, by rw [← mul_assoc, s56_pv7_mul_self, one_mul]⟩
    refine (Data.Hyp.s56_F_cases d hF).resolve_left fun h => hd.s56_pv7_not_mem_E ?_
    have h' := (mem_normalizer_iff.1 (hd.s56_ME hkM) _).1 h
    have e : k * (k⁻¹ * d.pv 7 * k) * k⁻¹ = d.pv 7 := by group
    rwa [e] at h'
  have hvc := s56_V_comm_E hv hc
  calc k * v * k⁻¹ * d.pv 7 * (k * v * k⁻¹)⁻¹ * (d.pv 7)⁻¹
      = k * (v * (k⁻¹ * d.pv 7 * k) * v⁻¹ * (k⁻¹ * d.pv 7 * k)⁻¹) * k⁻¹ := by group
    _ = k * (v * d.pv 7 * v⁻¹ * (v * c) * v⁻¹ * c⁻¹ * (d.pv 7)⁻¹) * k⁻¹ := by rw [hf]; group
    _ = k * (v * d.pv 7 * v⁻¹ * (c * v) * v⁻¹ * c⁻¹ * (d.pv 7)⁻¹) * k⁻¹ := by rw [hvc]
    _ = k * (v * d.pv 7 * v⁻¹ * (d.pv 7)⁻¹) * k⁻¹ := by group

theorem exists_lift (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {w : G}
    (hw : w ∈ d.E ⊓ d.F) : ∃ v ∈ d.s56V, v ∈ d.N ∧ d.s56Eps v = w := by
  obtain ⟨v, hv, hvw⟩ := hd.s56_V_eps_surj h49 hz w (mem_inf.1 hw).1
  refine ⟨v, hv, (hd.s56_mem_N_iff_eps h49 (hd.s56_Q_le_Q0 hv.1)).2 ?_, hvw⟩
  rw [hvw]
  exact (mem_inf.1 hw).2

private def Good (d : Data G) (w : G) : Prop :=
  ∃ v ∈ d.s56V, v ∈ d.N ∧ d.s56Eps v = w ∧ v * d.pv 7 * v⁻¹ * (d.pv 7)⁻¹ ∈ zpowers d.z

private theorem good_mul (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {w w' : G} (h : Good d w) (h' : Good d w') : Good d (w * w') := by
  obtain ⟨v, hv, hvN, hvw, hvδ⟩ := h
  obtain ⟨v', hv', hv'N, hv'w, hv'δ⟩ := h'
  refine ⟨v * v', mul_mem hv hv', mul_mem hvN hv'N, ?_, ?_⟩
  · rw [hd.s56_eps_mul_Q2' hv.2 hv'.2, hvw, hv'w]
  · rw [hd.s56_V_comm_pv7_hom h49 hz hv hv']
    exact mul_mem hvδ hv'δ

private theorem good_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {u : G} (hu : u ∈ d.s56U11) : Good d u := by
  obtain ⟨v, hv, hvN, hvu⟩ := exists_lift h49 hd hz
    (mem_inf.2 ⟨s56_U11_le_E d hd hu, s56_U10_le_F d (s56_U11_le_U10 d hu)⟩)
  exact ⟨v, hv, hvN, hvu, hd.s56_V_comm_pv7_mem_zpowers h49 hz hv (by rw [hvu]; exact hu)⟩

private theorem good_comm_K (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) {k w : G} (hk : k ∈ d.s56K) (hw : w ∈ d.E ⊓ d.F) :
    Good d (k * w * k⁻¹ * w⁻¹) := by
  obtain ⟨v, hv, hvN, hvw⟩ := exists_lift h49 hd hz hw
  have hkP0 : k ∈ d.s56P0 := hd.s56_K_le_P0 h49 hk
  obtain ⟨hkN, hkC⟩ := mem_inf.1 (hd.s56_K_le_CNt hk)
  have hkM : k ∈ d.M := hd.s56_CP0t_le_M hkP0 hkC
  have hkt : k * d.t = d.t * k := mem_centralizer_singleton_iff.1 hkC
  have hv' : k * v * k⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hkM hv
  have hv'N : k * v * k⁻¹ ∈ d.N := mul_mem (mul_mem hkN hvN) (inv_mem hkN)
  have ha := hκ v (mem_inf.2 ⟨hv, hvN⟩) _ hd.s56_pv7_mem_F
  refine ⟨k * v * k⁻¹ * v, mul_mem hv' hv, mul_mem hv'N hvN, ?_, ?_⟩
  · rw [hd.s56_eps_mul_Q2' hv'.2 hv.2, hd.s56_eps_conj hkt, hvw,
      inv_eq_of_mul_eq_one_right (hd.s56_E_sq (mem_inf.1 hw).1)]
  · rw [hd.s56_V_comm_pv7_hom h49 hz hv' hv, comm_pv7_conj h49 hd hkM hkN hv,
      hd.s56_P0_comm_U11 h49 hkP0 ha, mul_inv_cancel_right, hd.s56_E_sq (s56_U11_le_E d hd ha)]
    exact one_mem _

private theorem good_pv10 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) : Good d (d.pv 10) := by
  obtain ⟨x, hx, hxU⟩ : ∃ x ∈ d.E ⊓ d.F, x ∉ d.s56U10 := by
    by_contra hcon
    have hle : d.E ⊓ d.F ≤ d.s56U10 := fun x hx => by
      by_contra hxU
      exact hcon ⟨x, hx, hxU⟩
    have h := Subgroup.card_le_of_le hle
    rw [hd.s56_card_E_inf_F, s56_card_U10] at h
    omega
  have hxF : x ∈ d.F := (mem_inf.1 hx).2
  obtain ⟨k, hk, hkx⟩ : ∃ k ∈ d.s56K, k * x * k⁻¹ * x⁻¹ ∉ d.s56U11 := by
    by_contra hcon
    exact hxU (s56_comm_K_le_U10 hxF fun k hk => by
      by_contra h
      exact hcon ⟨k, hk, h⟩)
  rcases s56_U10_cases (hd.s56_P0_comm_F_le_U10 h49 (hd.s56_K_le_P0 h49 hk) hxF) with
    h | ⟨u, hu, hue⟩
  · exact absurd h hkx
  · have hg := good_mul h49 hd hz (good_comm_K h49 hd hz hκ hk hx)
      (good_U11 h49 hd hz (inv_mem hu))
    rwa [hue, mul_inv_cancel_right] at hg

theorem exists_u (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hκ : d.S56Kappa) :
    ∃ u ∈ d.s56V, u ∈ d.N ∧ (∀ f ∈ d.F, u * f = f * u) ∧ d.s56Eps u = d.pv 10 := by
  obtain ⟨u, hu, huN, huε, hu7⟩ : ∃ u ∈ d.s56V, u ∈ d.N ∧ d.s56Eps u = d.pv 10 ∧
      u * d.pv 7 * u⁻¹ * (d.pv 7)⁻¹ = 1 := by
    obtain ⟨v, hv, hvN, hvε, hvδ⟩ := good_pv10 h49 hd hz hκ
    rcases hd.s56_mem_zpowers_z hvδ with h | h
    · exact ⟨v, hv, hvN, hvε, h⟩
    · have h8E := s56_pv8_mem_E d
      have h8V : d.pv 8 ∈ d.s56V := hd.s56_E_le_V h49 h8E
      have h8ε : d.s56Eps (d.pv 8) = 1 := (hd.s56_V_eps_eq_one_iff h49 h8V).2 h8E
      have h8N : d.pv 8 ∈ d.N := (hd.s56_mem_N_iff_eps h49 (hd.s56_Q_le_Q0 h8V.1)).2
        (by rw [h8ε]; exact one_mem _)
      refine ⟨v * d.pv 8, mul_mem hv h8V, mul_mem hvN h8N, ?_, ?_⟩
      · rw [hd.s56_eps_mul_Q2' hv.2 h8V.2, hvε, h8ε, mul_one]
      · rw [hd.s56_V_comm_pv7_hom h49 hz hv h8V, h, hd.s56_pv8_comm_pv7, hd.s56_z_sq]
  have hu7' : u * d.pv 7 = d.pv 7 * u := by
    calc u * d.pv 7 = (u * d.pv 7 * u⁻¹ * (d.pv 7)⁻¹) * d.pv 7 * u := by group
      _ = d.pv 7 * u := by rw [hu7, one_mul]
  refine ⟨u, hu, huN, fun f hf => ?_, huε⟩
  rcases Data.Hyp.s56_F_cases d hf with h | h
  · exact s56_V_comm_E hu h
  · obtain ⟨e, he, rfl⟩ : ∃ e ∈ d.E, f = d.pv 7 * e :=
      ⟨d.pv 7 * f, h, by rw [← mul_assoc, s56_pv7_mul_self, one_mul]⟩
    have hc := s56_V_comm_E hu he
    calc u * (d.pv 7 * e) = u * d.pv 7 * e := by group
      _ = d.pv 7 * u * e := by rw [hu7']
      _ = d.pv 7 * (u * e) := by group
      _ = d.pv 7 * (e * u) := by rw [hc]
      _ = d.pv 7 * e * u := by group

end CFSG.LocalAnalysis.EvenBN.Tits.N.PZ
