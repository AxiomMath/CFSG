module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

section P05Ctr

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node05_Q_eq_J_mul_V (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q) :
    ∃ j ∈ d.s56J, ∃ v ∈ d.s56V, q = j * v := by
  obtain ⟨j, hj, w, hw, rfl⟩ := hd.s56_Q0_eq_J_mul_Q2 h49 (hd.s56_Q_le_Q0 hq)
  refine ⟨j, hj, w, mem_inf.2 ⟨?_, hw⟩, rfl⟩
  simpa using mul_mem (inv_mem (hd.s56_J_le_Q h49 hj)) hq

theorem node05_exists_w (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    ∃ x ∈ d.s56V, d.s56Cm x ∈ d.s56V ∧ d.s56Cm x ∈ ⁅d.s56Q, d.s56Q⁆ ∧
      d.s56Eps (d.s56Cm x) = d.z := by
  obtain ⟨x, hxV, hxε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 8) (Data.s56_pv8_mem_E d)
  have hv7Q : d.pv 7 ∈ d.s56Q := hd.s56_J_le_Q h49 (Data.s56_pv7_mem_J d)
  refine ⟨x, hxV, mem_inf.2 ⟨?_, hd.s56_cm_mem_Q2 h49 hxV.2⟩, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem hv7Q hxV.1) (inv_mem hv7Q)) (inv_mem hxV.1)
  · have := Subgroup.commutator_mem_commutator hv7Q hxV.1
    rwa [commutatorElement_def] at this
  · rw [hd.s56_eps_cm h49 hxV.2, hxε, Data.s56_pv7_conj_pv8 d]
    have hzc : d.pv 8 * d.z = d.z * d.pv 8 := hd.s56_E_comm (Data.s56_pv8_mem_E d) hd.s56_z_mem_E
    calc d.pv 8 * d.z * (d.pv 8)⁻¹ = d.z * d.pv 8 * (d.pv 8)⁻¹ := by rw [hzc]
      _ = d.z := by group

theorem node05_z0_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    z₀ ∈ ⁅d.s56Q, d.s56Q⁆ ⊔ d.E := by
  obtain ⟨x, -, hwV, hwQ, hwε⟩ := node05_exists_w h49 hd hz
  have hwz : d.s56Cm x * z₀⁻¹ ∈ d.E := by
    rw [← hd.s56_V_eps_eq_one_iff h49 (mul_mem hwV (inv_mem hz.mem_V)),
      hd.s56_eps_mul_Q2' hwV.2 (inv_mem hz.mem_V).2, hd.s56_eps_inv_Q2 hz.mem_Q2, hz.eps, hwε]
    exact hd.s56_z_sq
  have e : z₀ = (d.s56Cm x * z₀⁻¹)⁻¹ * d.s56Cm x := by group
  rw [e]
  exact mul_mem (mem_sup_right (inv_mem hwz)) (mem_sup_left hwQ)

theorem node05_eps_mem_F_of_cm_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) {v : G}
    (hv : v ∈ d.s56V) (h : d.s56Cm v ∈ d.E) : d.s56Eps v ∈ d.F := by
  have h1 := hd.s56_eps_cm h49 hv.2
  rw [hd.s56_eps_of_comm (hd.L_comm_t (Data.s56_E_le_L d h))] at h1
  refine (hd.s56_pv7_comm_iff (hd.s56_V_eps_mem_E hv)).1 ?_
  calc d.pv 7 * d.s56Eps v
      = (d.pv 7 * d.s56Eps v * (d.pv 7)⁻¹ * (d.s56Eps v)⁻¹) * d.s56Eps v * d.pv 7 := by group
    _ = d.s56Eps v * d.pv 7 := by rw [← h1]; group

theorem node05_eq_E_or_J (hd : d.Hyp) {H : Subgroup G} (hEH : d.E ≤ H) (hHJ : H ≤ d.s56J)
    (hx : d.x₅ ∈ normalizer (H : Set G)) : H = d.E ∨ H = d.s56J := by
  have hxM := hd.s56_x5_mem_M
  have hmod := S56.card_modEq_of_centralizer_le hd.s56_orderOf_x5 hEH hHJ
    (hd.s56_ME hxM) hx
    (fun c hc hcx => hd.s56_zpowers_le_E (hd.s56_J_cent_x5 hc hcx.symm))
  rw [hd.A_facts.1] at hmod
  have hdvd : Nat.card H ∣ 2 ^ 9 := by
    have := Subgroup.card_dvd_of_le hHJ
    rwa [hd.s56_card_J] at this
  obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h32 : 32 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le hEH
    rwa [hd.A_facts.1] at this
  rw [hk] at hmod h32
  have hk5 : 5 ≤ k := by
    rcases Nat.lt_or_ge k 5 with hlt | hge
    · exfalso
      interval_cases k <;> norm_num at h32
    · exact hge
  have hkc : k = 5 ∨ k = 9 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hkc with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hEH (by rw [hk, hd.A_facts.1]; norm_num)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hHJ (by rw [hd.s56_card_J, hk])

theorem node05_J_part (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {j : G}
    (hj : j ∈ d.s56J) (h : ∀ q ∈ d.s56V, j * q * j⁻¹ * q⁻¹ ∈ d.E) : j ∈ d.E := by
  let H : Subgroup G :=
    { carrier := {j | j ∈ d.s56J ∧ ∀ q ∈ d.s56V, j * q * j⁻¹ * q⁻¹ ∈ d.E}
      one_mem' := ⟨one_mem _, fun q _ => by simpa using one_mem d.E⟩
      mul_mem' := by
        rintro a b ⟨ha, haV⟩ ⟨hb, hbV⟩
        refine ⟨mul_mem ha hb, fun q hq => ?_⟩
        have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
            (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M ha)) _).1 (hbV q hq))
          (haV q hq)
      inv_mem' := by
        rintro a ⟨ha, haV⟩
        refine ⟨inv_mem ha, fun q hq => ?_⟩
        have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M (inv_mem ha))) _).1
          (inv_mem (haV q hq)) }
  have hEH : d.E ≤ H := fun e he => ⟨Data.s56_E_le_J d he, fun q hq => by
    have hc := Data.s56_V_comm_E hq he
    have e1 : e * q * e⁻¹ * q⁻¹ = 1 := by rw [← hc]; group
    rw [e1]
    exact one_mem _⟩
  have hcon : ∀ g ∈ d.M, g ∈ normalizer (d.s56J : Set G) → ∀ k ∈ H, g * k * g⁻¹ ∈ H := by
    intro g hg hgJ k ⟨hk, hkV⟩
    refine ⟨(mem_normalizer_iff.1 hgJ k).1 hk, fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 (inv_mem hg) hq
    have e : g * k * g⁻¹ * q * (g * k * g⁻¹)⁻¹ * q⁻¹ =
        g * (k * (g⁻¹ * q * g⁻¹⁻¹) * k⁻¹ * (g⁻¹ * q * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hd.s56_ME hg) _).1 (hkV _ hq')
  have hx : d.x₅ ∈ normalizer (H : Set G) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hcon _ hd.s56_x5_mem_M hd.s56_x5_normalizes_J k hk, fun hk => ?_⟩
    have := hcon _ (inv_mem hd.s56_x5_mem_M) (inv_mem hd.s56_x5_normalizes_J) _ hk
    simpa [mul_assoc] using this
  rcases node05_eq_E_or_J hd hEH (fun k hk => hk.1) hx with hH | hH
  · have hjH : j ∈ H := ⟨hj, h⟩
    rw [hH] at hjH
    exact hjH
  · exfalso
    obtain ⟨x, hxV, hwV, -, hwε⟩ := node05_exists_w h49 hd hz
    have hv7 : d.pv 7 ∈ H := by
      rw [hH]
      exact Data.s56_pv7_mem_J d
    have h1 := (hd.s56_V_eps_eq_one_iff h49 hwV).2 (hv7.2 x hxV)
    rw [hwε] at h1
    exact hd.s56_z_ne_one h1

theorem node05_V_part (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {v : G}
    (hv : v ∈ d.s56V) (h : ∀ j ∈ d.s56J, j * v * j⁻¹ * v⁻¹ ∈ d.E) : v ∈ d.E ⊔ zpowers z₀ := by
  let W : Subgroup G :=
    { carrier := {v | v ∈ d.s56V ∧ ∀ j ∈ d.s56J, j * v * j⁻¹ * v⁻¹ ∈ d.E}
      one_mem' := ⟨one_mem _, fun j _ => by simpa using one_mem d.E⟩
      mul_mem' := by
        rintro a b ⟨ha, haJ⟩ ⟨hb, hbJ⟩
        refine ⟨mul_mem ha hb, fun j hj => ?_⟩
        have e : j * (a * b) * j⁻¹ * (a * b)⁻¹ =
            (j * a * j⁻¹ * a⁻¹) * (a * (j * b * j⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem (haJ j hj)
          ((mem_normalizer_iff.1 (hd.s56_ME (d.s56_V_le_M ha)) _).1 (hbJ j hj))
      inv_mem' := by
        rintro a ⟨ha, haJ⟩
        refine ⟨inv_mem ha, fun j hj => ?_⟩
        have e : j * a⁻¹ * j⁻¹ * a⁻¹⁻¹ = a⁻¹ * (j * a * j⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.1 (hd.s56_ME (d.s56_V_le_M (inv_mem ha))) _).1
          (inv_mem (haJ j hj)) }
  set R : Subgroup G := (W.subgroupOf d.s56V).map hd.s56EpsHom with hR
  have hmemR : ∀ e, e ∈ R ↔ ∃ w ∈ W, d.s56Eps w = e := by
    intro e
    rw [hR, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.1, Subgroup.mem_subgroupOf.1 hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw.1⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
  have hRE : R ≤ d.E := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := (hmemR e).1 he
    exact hd.s56_V_eps_mem_E hw.1
  have hzR : zpowers d.z ≤ R := by
    refine zpowers_le.2 ((hmemR _).2 ⟨z₀, ⟨hz.mem_V, fun j hj => ?_⟩, hz.eps⟩)
    have h1 : j * z₀ * j⁻¹ * z₀⁻¹ = 1 := by rw [hz.comm_Q j (hd.s56_J_le_Q h49 hj)]; group
    rw [h1]
    exact one_mem _
  have hcon : ∀ g ∈ d.M, g * d.t = d.t * g → g ∈ normalizer (d.s56J : Set G) →
      ∀ k ∈ R, g * k * g⁻¹ ∈ R := by
    intro g hg hgt hgJ k hk
    obtain ⟨w, hw, rfl⟩ := (hmemR k).1 hk
    refine (hmemR _).2 ⟨g * w * g⁻¹, ⟨hd.s56_V_conj_mem h49 hg hw.1, fun j hj => ?_⟩,
      hd.s56_eps_conj hgt w⟩
    have hj' : g⁻¹ * j * g⁻¹⁻¹ ∈ d.s56J := (mem_normalizer_iff.1 (inv_mem hgJ) j).1 hj
    have e : j * (g * w * g⁻¹) * j⁻¹ * (g * w * g⁻¹)⁻¹ =
        g * ((g⁻¹ * j * g⁻¹⁻¹) * w * (g⁻¹ * j * g⁻¹⁻¹)⁻¹ * w⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hd.s56_ME hg) _).1 (hw.2 _ hj')
  have hxR : d.x₅ ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hcon _ hd.s56_x5_mem_M hd.s56_x5_comm_t hd.s56_x5_normalizes_J k hk,
      fun hk => ?_⟩
    have hxt' : d.x₅⁻¹ * d.t = d.t * d.x₅⁻¹ :=
      (show Commute d.x₅ d.t from hd.s56_x5_comm_t).inv_left.eq
    have := hcon _ (inv_mem hd.s56_x5_mem_M) hxt' (inv_mem hd.s56_x5_normalizes_J) _ hk
    simpa [mul_assoc] using this
  rcases hd.s56_stable_sub_E hzR hRE hxR with hRz | hRE'
  · have hεv : d.s56Eps v ∈ zpowers d.z := by
      rw [← hRz]
      exact (hmemR _).2 ⟨v, ⟨hv, h⟩, rfl⟩
    rcases hd.s56_mem_zpowers_z hεv with h1 | h1
    · exact mem_sup_left ((hd.s56_V_eps_eq_one_iff h49 hv).1 h1)
    · have hvz : v * z₀⁻¹ ∈ d.E := by
        rw [← hd.s56_V_eps_eq_one_iff h49 (mul_mem hv (inv_mem hz.mem_V)),
          hd.s56_eps_mul_Q2' hv.2 (inv_mem hz.mem_V).2, hd.s56_eps_inv_Q2 hz.mem_Q2, hz.eps, h1]
        exact hd.s56_z_sq
      have e : v = (v * z₀⁻¹) * z₀ := by group
      rw [e]
      exact mul_mem (mem_sup_left hvz) (mem_sup_right (mem_zpowers _))
  · exfalso
    have hv8 : d.pv 8 ∈ R := by
      rw [hRE']
      exact Data.s56_pv8_mem_E d
    obtain ⟨w, hw, hwε⟩ := (hmemR _).1 hv8
    have hcm : d.s56Cm w ∈ d.E := hw.2 _ (Data.s56_pv7_mem_J d)
    have hF := node05_eps_mem_F_of_cm_mem_E h49 hd hw.1 hcm
    rw [hwε] at hF
    exact hd.s56_pv8_not_mem_F hF

theorem node05_center (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    centralizerMod d.s56Q d.E d.s56Q = d.E ⊔ zpowers z₀ ∧
      ⁅d.s56Q, d.s56Q⁆ ⊔ d.E = d.E ⊔ zpowers z₀ := by
  have hQM : d.s56Q ≤ d.M := hd.s56_Q_le_Q0.trans (hd.s56_Q0_le_M h49)
  have hsub : centralizerMod d.s56Q d.E d.s56Q ≤ d.E ⊔ zpowers z₀ := by
    rintro q ⟨hqQ, -, hqc⟩
    obtain ⟨j, hj, v, hv, rfl⟩ := node05_Q_eq_J_mul_V h49 hd hqQ
    have hjE : j ∈ d.E := by
      refine node05_J_part h49 hd hz hj fun q' hq' => ?_
      have h1 := hqc q' hq'.1
      have h2 : v * q' * v⁻¹ * q'⁻¹ ∈ d.E := hd.s56_Q2_comm_mem_E h49 hv.2 hq'.2
      have h3 : j * (v * q' * v⁻¹ * q'⁻¹) * j⁻¹ ∈ d.E :=
        (mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M hj)) _).1 h2
      have e : j * q' * j⁻¹ * q'⁻¹ =
          (j * (v * q' * v⁻¹ * q'⁻¹) * j⁻¹)⁻¹ * (j * v * q' * (j * v)⁻¹ * q'⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem h3) h1
    have hvV : j * v ∈ d.s56V := mul_mem (hd.s56_E_le_V h49 hjE) hv
    refine node05_V_part h49 hd hz hvV fun j' hj' => ?_
    have h1 := hqc j' (hd.s56_J_le_Q h49 hj')
    have e : j' * (j * v) * j'⁻¹ * (j * v)⁻¹ = ((j * v) * j' * (j * v)⁻¹ * j'⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hsup : d.E ⊔ zpowers z₀ ≤ centralizerMod d.s56Q d.E d.s56Q := by
    refine sup_le (fun e he => ⟨hd.s56_E_le_Q h49 he, Subgroup.le_normalizer he, fun y hy => ?_⟩)
      (zpowers_le.2 ⟨hz.mem_Q, hd.s56_ME hz.mem_M, fun y hy => ?_⟩)
    · have h1 : y * e⁻¹ * y⁻¹ ∈ d.E :=
        (mem_normalizer_iff.1 (hd.s56_ME (hQM hy)) _).1 (inv_mem he)
      have e1 : e * y * e⁻¹ * y⁻¹ = e * (y * e⁻¹ * y⁻¹) := by group
      rw [e1]
      exact mul_mem he h1
    · have h1 : z₀ * y = y * z₀ := (hz.comm_Q y hy).symm
      have e1 : z₀ * y * z₀⁻¹ * y⁻¹ = 1 := by rw [h1]; group
      rw [e1]
      exact one_mem _
  refine ⟨le_antisymm hsub hsup, le_antisymm ?_ ?_⟩
  · exact sup_le (hd.s56_Q_comm_le_S h49 hz.mem_Q2 hz.eps hz.dich) le_sup_left
  · exact sup_le le_sup_right (zpowers_le.2 (node05_z0_mem h49 hd hz))

end P05Ctr

end CFSG.LocalAnalysis.EvenBN.Tits.N
