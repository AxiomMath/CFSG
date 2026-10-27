module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Ten

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


structure S56Z0 (d : Data G) (z₀ : G) : Prop where
  mem_Q : z₀ ∈ d.s56Q
  mem_Q2 : z₀ ∈ d.s56Q2
  eps : d.s56Eps z₀ = d.z
  comm_x : d.x₅ * z₀ = z₀ * d.x₅
  sq : z₀ * z₀ ∈ zpowers d.z
  comm_v : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z
  dich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e
  comm_Q : ∀ q ∈ d.s56Q, q * z₀ = z₀ * q

theorem Hyp.s56_exists_S56Z0 (h49 : d.Thm49Statement) (hd : d.Hyp) : ∃ z₀ : G, d.S56Z0 z₀ := by
  obtain ⟨z₀, hQ, hQ2, hε, hxz, hsq, hvz, hdich, hcomm, -⟩ := hd.s56_exists_z0_full h49
  exact ⟨z₀, ⟨hQ, hQ2, hε, hxz, hsq, hvz, hdich, hcomm⟩⟩

theorem S56Z0.cen {z₀ : G} (hz : d.S56Z0 z₀) {e : G} (he : e ∈ d.E) : z₀ * e = e * z₀ :=
  (((s56_mem_Q2_iff).1 hz.mem_Q2).2 e he).symm

theorem S56Z0.mem_M {z₀ : G} (hz : d.S56Z0 z₀) : z₀ ∈ d.M := ((s56_mem_Q2_iff).1 hz.mem_Q2).1

theorem Hyp.s56_Z0_sq_cases (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    z₀ * z₀ = 1 ∨ z₀ * z₀ = d.z :=
  hd.s56_mem_zpowers_z hz.sq

theorem Hyp.s56_card_zpowers_z (hd : d.Hyp) : Nat.card (zpowers d.z) = 2 := by
  rw [Nat.card_zpowers]
  exact hd.s56_orderOf_z

@[expose] noncomputable def s56V (d : Data G) : Subgroup G := d.s56Q ⊓ d.s56Q2

theorem s56_mem_V_iff {v : G} : v ∈ d.s56V ↔ v ∈ d.s56Q ∧ v ∈ d.s56Q2 := mem_inf

theorem s56_V_le_Q (d : Data G) : d.s56V ≤ d.s56Q := inf_le_left

theorem s56_V_le_Q2 (d : Data G) : d.s56V ≤ d.s56Q2 := inf_le_right

theorem s56_V_le_M (d : Data G) : d.s56V ≤ d.M := fun _ hv => ((s56_mem_Q2_iff).1 hv.2).1

theorem Hyp.s56_V_conj_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {g v : G} (hg : g ∈ d.M)
    (hv : v ∈ d.s56V) : g * v * g⁻¹ ∈ d.s56V :=
  mem_inf.2 ⟨(mem_normalizer_iff.1 (hd.s56_M_le_normalizer_Q h49 hg) v).1 hv.1,
    hd.s56_Q2_conj_mem hg hv.2⟩

theorem Hyp.s56_M_le_normalizer_V (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.M ≤ normalizer (d.s56V : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hd.s56_V_conj_mem h49 hg hv, fun hv => ?_⟩
  have := hd.s56_V_conj_mem h49 (inv_mem hg) hv
  simpa [mul_assoc] using this

theorem Hyp.s56_E_le_V (h49 : d.Thm49Statement) (hd : d.Hyp) : d.E ≤ d.s56V :=
  le_inf (hd.s56_E_le_Q h49) hd.s56_E_le_Q2

theorem s56_V_comm_E {v e : G} (hv : v ∈ d.s56V) (he : e ∈ d.E) : v * e = e * v :=
  (((s56_mem_Q2_iff).1 hv.2).2 e he).symm

theorem Hyp.s56_V_isPGroup (h49 : d.Thm49Statement) (hd : d.Hyp) : IsPGroup 2 d.s56V :=
  IsPGroup.to_le (s56_Q0_isPGroup d) (fun v hv => hd.s56_Q_le_Q0 hv.1)

theorem S56Z0.mem_V {z₀ : G} (hz : d.S56Z0 z₀) : z₀ ∈ d.s56V := ⟨hz.mem_Q, hz.mem_Q2⟩

theorem S56Z0.comm_V {z₀ : G} (hz : d.S56Z0 z₀) {v : G} (hv : v ∈ d.s56V) : v * z₀ = z₀ * v :=
  hz.comm_Q v hv.1

@[expose] noncomputable def Hyp.s56EpsHom (hd : d.Hyp) : d.s56V →* G :=
  MonoidHom.mk' (fun v => d.s56Eps v.1) (fun v w => hd.s56_eps_mul_Q2' v.2.2 w.2.2)

theorem Hyp.s56EpsHom_apply (hd : d.Hyp) (v : d.s56V) : hd.s56EpsHom v = d.s56Eps v.1 := rfl

theorem Hyp.s56_V_eps_eq_one_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {v : G} (hv : v ∈ d.s56V) :
    d.s56Eps v = 1 ↔ v ∈ d.E := by
  constructor
  · intro h
    have h1 := hd.s56_conj_t v
    rw [h, mul_one] at h1
    have hvt : v * d.t = d.t * v := by
      calc v * d.t = v * d.t * v⁻¹ * v := by group
        _ = d.t * v := by rw [h1]
    have hvC : v ∈ centralizer (d.A : Set G) :=
      (hd.s56_mem_centralizer_A_iff).2 ⟨fun e he => (s56_V_comm_E hv he).symm, hvt⟩
    have := hd.s56_Q_inf_C h49 ▸ (mem_inf.2 ⟨hv.1, hvC⟩ : v ∈ d.s56Q ⊓ centralizer (d.A : Set G))
    exact this
  · intro he
    exact hd.s56_eps_of_comm (hd.L_comm_t (s56_E_le_L d he))

theorem Hyp.s56_V_eps_mem_E (hd : d.Hyp) {v : G} (hv : v ∈ d.s56V) : d.s56Eps v ∈ d.E :=
  hd.s56_eps_mem_E (s56_V_le_M d hv)

theorem Hyp.s56_x5_normalizes_zpowers_z (hd : d.Hyp) :
    d.x₅ ∈ normalizer ((zpowers d.z : Subgroup G) : Set G) := by
  apply Subgroup.centralizer_le_normalizer ((zpowers d.z : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := hw
  exact (Commute.zpow_left (show Commute d.z d.x₅ from hd.s56_x5_comm_z.symm) k).eq

theorem Hyp.s56_stable_sub_E (hd : d.Hyp) {R : Subgroup G} (hzR : zpowers d.z ≤ R)
    (hRE : R ≤ d.E) (hx : d.x₅ ∈ normalizer (R : Set G)) : R = zpowers d.z ∨ R = d.E := by
  have hmod := S56.card_modEq_of_centralizer_le hd.s56_orderOf_x5 hzR hRE
    hd.s56_x5_normalizes_zpowers_z hx (fun c hc hcx => hd.s56_E_cent_x5 hc hcx.symm)
  have hzcard := hd.s56_card_zpowers_z
  have hdvd : Nat.card R ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le hRE
    rw [hd.A_facts.1] at this
    simpa using this
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk, hzcard] at hmod
  have hk' : k = 1 ∨ k = 5 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hk' with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hzR (by rw [hk, hzcard]; norm_num)).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hRE (by rw [hk, hd.A_facts.1]; norm_num)

theorem Hyp.s56_V_eps_surj (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    ∀ s ∈ d.E, ∃ v ∈ d.s56V, d.s56Eps v = s := by
  have hxM := hd.s56_x5_mem_M
  have hxt := hd.s56_x5_comm_t
  set K : Subgroup G := hd.s56EpsHom.range with hK
  have hmemK : ∀ k, k ∈ K ↔ ∃ v ∈ d.s56V, d.s56Eps v = k := by
    intro k
    rw [hK, MonoidHom.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hKE : K ≤ d.E := fun k hk => by
    obtain ⟨v, hv, rfl⟩ := (hmemK k).1 hk
    exact hd.s56_V_eps_mem_E hv
  have hzK : zpowers d.z ≤ K := zpowers_le.2 ((hmemK _).2 ⟨z₀, hz.mem_V, hz.eps⟩)
  have hcon : ∀ g ∈ d.M, g * d.t = d.t * g → ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg hgt k hk
    obtain ⟨v, hv, rfl⟩ := (hmemK k).1 hk
    refine (hmemK _).2 ⟨g * v * g⁻¹, hd.s56_V_conj_mem h49 hg hv, ?_⟩
    exact hd.s56_eps_conj hgt v
  have hxK : d.x₅ ∈ normalizer (K : Set G) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hcon _ hxM hxt k hk, fun hk => ?_⟩
    have hxt' : d.x₅⁻¹ * d.t = d.t * d.x₅⁻¹ := (show Commute d.x₅ d.t from hxt).inv_left.eq
    have := hcon d.x₅⁻¹ (inv_mem hxM) hxt' _ hk
    simpa [mul_assoc] using this
  rcases hd.s56_stable_sub_E hzK hKE hxK with hKz | hKE'
  · exfalso
    have hw : ∀ s ∈ d.E, s * (d.x₅ * s * d.x₅⁻¹) ∈ zpowers d.z := by
      intro s hs
      obtain ⟨-, -, htrans, -⟩ := hd.s56_structure_M h49
      obtain ⟨m, hm, hmt⟩ := htrans _ hs
      have hmε : d.s56Eps m = s := by
        rw [s56Eps, hmt, ← mul_assoc, hd.t_mul_self, one_mul]
      have hmQ0 : m ∈ d.s56Q0 := hd.s56_Q2_le_Q0 h49 hm
      have hxm : d.x₅ * m⁻¹ * d.x₅⁻¹ ∈ d.s56Q2 := hd.s56_Q2_conj_mem hxM (inv_mem hm)
      have hcomm : m * d.x₅ * m⁻¹ * d.x₅⁻¹ ∈ d.s56Q := by
        have := Subgroup.commutator_mem_commutator hmQ0 (mem_zpowers d.x₅)
        rwa [commutatorElement_def] at this
      have hprod : m * d.x₅ * m⁻¹ * d.x₅⁻¹ = m * (d.x₅ * m⁻¹ * d.x₅⁻¹) := by group
      have hvV : m * (d.x₅ * m⁻¹ * d.x₅⁻¹) ∈ d.s56V := by
        refine mem_inf.2 ⟨?_, mul_mem hm hxm⟩
        rw [← hprod]; exact hcomm
      have hε1 : d.s56Eps (m * (d.x₅ * m⁻¹ * d.x₅⁻¹)) = s * (d.x₅ * s * d.x₅⁻¹) := by
        rw [hd.s56_eps_mul_Q2' hm hxm, hmε, hd.s56_eps_conj hxt, hd.s56_eps_inv_Q2 hm, hmε]
      rw [← hε1]
      have : d.s56Eps (m * (d.x₅ * m⁻¹ * d.x₅⁻¹)) ∈ K := (hmemK _).2 ⟨_, hvV, rfl⟩
      rwa [hKz] at this
    have hx2 : ∀ s ∈ d.E, d.x₅ ^ 2 * s = s * d.x₅ ^ 2 := by
      intro s hs
      have hxs : d.x₅ * s * d.x₅⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hd.s56_ME hxM) s).1 hs
      have h1 := hw s hs
      have hss := hd.s56_E_sq hs
      obtain ⟨w, hwdef⟩ : ∃ w, w = s * (d.x₅ * s * d.x₅⁻¹) := ⟨_, rfl⟩
      rw [← hwdef] at h1
      have hxsw : d.x₅ * s * d.x₅⁻¹ = s * w := by
        rw [hwdef]
        calc d.x₅ * s * d.x₅⁻¹ = (s * s) * (d.x₅ * s * d.x₅⁻¹) := by rw [hss, one_mul]
          _ = s * (s * (d.x₅ * s * d.x₅⁻¹)) := by group
      have hxw : d.x₅ * w * d.x₅⁻¹ = w := by
        have := hd.s56_M_comm_zpowers hxM h1
        rw [this]; group
      have hww := hd.s56_zpowers_sq h1
      have hx2s : d.x₅ * (d.x₅ * s * d.x₅⁻¹) * d.x₅⁻¹ = s := by
        rw [hxsw]
        calc d.x₅ * (s * w) * d.x₅⁻¹ = (d.x₅ * s * d.x₅⁻¹) * (d.x₅ * w * d.x₅⁻¹) := by group
          _ = (s * w) * w := by rw [hxsw, hxw]
          _ = s * (w * w) := by group
          _ = s := by rw [hww, mul_one]
      have e : d.x₅ ^ 2 * s * (d.x₅ ^ 2)⁻¹ = d.x₅ * (d.x₅ * s * d.x₅⁻¹) * d.x₅⁻¹ := by
        rw [pow_two]; group
      exact mul_inv_eq_iff_eq_mul.1 (e.trans hx2s)
    have hx1 : ∀ s ∈ d.E, s * d.x₅ = d.x₅ * s := by
      intro s hs
      have hx5 : d.x₅ ^ 5 = 1 := by rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _
      have h6 : (d.x₅ ^ 2) ^ 3 = d.x₅ := by
        calc (d.x₅ ^ 2) ^ 3 = d.x₅ ^ 5 * d.x₅ := by group
          _ = d.x₅ := by rw [hx5, one_mul]
      have hc : Commute (d.x₅ ^ 2) s := hx2 s hs
      have hc3 := hc.pow_left 3
      rw [h6] at hc3
      exact hc3.symm.eq
    have hEz : d.E ≤ zpowers d.z := fun s hs => hd.s56_E_cent_x5 hs (hx1 s hs)
    have hle := Subgroup.card_le_of_le hEz
    rw [hd.A_facts.1, hd.s56_card_zpowers_z] at hle
    omega
  · intro s hs
    have hsK : s ∈ K := by rw [hKE']; exact hs
    exact (hmemK s).1 hsK

theorem Hyp.s56_card_V (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    Nat.card d.s56V = 2 ^ 10 := by
  have hsurj := hd.s56_V_eps_surj h49 hz
  have hrange : hd.s56EpsHom.range = d.E := by
    refine le_antisymm ?_ ?_
    · rintro k ⟨v, rfl⟩
      exact hd.s56_V_eps_mem_E v.2
    · intro s hs
      obtain ⟨v, hv, hvs⟩ := hsurj s hs
      exact ⟨⟨v, hv⟩, hvs⟩
  have hker : hd.s56EpsHom.ker = d.E.subgroupOf d.s56V := by
    ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf, hd.s56EpsHom_apply]
    exact hd.s56_V_eps_eq_one_iff h49 v.2
  have h := Subgroup.card_ker_mul_card_range hd.s56EpsHom
  rw [hrange, hker] at h
  have hcard : Nat.card (d.E.subgroupOf d.s56V) = Nat.card d.E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hd.s56_E_le_V h49)).toEquiv
  rw [hcard, hd.A_facts.1] at h
  rw [← h]
  norm_num

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
