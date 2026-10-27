module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.s56_S_le_V (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.E ⊔ zpowers z₀ ≤ d.s56V :=
  sup_le (hd.s56_E_le_V h49) (zpowers_le.2 hz.mem_V)

theorem Hyp.s56_S_comm_V (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {s v : G} (hs : s ∈ d.E ⊔ zpowers z₀) (hv : v ∈ d.s56V) : s * v = v * s := by
  have hz₀sq := hd.s56_Q2_sq_mem_E_all h49 z₀ hz.mem_Q2
  rcases s56y_mem_sup_zpowers (A := d.E) (fun a ha => hz.cen ha) hz₀sq hs with
    h | ⟨e, he, rfl⟩
  · exact (s56_V_comm_E hv h).symm
  · calc z₀ * e * v = z₀ * (e * v) := by group
      _ = z₀ * (v * e) := by rw [← s56_V_comm_E hv he]
      _ = (z₀ * v) * e := by group
      _ = (v * z₀) * e := by rw [← hz.comm_V hv]
      _ = v * (z₀ * e) := by group

theorem Hyp.s56_J_conj_V_sq (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {j v : G} (hj : j ∈ d.s56J) (hv : v ∈ d.s56V) :
    (j * d.s56Eps v * j⁻¹ = d.s56Eps v → j * (v * v) * j⁻¹ = v * v) ∧
    (j * d.s56Eps v * j⁻¹ = d.z * d.s56Eps v →
      j * (v * v) * j⁻¹ = (z₀ * z₀) * (v * v)) := by
  have hjt : j * d.t = d.t * j := hd.L_comm_t (s56_J_le_L d hj)
  have hjM : j ∈ d.M := hd.s56_J_le_M hj
  have hw : j * v * j⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hjM hv
  have hεw : d.s56Eps (j * v * j⁻¹) = j * d.s56Eps v * j⁻¹ := hd.s56_eps_conj hjt v
  have hz₀sq := hd.s56_Q2_sq_mem_E_all h49 z₀ hz.mem_Q2
  obtain ⟨u, hudef⟩ : ∃ u, u = j * v * j⁻¹ * v⁻¹ := ⟨_, rfl⟩
  have huS : u ∈ d.E ⊔ zpowers z₀ := by
    rw [hudef]; exact hd.s56_J_comm_Q2_mem h49 hz.mem_Q2 hz.eps hz.dich hj hv.2
  have huV : u ∈ d.s56V := by rw [hudef]; exact mul_mem hw (inv_mem hv)
  have hwu : j * v * j⁻¹ = u * v := by rw [hudef]; group
  have hεu : d.s56Eps u = d.s56Eps (j * v * j⁻¹) * d.s56Eps v := by
    rw [hudef, hd.s56_eps_mul_Q2' hw.2 (inv_mem hv).2, hd.s56_eps_inv_Q2 hv.2]
  have hεvE := hd.s56_V_eps_mem_E hv
  have hεε := hd.s56_E_sq hεvE
  have hsq : j * (v * v) * j⁻¹ = (u * u) * (v * v) := by
    have huv : u * v = v * u := hd.s56_S_comm_V h49 hz huS hv
    calc j * (v * v) * j⁻¹ = (j * v * j⁻¹) * (j * v * j⁻¹) := by group
      _ = (u * v) * (u * v) := by rw [hwu]
      _ = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by group
  constructor
  · intro h
    have hε1 : d.s56Eps u = 1 := by rw [hεu, hεw, h]; exact hεε
    have huE : u ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 huV).1 hε1
    rw [hsq, hd.s56_E_sq huE, one_mul]
  · intro h
    have hε1 : d.s56Eps u = d.z := by
      rw [hεu, hεw, h]
      calc d.z * d.s56Eps v * d.s56Eps v = d.z * (d.s56Eps v * d.s56Eps v) := by group
        _ = d.z := by rw [hεε, mul_one]
    rcases s56y_mem_sup_zpowers (A := d.E) (fun a ha => hz.cen ha) hz₀sq huS with
      huE | ⟨e, he, hue⟩
    · exfalso
      have := (hd.s56_V_eps_eq_one_iff h49 huV).2 huE
      rw [hε1] at this
      exact hd.s56_z_ne_one this
    · have huu : u * u = z₀ * z₀ := by
        rw [hue]
        calc z₀ * e * (z₀ * e) = z₀ * (e * z₀) * e := by group
          _ = z₀ * (z₀ * e) * e := by rw [← hz.cen he]
          _ = (z₀ * z₀) * (e * e) := by group
          _ = z₀ * z₀ := by rw [hd.s56_E_sq he, mul_one]
      rw [hsq, huu]

theorem Hyp.s56_V_sq_mem_of_sq_eq_one (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (h1 : z₀ * z₀ = 1) {v : G} (hv : v ∈ d.s56V) : v * v ∈ zpowers d.z := by
  have hE : v * v ∈ d.E := hd.s56_Q2_sq_mem_E_all h49 v hv.2
  have hmem : v * v ∈ d.E ⊓ centralizer (d.s56J : Set G) := by
    refine mem_inf.2 ⟨hE, ?_⟩
    rw [mem_centralizer_iff]
    intro j hj
    have hjε := hd.s56_J_comm_E hj (hd.s56_V_eps_mem_E hv)
    have hsq : j * (v * v) * j⁻¹ = v * v := by
      rcases hd.s56_mem_zpowers_z hjε with h | h
      · exact (hd.s56_J_conj_V_sq h49 hz hj hv).1 (mul_inv_eq_one.1 h)
      · rw [(hd.s56_J_conj_V_sq h49 hz hj hv).2 (mul_inv_eq_iff_eq_mul.1 h), h1, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 hsq
  rwa [hd.s56_E_inf_centralizer_J] at hmem

theorem Hyp.s56_V_sq_eps_mem_of_sq_eq_z (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (h1 : z₀ * z₀ = d.z) {v : G} (hv : v ∈ d.s56V) :
    v * v * d.s56Eps v ∈ zpowers d.z := by
  have hε := hd.s56_V_eps_mem_E hv
  have hvvE : v * v ∈ d.E := hd.s56_Q2_sq_mem_E_all h49 v hv.2
  have hE : v * v * d.s56Eps v ∈ d.E := mul_mem hvvE hε
  have hmem : v * v * d.s56Eps v ∈ d.E ⊓ centralizer (d.s56J : Set G) := by
    refine mem_inf.2 ⟨hE, ?_⟩
    rw [mem_centralizer_iff]
    intro j hj
    have hjε := hd.s56_J_comm_E hj hε
    have hconj : j * (v * v * d.s56Eps v) * j⁻¹ = v * v * d.s56Eps v := by
      have e : j * (v * v * d.s56Eps v) * j⁻¹ = (j * (v * v) * j⁻¹) * (j * d.s56Eps v * j⁻¹) := by
        group
      rw [e]
      rcases hd.s56_mem_zpowers_z hjε with h | h
      · rw [(hd.s56_J_conj_V_sq h49 hz hj hv).1 (mul_inv_eq_one.1 h), mul_inv_eq_one.1 h]
      · have h' := mul_inv_eq_iff_eq_mul.1 h
        rw [(hd.s56_J_conj_V_sq h49 hz hj hv).2 h', h1, h']
        have hzvv : d.z * (v * v) = (v * v) * d.z := hd.s56_E_comm hd.s56_z_mem_E hvvE
        calc d.z * (v * v) * (d.z * d.s56Eps v) = (v * v) * d.z * (d.z * d.s56Eps v) := by
              rw [hzvv]
          _ = (v * v) * (d.z * d.z) * d.s56Eps v := by group
          _ = v * v * d.s56Eps v := by rw [hd.s56_z_sq, mul_one]
    exact mul_inv_eq_iff_eq_mul.1 hconj
  rwa [hd.s56_E_inf_centralizer_J] at hmem

theorem Hyp.s56_V_comm_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {a b : G} (ha : a ∈ d.s56V) (hb : b ∈ d.s56V) : a * b * a⁻¹ * b⁻¹ ∈ zpowers d.z := by
  have hE : a * b * a⁻¹ * b⁻¹ ∈ d.E := hd.s56_Q2_comm_mem_E h49 ha.2 hb.2
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ d.E ⊓ centralizer (d.s56J : Set G) := by
    refine mem_inf.2 ⟨hE, ?_⟩
    rw [mem_centralizer_iff]
    intro j hj
    have hua := hd.s56_J_comm_Q2_mem h49 hz.mem_Q2 hz.eps hz.dich hj ha.2
    have hub := hd.s56_J_comm_Q2_mem h49 hz.mem_Q2 hz.eps hz.dich hj hb.2
    obtain ⟨ua, huadef⟩ : ∃ ua, ua = j * a * j⁻¹ * a⁻¹ := ⟨_, rfl⟩
    obtain ⟨ub, hubdef⟩ : ∃ ub, ub = j * b * j⁻¹ * b⁻¹ := ⟨_, rfl⟩
    rw [← huadef] at hua
    rw [← hubdef] at hub
    have huaV : ua ∈ d.s56V := hd.s56_S_le_V h49 hz hua
    have hubV : ub ∈ d.s56V := hd.s56_S_le_V h49 hz hub
    have hca : ua * a = a * ua := hd.s56_S_comm_V h49 hz hua ha
    have hcb : ub * b = b * ub := hd.s56_S_comm_V h49 hz hub hb
    have hja : j * a * j⁻¹ = a * ua := by
      calc j * a * j⁻¹ = ua * a := by rw [huadef]; group
        _ = a * ua := hca
    have hjb : j * b * j⁻¹ = b * ub := by
      calc j * b * j⁻¹ = ub * b := by rw [hubdef]; group
        _ = b * ub := hcb
    have key : j * (a * b * a⁻¹ * b⁻¹) * j⁻¹ = a * b * a⁻¹ * b⁻¹ := by
      have e : j * (a * b * a⁻¹ * b⁻¹) * j⁻¹ = ⁅j * a * j⁻¹, j * b * j⁻¹⁆ := by
        rw [commutatorElement_def]; group
      rw [e, hja, hjb, S56.comm_mul_central hca (hd.s56_S_comm_V h49 hz hua hb)
        (hd.s56_S_comm_V h49 hz hua hubV) (hd.s56_S_comm_V h49 hz hub ha) hcb,
        commutatorElement_def]
    exact mul_inv_eq_iff_eq_mul.1 key
  rwa [hd.s56_E_inf_centralizer_J] at hmem

theorem Hyp.s56_V_center_cases (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) :
    (∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) ∨
      ∀ v ∈ d.s56V, ((∀ w ∈ d.s56V, v * w = w * v) ↔ v ∈ d.E ⊔ zpowers z₀) := by
  have hxM := hd.s56_x5_mem_M
  have hxt := hd.s56_x5_comm_t
  set R : Subgroup G := (Subgroup.center d.s56V).map hd.s56EpsHom with hR
  have hmemR : ∀ s, s ∈ R ↔
      ∃ v ∈ d.s56V, (∀ w ∈ d.s56V, v * w = w * v) ∧ d.s56Eps v = s := by
    intro s
    rw [hR, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.1, v.2, fun w hw => ?_, rfl⟩
      have := (Subgroup.mem_center_iff.1 hv) ⟨w, hw⟩
      exact (congrArg Subtype.val this).symm
    · rintro ⟨v, hv, hc, rfl⟩
      refine ⟨⟨v, hv⟩, Subgroup.mem_center_iff.2 fun w => ?_, rfl⟩
      exact Subtype.ext (hc w.1 w.2).symm
  have hRE : R ≤ d.E := by
    intro s hs
    obtain ⟨v, hv, -, rfl⟩ := (hmemR s).1 hs
    exact hd.s56_V_eps_mem_E hv
  have hzR : zpowers d.z ≤ R :=
    zpowers_le.2 ((hmemR _).2 ⟨z₀, hz.mem_V, fun w hw => (hz.comm_V hw).symm, hz.eps⟩)
  have hcon : ∀ g ∈ d.M, g * d.t = d.t * g → ∀ k ∈ R, g * k * g⁻¹ ∈ R := by
    intro g hg hgt k hk
    obtain ⟨v, hv, hc, rfl⟩ := (hmemR k).1 hk
    refine (hmemR _).2 ⟨g * v * g⁻¹, hd.s56_V_conj_mem h49 hg hv, ?_, hd.s56_eps_conj hgt v⟩
    intro w hw
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 (inv_mem hg) hw
    have h := hc _ hw'
    calc g * v * g⁻¹ * w = g * (v * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g⁻¹⁻¹) * v) * g⁻¹ := by rw [h]
      _ = w * (g * v * g⁻¹) := by group
  have hxR : d.x₅ ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hcon _ hxM hxt k hk, fun hk => ?_⟩
    have hxt' : d.x₅⁻¹ * d.t = d.t * d.x₅⁻¹ := (show Commute d.x₅ d.t from hxt).inv_left.eq
    have := hcon d.x₅⁻¹ (inv_mem hxM) hxt' _ hk
    simpa [mul_assoc] using this
  rcases hd.s56_stable_sub_E hzR hRE hxR with hRz | hRE'
  · right
    intro v hv
    constructor
    · intro hc
      have hεv : d.s56Eps v ∈ zpowers d.z := by
        rw [← hRz]; exact (hmemR _).2 ⟨v, hv, hc, rfl⟩
      rcases hd.s56_mem_zpowers_z hεv with h | h
      · exact mem_sup_left ((hd.s56_V_eps_eq_one_iff h49 hv).1 h)
      · have hvz : v * z₀⁻¹ ∈ d.E := by
          rw [← hd.s56_V_eps_eq_one_iff h49 (mul_mem hv (inv_mem hz.mem_V)),
            hd.s56_eps_mul_Q2' hv.2 (inv_mem hz.mem_V).2, hd.s56_eps_inv_Q2 hz.mem_Q2, hz.eps, h]
          exact hd.s56_z_sq
        have e : v = (v * z₀⁻¹) * z₀ := by group
        rw [e]
        exact mul_mem (mem_sup_left hvz) (mem_sup_right (mem_zpowers _))
    · intro hs w hw
      exact hd.s56_S_comm_V h49 hz hs hw
  · left
    intro a ha b hb
    have hεa : d.s56Eps a ∈ R := by rw [hRE']; exact hd.s56_V_eps_mem_E ha
    obtain ⟨w, hw, hwc, hwε⟩ := (hmemR _).1 hεa
    have hawE : a * w⁻¹ ∈ d.E := by
      rw [← hd.s56_V_eps_eq_one_iff h49 (mul_mem ha (inv_mem hw)),
        hd.s56_eps_mul_Q2' ha.2 (inv_mem hw).2, hd.s56_eps_inv_Q2 hw.2, hwε]
      exact hd.s56_E_sq (hd.s56_V_eps_mem_E ha)
    have hac : ∀ c ∈ d.s56V, a * c = c * a := by
      intro c hc
      have h1 : a = (a * w⁻¹) * w := by group
      rw [h1]
      calc (a * w⁻¹) * w * c = (a * w⁻¹) * (w * c) := by group
        _ = (a * w⁻¹) * (c * w) := by rw [hwc c hc]
        _ = ((a * w⁻¹) * c) * w := by group
        _ = (c * (a * w⁻¹)) * w := by rw [← s56_V_comm_E hc hawE]
        _ = c * ((a * w⁻¹) * w) := by group
    exact hac b hb

theorem Hyp.s56_V_elem_abelian (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (hab : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) (h1 : z₀ * z₀ = 1) :
    ∀ v ∈ d.s56V, v * v = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxM := hd.s56_x5_mem_M
  have hXV : zpowers d.x₅ ≤ normalizer (d.s56V : Set G) :=
    hd.s56_X_le_M.trans (hd.s56_M_le_normalizer_V h49)
  let Ω : Subgroup G :=
    { carrier := {v | v ∈ d.s56V ∧ v * v = 1}
      one_mem' := ⟨one_mem _, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab a ha b hb]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha1, hb1, mul_one]
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨inv_mem ha, ?_⟩
        calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          _ = 1 := by rw [ha1, inv_one] }
  have hcommΩ : ⁅d.s56V, zpowers d.x₅⁆ ≤ Ω := by
    refine Subgroup.commutator_le.2 fun v hv g hg => ?_
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    have hgv : g * v⁻¹ * g⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hgM (inv_mem hv)
    have hcv : ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    have hvv : v * v ∈ zpowers d.z := hd.s56_V_sq_mem_of_sq_eq_one h49 hz h1 hv
    have hfix : g * (v * v) * g⁻¹ = v * v := by
      rw [hd.s56_M_comm_zpowers hgM hvv]; group
    have hw : (g * v⁻¹ * g⁻¹) * (g * v⁻¹ * g⁻¹) = (v * v)⁻¹ := by
      calc (g * v⁻¹ * g⁻¹) * (g * v⁻¹ * g⁻¹) = (g * (v * v) * g⁻¹)⁻¹ := by group
        _ = (v * v)⁻¹ := by rw [hfix]
    rw [hcv]
    refine ⟨mul_mem hv hgv, ?_⟩
    calc v * (g * v⁻¹ * g⁻¹) * (v * (g * v⁻¹ * g⁻¹))
        = v * ((g * v⁻¹ * g⁻¹) * v) * (g * v⁻¹ * g⁻¹) := by group
      _ = v * (v * (g * v⁻¹ * g⁻¹)) * (g * v⁻¹ * g⁻¹) := by rw [hab _ hgv v hv]
      _ = (v * v) * ((g * v⁻¹ * g⁻¹) * (g * v⁻¹ * g⁻¹)) := by group
      _ = 1 := by rw [hw]; group
  intro v hv
  obtain ⟨c, hc, k, hk, rfl⟩ := S56.coprime_decomp_mem (p := 2) (r := 5) (by norm_num)
    (hd.s56_V_isPGroup h49) hd.s56_X_isPGroup hXV hv
  have hcΩ : c * c = 1 := (hcommΩ hc).2
  have hcV : c ∈ d.s56V := (hcommΩ hc).1
  obtain ⟨hkV, hkX⟩ := mem_inf.1 hk
  have hkZ : k ∈ zpowers d.z ⊔ zpowers z₀ := by
    rw [← hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich]
    exact mem_inf.2 ⟨hkV.1, hkX⟩
  have hkk : k * k = 1 := by
    rcases s56y_mem_sup_zpowers (A := zpowers d.z) (y := z₀)
      (fun a ha => hd.s56_M_comm_zpowers hz.mem_M ha) hz.sq hkZ with h | ⟨a, ha, rfl⟩
    · exact hd.s56_zpowers_sq h
    · calc z₀ * a * (z₀ * a) = z₀ * (a * z₀) * a := by group
        _ = z₀ * (z₀ * a) * a := by rw [← hd.s56_M_comm_zpowers hz.mem_M ha]
        _ = (z₀ * z₀) * (a * a) := by group
        _ = 1 := by rw [h1, hd.s56_zpowers_sq ha, mul_one]
  calc c * k * (c * k) = c * (k * c) * k := by group
    _ = c * (c * k) * k := by rw [← hab c hcV k hkV]
    _ = (c * c) * (k * k) := by group
    _ = 1 := by rw [hcΩ, hkk, mul_one]

theorem Hyp.s56_V_shape (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    Nat.card d.s56V = 2 ^ 10 ∧ d.M ≤ normalizer (d.s56V : Set G) ∧ d.E ≤ d.s56V ∧
    z₀ ∈ d.s56V ∧ (∀ s ∈ d.E ⊔ zpowers z₀, ∀ v ∈ d.s56V, s * v = v * s) ∧
    (∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b * a⁻¹ * b⁻¹ ∈ zpowers d.z) ∧
    (z₀ * z₀ = 1 → ∀ v ∈ d.s56V, v * v ∈ zpowers d.z) ∧
    (z₀ * z₀ = d.z → ∀ v ∈ d.s56V, v * v * d.s56Eps v ∈ zpowers d.z) ∧
    ((∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) ∨
      ∀ v ∈ d.s56V, ((∀ w ∈ d.s56V, v * w = w * v) ↔ v ∈ d.E ⊔ zpowers z₀)) ∧
    ((∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) → z₀ * z₀ = 1 → ∀ v ∈ d.s56V, v * v = 1) :=
  ⟨hd.s56_card_V h49 hz, hd.s56_M_le_normalizer_V h49, hd.s56_E_le_V h49, hz.mem_V,
    fun _ hs _ hv => hd.s56_S_comm_V h49 hz hs hv,
    fun _ ha _ hb => hd.s56_V_comm_mem h49 hz ha hb,
    fun h1 _ hv => hd.s56_V_sq_mem_of_sq_eq_one h49 hz h1 hv,
    fun h1 _ hv => hd.s56_V_sq_eps_mem_of_sq_eq_z h49 hz h1 hv,
    hd.s56_V_center_cases h49 hz,
    fun hab h1 => hd.s56_V_elem_abelian h49 hz hab h1⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
