module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaAPhi
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaAAlg
import CFSG.LocalAnalysis.EvenBN.Tits.S56P11

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Model

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def kk (d : Data G) (x q : G) : ZMod 2 := eb d x ⬝ᵥ fb d q

@[expose] noncomputable def ep (d : Data G) (z₀ x q : G) : G :=
  x * q * x⁻¹ * q⁻¹ * (z₀ ^ (kk d x q).val)⁻¹

@[expose] noncomputable def Bf (d : Data G) (z₀ x q : G) : W4 := wcoord d (ep d z₀ x q)

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem z0_pow_mem (hz : d.S56Z0 z₀) (a b : ZMod 2) :
    z₀ ^ a.val * z₀ ^ b.val * (z₀ ^ (a + b).val)⁻¹ ∈ zpowers d.z := by
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [one_mem]
  · simp [one_mem]
  · simp [one_mem]
  · simp [h11]
    exact hz.sq

theorem zpow_mem_E' (hd : d.Hyp) (n : ℕ) : d.z ^ n ∈ d.E := pow_mem hd.s56_z_mem_E n

theorem zpow_mem_zp (n : ℕ) : d.z ^ n ∈ zpowers d.z := pow_mem (mem_zpowers _) n

theorem J_comm_t (hd : d.Hyp) {q : G} (hq : q ∈ d.s56J) : q * d.t = d.t * q :=
  hd.L_comm_t (Data.s56_J_le_L d hq)

theorem J_comm_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {q : G}
    (hq : q ∈ d.s56J) : q * z₀ = z₀ * q :=
  hz.comm_Q q (hd.s56_J_le_Q h49 hq)

theorem comm_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) {x q : G} (hx : x ∈ d.s56V)
    (hq : q ∈ d.s56J) : x * q * x⁻¹ * q⁻¹ ∈ d.s56V := by
  have h1 : q * x⁻¹ * q⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 (hd.s56_J_le_M hq) (inv_mem hx)
  have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [e]
  exact mul_mem hx h1

theorem eps_comm (h49 : d.Thm49Statement) (hd : d.Hyp) {x q : G} (hx : x ∈ d.s56V)
    (hq : q ∈ d.s56J) : d.s56Eps (x * q * x⁻¹ * q⁻¹) = d.z ^ (kk d x q).val := by
  have hxQ2 : x ∈ d.s56Q2 := hx.2
  have h1 : q * x⁻¹ * q⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 (hd.s56_J_le_M hq) (inv_mem hx)
  have e1 : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [e1, hd.s56_eps_mul_Q2' hxQ2 h1.2, hd.s56_eps_conj (J_comm_t hd hq) x⁻¹,
    hd.s56_eps_inv_Q2 hxQ2]
  have heE : d.s56Eps x ∈ d.E := hd.s56_V_eps_mem_E hx
  have hphi := phi_mem hd hq heE
  have hee : d.s56Eps x * d.s56Eps x = 1 := hd.s56_E_sq heE
  have hκ : kk d x q = phi d q (d.s56Eps x) := by
    rw [kk, phi_eps hd hq hx, dotProduct_comm]
  rw [hκ]
  have e2 : q * d.s56Eps x * q⁻¹ = d.z ^ (phi d q (d.s56Eps x)).val * d.s56Eps x := by
    calc q * d.s56Eps x * q⁻¹ = (q * d.s56Eps x * q⁻¹ * (d.s56Eps x)⁻¹) * d.s56Eps x := by group
      _ = _ := by rw [hphi]
  rw [e2]
  have hc : d.s56Eps x * d.z ^ (phi d q (d.s56Eps x)).val =
      d.z ^ (phi d q (d.s56Eps x)).val * d.s56Eps x :=
    hd.s56_E_comm heE (zpow_mem_E' hd _)
  calc d.s56Eps x * (d.z ^ (phi d q (d.s56Eps x)).val * d.s56Eps x)
      = (d.s56Eps x * d.z ^ (phi d q (d.s56Eps x)).val) * d.s56Eps x := by group
    _ = (d.z ^ (phi d q (d.s56Eps x)).val * d.s56Eps x) * d.s56Eps x := by rw [hc]
    _ = d.z ^ (phi d q (d.s56Eps x)).val * (d.s56Eps x * d.s56Eps x) := by group
    _ = d.z ^ (phi d q (d.s56Eps x)).val := by rw [hee, mul_one]


theorem eps_z0_pow (hd : d.Hyp) (hz : d.S56Z0 z₀) (a : ZMod 2) :
    d.s56Eps (z₀ ^ a.val) = d.z ^ a.val := by
  rcases zmod2_cases a with rfl | rfl
  · simp [hd.s56_eps_one]
  · simp [hz.eps]

theorem ep_mem (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {x q : G}
    (hx : x ∈ d.s56V) (hq : q ∈ d.s56J) : ep d z₀ x q ∈ d.E := by
  have hD := comm_mem_V h49 hd hx hq
  have hzp : z₀ ^ (kk d x q).val ∈ d.s56V := pow_mem hz.mem_V _
  have hu : ep d z₀ x q ∈ d.s56V := mul_mem hD (inv_mem hzp)
  refine (hd.s56_V_eps_eq_one_iff h49 hu).1 ?_
  show d.s56Eps (x * q * x⁻¹ * q⁻¹ * (z₀ ^ (kk d x q).val)⁻¹) = 1
  rw [hd.s56_eps_mul_Q2' hD.2 (inv_mem hzp).2, eps_comm h49 hd hx hq,
    hd.s56_eps_inv_Q2 hzp.2, eps_z0_pow hd hz]
  exact hd.s56_zpowers_sq (zpow_mem_zp _)

theorem comm_eq (d : Data G) (z₀ x q : G) :
    x * q * x⁻¹ * q⁻¹ = ep d z₀ x q * z₀ ^ (kk d x q).val := by
  unfold ep
  rw [inv_mul_cancel_right]

theorem V_comm_z0_pow (hz : d.S56Z0 z₀) {x : G} (hx : x ∈ d.s56V) (n : ℕ) :
    x * z₀ ^ n = z₀ ^ n * x :=
  (Commute.pow_right (show Commute x z₀ from hz.comm_V hx) n).eq

theorem E_comm_z0_pow (hz : d.S56Z0 z₀) {e : G} (he : e ∈ d.E) (n : ℕ) :
    z₀ ^ n * e = e * z₀ ^ n :=
  (Commute.pow_left (show Commute z₀ e from hz.cen he) n).eq

theorem ep_mul_x (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {x x' q : G}
    (hx : x ∈ d.s56V) (hx' : x' ∈ d.s56V) (hq : q ∈ d.s56J) :
    ∃ w ∈ zpowers d.z, ep d z₀ (x * x') q = ep d z₀ x' q * ep d z₀ x q * w := by
  have hκ : kk d (x * x') q = kk d x' q + kk d x q := by
    unfold kk
    rw [eb_mul hd hx hx', add_dotProduct, add_comm]
  refine ⟨z₀ ^ (kk d x' q).val * z₀ ^ (kk d x q).val * (z₀ ^ (kk d x' q + kk d x q).val)⁻¹,
    z0_pow_mem hz _ _, ?_⟩
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁, E₁ = ep d z₀ x q := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂def⟩ : ∃ E₂, E₂ = ep d z₀ x' q := ⟨_, rfl⟩
  have hE₁ : E₁ ∈ d.E := hE₁def ▸ ep_mem h49 hd hz hx hq
  have hE₂ : E₂ ∈ d.E := hE₂def ▸ ep_mem h49 hd hz hx' hq
  have hD₁ : x * q * x⁻¹ * q⁻¹ = E₁ * z₀ ^ (kk d x q).val := by
    rw [hE₁def]; exact comm_eq d z₀ x q
  have hD₂ : x' * q * x'⁻¹ * q⁻¹ = E₂ * z₀ ^ (kk d x' q).val := by
    rw [hE₂def]; exact comm_eq d z₀ x' q
  have hD₃ : x * x' * q * (x * x')⁻¹ * q⁻¹ =
      (x * (x' * q * x'⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by
    group
  have hc₂ : x * (E₂ * z₀ ^ (kk d x' q).val) * x⁻¹ = E₂ * z₀ ^ (kk d x' q).val := by
    have h1 : x * E₂ = E₂ * x := Data.s56_V_comm_E hx hE₂
    have h2 : x * z₀ ^ (kk d x' q).val = z₀ ^ (kk d x' q).val * x := V_comm_z0_pow hz hx _
    calc x * (E₂ * z₀ ^ (kk d x' q).val) * x⁻¹ = (x * E₂) * z₀ ^ (kk d x' q).val * x⁻¹ := by group
      _ = E₂ * (x * z₀ ^ (kk d x' q).val) * x⁻¹ := by rw [h1]; group
      _ = E₂ * (z₀ ^ (kk d x' q).val * x) * x⁻¹ := by rw [h2]
      _ = E₂ * z₀ ^ (kk d x' q).val := by group
  have hZE : z₀ ^ (kk d x' q).val * E₁ = E₁ * z₀ ^ (kk d x' q).val := E_comm_z0_pow hz hE₁ _
  have hD₃' : x * x' * q * (x * x')⁻¹ * q⁻¹ =
      E₂ * E₁ * (z₀ ^ (kk d x' q).val * z₀ ^ (kk d x q).val) := by
    rw [hD₃, hD₂, hc₂, hD₁]
    calc E₂ * z₀ ^ (kk d x' q).val * (E₁ * z₀ ^ (kk d x q).val)
        = E₂ * (z₀ ^ (kk d x' q).val * E₁) * z₀ ^ (kk d x q).val := by group
      _ = E₂ * (E₁ * z₀ ^ (kk d x' q).val) * z₀ ^ (kk d x q).val := by rw [hZE]
      _ = _ := by group
  have hL : ep d z₀ (x * x') q =
      (x * x' * q * (x * x')⁻¹ * q⁻¹) * (z₀ ^ (kk d (x * x') q).val)⁻¹ := rfl
  rw [hL, hκ, hD₃', ← hE₁def, ← hE₂def]
  group


theorem J_comm_z0_pow (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {q : G}
    (hq : q ∈ d.s56J) (n : ℕ) : q * z₀ ^ n = z₀ ^ n * q :=
  (Commute.pow_right (show Commute q z₀ from J_comm_z0 h49 hd hz hq) n).eq

theorem ep_mul_q (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {x q q' : G}
    (hx : x ∈ d.s56V) (hq : q ∈ d.s56J) (hq' : q' ∈ d.s56J) :
    ∃ w ∈ zpowers d.z, ep d z₀ x (q * q') = ep d z₀ x q * ep d z₀ x q' * w := by
  have hκ : kk d x (q * q') = kk d x q + kk d x q' := by
    unfold kk
    rw [fb_mul hd hq hq', dotProduct_add]
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁, E₁ = ep d z₀ x q := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂def⟩ : ∃ E₂, E₂ = ep d z₀ x q' := ⟨_, rfl⟩
  have hE₁ : E₁ ∈ d.E := hE₁def ▸ ep_mem h49 hd hz hx hq
  have hE₂ : E₂ ∈ d.E := hE₂def ▸ ep_mem h49 hd hz hx hq'
  have hD₁ : x * q * x⁻¹ * q⁻¹ = E₁ * z₀ ^ (kk d x q).val := by
    rw [hE₁def]; exact comm_eq d z₀ x q
  have hD₂ : x * q' * x⁻¹ * q'⁻¹ = E₂ * z₀ ^ (kk d x q').val := by
    rw [hE₂def]; exact comm_eq d z₀ x q'
  have hD₃ : x * (q * q') * x⁻¹ * (q * q')⁻¹ =
      (x * q * x⁻¹ * q⁻¹) * (q * (x * q' * x⁻¹ * q'⁻¹) * q⁻¹) := by group
  obtain ⟨c, hcdef⟩ : ∃ c, c = q * E₂ * q⁻¹ * E₂⁻¹ := ⟨_, rfl⟩
  have hc : c ∈ zpowers d.z := hcdef ▸ hd.s56_J_comm_E hq hE₂
  have hcE : c ∈ d.E := hd.s56_zpowers_le_E hc
  have hqE₂ : q * E₂ * q⁻¹ = c * E₂ := by rw [hcdef]; group
  have hqz : q * z₀ ^ (kk d x q').val * q⁻¹ = z₀ ^ (kk d x q').val := by
    rw [J_comm_z0_pow h49 hd hz hq]; group
  have hqD : q * (E₂ * z₀ ^ (kk d x q').val) * q⁻¹ = c * E₂ * z₀ ^ (kk d x q').val := by
    calc q * (E₂ * z₀ ^ (kk d x q').val) * q⁻¹
        = (q * E₂ * q⁻¹) * (q * z₀ ^ (kk d x q').val * q⁻¹) := by group
      _ = c * E₂ * z₀ ^ (kk d x q').val := by rw [hqE₂, hqz]
  have hZc : z₀ ^ (kk d x q).val * c = c * z₀ ^ (kk d x q).val := E_comm_z0_pow hz hcE _
  have hZE : z₀ ^ (kk d x q).val * E₂ = E₂ * z₀ ^ (kk d x q).val := E_comm_z0_pow hz hE₂ _
  have hcE₂ : c * E₂ = E₂ * c := hd.s56_E_comm hcE hE₂
  have hD₃' : x * (q * q') * x⁻¹ * (q * q')⁻¹ =
      E₁ * E₂ * (c * (z₀ ^ (kk d x q).val * z₀ ^ (kk d x q').val)) := by
    rw [hD₃, hD₂, hqD, hD₁]
    calc E₁ * z₀ ^ (kk d x q).val * (c * E₂ * z₀ ^ (kk d x q').val)
        = E₁ * (z₀ ^ (kk d x q).val * c) * E₂ * z₀ ^ (kk d x q').val := by group
      _ = E₁ * (c * z₀ ^ (kk d x q).val) * E₂ * z₀ ^ (kk d x q').val := by rw [hZc]
      _ = E₁ * c * (z₀ ^ (kk d x q).val * E₂) * z₀ ^ (kk d x q').val := by group
      _ = E₁ * c * (E₂ * z₀ ^ (kk d x q).val) * z₀ ^ (kk d x q').val := by rw [hZE]
      _ = E₁ * (c * E₂) * z₀ ^ (kk d x q).val * z₀ ^ (kk d x q').val := by group
      _ = E₁ * (E₂ * c) * z₀ ^ (kk d x q).val * z₀ ^ (kk d x q').val := by rw [hcE₂]
      _ = _ := by group
  refine ⟨c * (z₀ ^ (kk d x q).val * z₀ ^ (kk d x q').val *
    (z₀ ^ (kk d x q + kk d x q').val)⁻¹), mul_mem hc (z0_pow_mem hz _ _), ?_⟩
  have hL : ep d z₀ x (q * q') =
      (x * (q * q') * x⁻¹ * (q * q')⁻¹) * (z₀ ^ (kk d x (q * q')).val)⁻¹ := rfl
  rw [hL, hκ, hD₃', ← hE₁def, ← hE₂def]
  group

theorem wcoord_one (hd : d.Hyp) : wcoord d (1 : G) = 0 := by
  funext i
  simp [wcoord, ecoord_one hd]

theorem Bf_eq_zero_of_fb (hd : d.Hyp) {x q : G} (hx : x ∈ d.s56V) (hq : q ∈ d.s56J)
    (hfb : fb d q = 0) : Bf d z₀ x q = 0 := by
  have hqE : q ∈ d.E := (fb_eq_zero_iff hd hq).1 hfb
  have hκ : kk d x q = 0 := by
    unfold kk
    rw [hfb, dotProduct_zero]
  have hcomm : x * q = q * x := Data.s56_V_comm_E hx hqE
  have h1 : ep d z₀ x q = 1 := by
    unfold ep
    rw [hκ, hcomm]
    simp
  unfold Bf
  rw [h1, wcoord_one hd]

theorem Bf_eq_zero_of_eb (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {x q : G}
    (hx : x ∈ d.s56V) (hq : q ∈ d.s56J) (heb : eb d x = 0) : Bf d z₀ x q = 0 := by
  have hεz : d.s56Eps x ∈ zpowers d.z := (eb_eq_zero_iff hd hx).1 heb
  obtain ⟨m, hm⟩ : ∃ m : ZMod 2, d.s56Eps x = d.z ^ m.val := ⟨zc _, zpow_zc hd hεz⟩
  have hzm : z₀ ^ m.val ∈ d.s56V := pow_mem hz.mem_V _
  have he₀V : x * z₀ ^ m.val ∈ d.s56V := mul_mem hx hzm
  have he₀E : x * z₀ ^ m.val ∈ d.E := by
    refine (hd.s56_V_eps_eq_one_iff h49 he₀V).1 ?_
    rw [hd.s56_eps_mul_Q2' hx.2 hzm.2, eps_z0_pow hd hz m, hm]
    exact hd.s56_zpowers_sq (zpow_mem_zp _)
  obtain ⟨e₀, he₀def⟩ : ∃ e₀, e₀ = x * z₀ ^ m.val := ⟨_, rfl⟩
  have hxe : x = e₀ * (z₀ ^ m.val)⁻¹ := by rw [he₀def]; group
  have he₀E' : e₀ ∈ d.E := he₀def ▸ he₀E
  have hcomm_q : q * z₀ ^ m.val = z₀ ^ m.val * q := J_comm_z0_pow h49 hd hz hq _
  have hZq : (z₀ ^ m.val)⁻¹ * q * z₀ ^ m.val = q := by
    calc (z₀ ^ m.val)⁻¹ * q * z₀ ^ m.val = (z₀ ^ m.val)⁻¹ * (q * z₀ ^ m.val) := by group
      _ = (z₀ ^ m.val)⁻¹ * (z₀ ^ m.val * q) := by rw [hcomm_q]
      _ = q := by group
  have hD : x * q * x⁻¹ * q⁻¹ = (q * e₀ * q⁻¹ * e₀⁻¹)⁻¹ := by
    calc x * q * x⁻¹ * q⁻¹ = e₀ * ((z₀ ^ m.val)⁻¹ * q * z₀ ^ m.val) * e₀⁻¹ * q⁻¹ := by
          rw [hxe]; group
      _ = e₀ * q * e₀⁻¹ * q⁻¹ := by rw [hZq]
      _ = (q * e₀ * q⁻¹ * e₀⁻¹)⁻¹ := by group
  have hDz : x * q * x⁻¹ * q⁻¹ ∈ zpowers d.z := by
    rw [hD]
    exact inv_mem (hd.s56_J_comm_E hq he₀E')
  have hκ : kk d x q = 0 := by
    unfold kk
    rw [heb, zero_dotProduct]
  have hep : ep d z₀ x q = x * q * x⁻¹ * q⁻¹ := by
    unfold ep
    rw [hκ]
    simp
  unfold Bf
  rw [hep]
  exact (wcoord_eq_zero_iff hd (hd.s56_zpowers_le_E hDz)).2 hDz

theorem Bf_conj (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {g : G} (hgL : g ∈ d.L)
    (hgM : g ∈ d.M) (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hAz : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hA : ∀ j : Fin 5, g * d.pv (basisV j) * g⁻¹ = crdE d (fun i => A i j)) {x q : G}
    (hx : x ∈ d.s56V) (hq : q ∈ d.s56J) :
    Bf d z₀ (g * x * g⁻¹) (g * q * g⁻¹) = (Matrix.of fun i j : Fin 4 => A i.succ j.succ) *ᵥ
      Bf d z₀ x q := by
  have hgt : g * d.t = d.t * g := hd.L_comm_t hgL
  obtain ⟨hx', hebx⟩ := eb_conj hd hgM hgt A hAz hA h49 hx
  obtain ⟨hq', hfbq⟩ := fb_conj hd hgL hgM A hAz hA hq
  set A4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun i j : Fin 4 => A i.succ j.succ with hA4
  have hκ : kk d (g * x * g⁻¹) (g * q * g⁻¹) = kk d x q := by
    unfold kk
    rw [hebx]
    calc (A4 *ᵥ eb d x) ⬝ᵥ fb d (g * q * g⁻¹) = fb d (g * q * g⁻¹) ⬝ᵥ (A4 *ᵥ eb d x) := dotProduct_comm _ _
      _ = (fb d (g * q * g⁻¹) ᵥ* A4) ⬝ᵥ eb d x := Matrix.dotProduct_mulVec _ _ _
      _ = (A4ᵀ *ᵥ fb d (g * q * g⁻¹)) ⬝ᵥ eb d x := by rw [Matrix.mulVec_transpose]
      _ = fb d q ⬝ᵥ eb d x := by rw [hfbq]
      _ = eb d x ⬝ᵥ fb d q := dotProduct_comm _ _
  have hE := ep_mem h49 hd hz hx hq
  have hc₀ : g * z₀ * g⁻¹ * z₀⁻¹ ∈ zpowers d.z := hd.s56_M_comm_z0 h49 hz hgM
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀, c₀ = g * z₀ * g⁻¹ * z₀⁻¹ := ⟨_, rfl⟩
  have hc₀' : c₀ ∈ zpowers d.z := hc₀def ▸ hc₀
  have hgz : g * z₀ * g⁻¹ = c₀ * z₀ := by rw [hc₀def]; group
  have hgZ : ∀ n : ℕ, g * z₀ ^ n * g⁻¹ * (z₀ ^ n)⁻¹ ∈ zpowers d.z := by
    intro n
    have h1 : g * z₀ ^ n * g⁻¹ = (c₀ * z₀) ^ n := by rw [← hgz, conj_pow]
    have h2 : (c₀ * z₀) ^ n = c₀ ^ n * z₀ ^ n :=
      (Commute.mul_pow (show Commute c₀ z₀ from (hz.cen (hd.s56_zpowers_le_E hc₀')).symm) n)
    rw [h1, h2, mul_inv_cancel_right]
    exact pow_mem hc₀' n
  have hL : ep d z₀ (g * x * g⁻¹) (g * q * g⁻¹) =
      (g * ep d z₀ x q * g⁻¹) * (g * z₀ ^ (kk d x q).val * g⁻¹ * (z₀ ^ (kk d x q).val)⁻¹) := by
    have hD := comm_eq d z₀ x q
    have e1 : g * x * g⁻¹ * (g * q * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * q * g⁻¹)⁻¹ =
        g * (x * q * x⁻¹ * q⁻¹) * g⁻¹ := by group
    unfold ep
    rw [hκ, e1]
    have e2 : x * q * x⁻¹ * q⁻¹ = (x * q * x⁻¹ * q⁻¹ * (z₀ ^ (kk d x q).val)⁻¹) * z₀ ^ (kk d x q).val := by
      group
    conv_lhs => rw [e2]
    group
  unfold Bf
  rw [hL]
  have hwE : g * z₀ ^ (kk d x q).val * g⁻¹ * (z₀ ^ (kk d x q).val)⁻¹ ∈ d.E :=
    hd.s56_zpowers_le_E (hgZ _)
  obtain ⟨hgEE, hwc⟩ := wcoord_conj hd A hAz hA hE
  rw [wcoord_mul hd hgEE hwE, hwc, (wcoord_eq_zero_iff hd hwE).2 (hgZ _), add_zero]


theorem w4_add_self (a : W4) : a + a = 0 := by
  funext i
  have : ∀ y : ZMod 2, y + y = 0 := by decide
  exact this (a i)

theorem zpow_val_inj (hd : d.Hyp) {a b : ZMod 2} (h : d.z ^ a.val = d.z ^ b.val) : a = b := by
  have hz1 : d.z ≠ 1 := hd.s56_z_ne_one
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · exact absurd (by simpa using h) (Ne.symm hz1)
  · exact absurd (by simpa using h) hz1
  · rfl

theorem conj_comm_eq_inv {x q : G} (h : x * (q * q) = q * q * x) :
    q * (x * q * x⁻¹ * q⁻¹) * q⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by
  have h' : q⁻¹ * q⁻¹ * x⁻¹ = x⁻¹ * (q⁻¹ * q⁻¹) := by
    have := congrArg (fun y => y⁻¹) h
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  calc q * (x * q * x⁻¹ * q⁻¹) * q⁻¹ = q * x * q * (x⁻¹ * (q⁻¹ * q⁻¹)) := by group
    _ = q * x * q * (q⁻¹ * q⁻¹ * x⁻¹) := by rw [h']
    _ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by group

theorem trace_identity (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {x q : G}
    (hx : x ∈ d.s56V) (hq : q ∈ d.s56J) :
    fb d q ⬝ᵥ Bf d z₀ x q = zc (z₀ * z₀) * (fb d q ⬝ᵥ eb d x) := by
  have he' := ep_mem h49 hd hz hx hq
  unfold Bf
  rw [← phi_dot hd hq he']
  have hκeq : kk d x q = fb d q ⬝ᵥ eb d x := dotProduct_comm _ _
  rw [← hκeq]
  have hq2E : q * q ∈ d.E :=
    (fb_eq_zero_iff hd (mul_mem hq hq)).1 (by rw [fb_mul hd hq hq, w4_add_self])
  have hxqq : x * (q * q) = q * q * x := Data.s56_V_comm_E hx hq2E
  have hconj := conj_comm_eq_inv hxqq
  have hD := comm_eq d z₀ x q
  rw [hD] at hconj
  obtain ⟨e', he'def⟩ : ∃ e', e' = ep d z₀ x q := ⟨_, rfl⟩
  rw [← he'def] at hconj ⊢
  have he'E : e' ∈ d.E := he'def ▸ he'
  have hee : e' * e' = 1 := hd.s56_E_sq he'E
  have hinv : e'⁻¹ = e' := inv_eq_of_mul_eq_one_right hee
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = z₀ ^ (kk d x q).val := ⟨_, rfl⟩
  rw [← hZdef] at hconj
  have hZq : q * Z * q⁻¹ = Z := by
    rw [hZdef, J_comm_z0_pow h49 hd hz hq]; group
  have hZe : Z * e' = e' * Z := by rw [hZdef]; exact E_comm_z0_pow hz he'E _
  have hphi := phi_mem hd hq he'E
  obtain ⟨φ, hφdef⟩ : ∃ φ, φ = phi d q e' := ⟨_, rfl⟩
  rw [← hφdef] at hphi ⊢
  have hqe : q * e' * q⁻¹ = d.z ^ φ.val * e' := by
    calc q * e' * q⁻¹ = (q * e' * q⁻¹ * e'⁻¹) * e' := by group
      _ = d.z ^ φ.val * e' := by rw [hphi]
  have h1 : q * (e' * Z) * q⁻¹ = d.z ^ φ.val * e' * Z := by
    calc q * (e' * Z) * q⁻¹ = (q * e' * q⁻¹) * (q * Z * q⁻¹) := by group
      _ = d.z ^ φ.val * e' * Z := by rw [hqe, hZq]
  rw [h1, _root_.mul_inv_rev, hinv] at hconj
  have hze : d.z ^ φ.val * e' = e' * d.z ^ φ.val := hd.s56_E_comm (zpow_mem_E' hd _) he'E
  have hZi : Z⁻¹ * e' = e' * Z⁻¹ := by
    have : Commute Z e' := hZe
    exact this.inv_left.eq
  have h2 : d.z ^ φ.val * Z = Z⁻¹ := by
    have h3 : e' * (d.z ^ φ.val * Z) = e' * Z⁻¹ := by
      calc e' * (d.z ^ φ.val * Z) = (e' * d.z ^ φ.val) * Z := by group
        _ = (d.z ^ φ.val * e') * Z := by rw [hze]
        _ = Z⁻¹ * e' := hconj
        _ = e' * Z⁻¹ := hZi
    exact mul_left_cancel h3
  have hs : z₀ * z₀ = d.z ^ (zc (z₀ * z₀)).val := zpow_zc hd hz.sq
  rcases zmod2_cases (kk d x q) with hk | hk
  · rw [hk] at hZdef
    simp at hZdef
    rw [hZdef] at h2
    simp at h2
    have : d.z ^ φ.val = d.z ^ (0 : ZMod 2).val := by simpa using h2
    rw [zpow_val_inj hd this, hk]
    simp
  · rw [hk] at hZdef
    simp at hZdef
    rw [hZdef] at h2
    have h4 : d.z ^ φ.val = (z₀ * z₀)⁻¹ := by
      rw [_root_.mul_inv_rev]
      exact eq_mul_inv_of_mul_eq h2
    rw [hs, inv_eq_of_mul_eq_one_right (hd.s56_zpowers_sq (zpow_mem_zp _))] at h4
    rw [zpow_val_inj hd h4, hk]
    simp


noncomputable def ebHom (hd : d.Hyp) : ↥d.s56V →* Multiplicative W4 :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (eb d x.1)) (fun x y => by
    have := eb_mul hd x.2 y.2
    simpa [ofAdd_add] using congrArg Multiplicative.ofAdd this)

noncomputable def fbHom (hd : d.Hyp) : ↥d.s56J →* Multiplicative W4 :=
  MonoidHom.mk' (fun q => Multiplicative.ofAdd (fb d q.1)) (fun x y => by
    have := fb_mul hd x.2 y.2
    simpa [ofAdd_add] using congrArg Multiplicative.ofAdd this)

theorem exists_tensor (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    ∃ T : Fin 64 → ZMod 2, ∀ x ∈ d.s56V, ∀ q ∈ d.s56J,
      Bf d z₀ x q = betaT T (eb d x) (fb d q) := by
  have heb : Function.Surjective (ebHom hd) := by
    intro a
    obtain ⟨x, hx, hxa⟩ := eb_surj h49 hd hz (Multiplicative.toAdd a)
    exact ⟨⟨x, hx⟩, by simp [ebHom, hxa]⟩
  have hfb : Function.Surjective (fbHom hd) := by
    intro b
    obtain ⟨q, hq, hqb⟩ := fb_surj hd (Multiplicative.toAdd b)
    exact ⟨⟨q, hq⟩, by simp [fbHom, hqb]⟩
  obtain ⟨T, hT⟩ := kapA_rep (ebHom hd) (fbHom hd) heb hfb (fun x q => Bf d z₀ x.1 q.1)
    (fun x x' q => by
      obtain ⟨w, hw, hep⟩ := ep_mul_x h49 hd hz x.2 x'.2 q.2
      have h1 := ep_mem h49 hd hz x.2 q.2
      have h2 := ep_mem h49 hd hz x'.2 q.2
      have hwE := hd.s56_zpowers_le_E hw
      show wcoord d (ep d z₀ (x.1 * x'.1) q.1) = wcoord d (ep d z₀ x.1 q.1) + wcoord d (ep d z₀ x'.1 q.1)
      rw [hep, wcoord_mul hd (mul_mem h2 h1) hwE, wcoord_mul hd h2 h1,
        (wcoord_eq_zero_iff hd hwE).2 hw, add_zero, add_comm])
    (fun x q q' => by
      obtain ⟨w, hw, hep⟩ := ep_mul_q h49 hd hz x.2 q.2 q'.2
      have h1 := ep_mem h49 hd hz x.2 q.2
      have h2 := ep_mem h49 hd hz x.2 q'.2
      have hwE := hd.s56_zpowers_le_E hw
      show wcoord d (ep d z₀ x.1 (q.1 * q'.1)) = wcoord d (ep d z₀ x.1 q.1) + wcoord d (ep d z₀ x.1 q'.1)
      rw [hep, wcoord_mul hd (mul_mem h1 h2) hwE, wcoord_mul hd h1 h2,
        (wcoord_eq_zero_iff hd hwE).2 hw, add_zero])
    (fun x q h => by
      have : eb d x.1 = 0 := by simpa [ebHom] using h
      exact Bf_eq_zero_of_eb h49 hd hz x.2 q.2 this)
    (fun x q h => by
      have : fb d q.1 = 0 := by simpa [fbHom] using h
      exact Bf_eq_zero_of_fb hd x.2 q.2 this)
  refine ⟨T, fun x hx q hq => ?_⟩
  have := hT ⟨x, hx⟩ ⟨q, hq⟩
  simpa [ebHom, fbHom] using this


theorem lift_mem_LM (hd : d.Hyp) {h : Equiv.Perm (Fin 1755)} (hh : h ∈ titsH) :
    d.lift h ∈ d.L ∧ d.lift h ∈ d.M := by
  have hXD : h ∈ titsD := titsH_le_titsD hh
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hC : d.lift h ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem _)
  have hXN : h ∈ titsD ⊓ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
    rw [Model.titsD_inf_normalizer_hatE]
    exact hh
  refine ⟨d.lift_mem _, ?_⟩
  show d.lift h ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hC]
  have hρ : (d.ρ ⟨d.lift h, hC⟩ : Equiv.Perm (Fin 1755)) = h := hd.ρ_lift hXD
  rw [hρ]
  exact hXN.2

theorem gen_facts (hd : d.Hyp) (c : Fin 3) :
    d.lift (chainGen titsHArrs c.val) ∈ d.L ∧ d.lift (chainGen titsHArrs c.val) ∈ d.M ∧
      ∀ j : Fin 5, d.lift (chainGen titsHArrs c.val) * d.pv (basisV j) *
        (d.lift (chainGen titsHArrs c.val))⁻¹ = crdE d (fun i => kapA5 c i j) := by
  have hhH := kapA_model_mem c
  have hhD : chainGen titsHArrs c.val ∈ titsD := titsH_le_titsD hhH
  obtain ⟨hL, hM⟩ := lift_mem_LM hd hhH
  exact ⟨hL, hM, fun j => lift_action hd hhD (kapA5 c) (fun j' => kapA_model_action c j') j⟩

theorem tensor_E1 (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hz : d.S56Z0 z₀) {T : Fin 64 → ZMod 2}
    (hT : ∀ x ∈ d.s56V, ∀ q ∈ d.s56J, Bf d z₀ x q = betaT T (eb d x) (fb d q)) (c : Fin 3)
    (a b' : W4) :
    betaT T (kapA4 c *ᵥ a) b' = kapA4 c *ᵥ betaT T a ((kapA4 c)ᵀ *ᵥ b') := by
  obtain ⟨hgL, hgM, hA⟩ := gen_facts hd c
  generalize d.lift (chainGen titsHArrs c.val) = g at hgL hgM hA
  have hAz := kapA5_zcol c
  have e4 : kapA4 c = Matrix.of fun i j : Fin 4 => kapA5 c i.succ j.succ := rfl
  obtain ⟨x, hx, hxa⟩ := eb_surj h49 hd hz a
  obtain ⟨q₀, hq₀, hq₀b⟩ := fb_surj hd b'
  have hgJ : g⁻¹ * q₀ * g ∈ d.s56J := by
    have hn : g⁻¹ ∈ normalizer (d.s56J : Set G) :=
      hd.s56_L_inf_M_normalizes_J (inv_mem hgL) (inv_mem hgM)
    simpa using (mem_normalizer_iff.1 hn q₀).1 hq₀
  have hgq : g * (g⁻¹ * q₀ * g) * g⁻¹ = q₀ := by group
  obtain ⟨hx', hebx⟩ := eb_conj hd hgM (hd.L_comm_t hgL) (kapA5 c) hAz hA h49 hx
  obtain ⟨hq', hfbq⟩ := fb_conj hd hgL hgM (kapA5 c) hAz hA hgJ
  have hB := Bf_conj h49 hd hz hgL hgM (kapA5 c) hAz hA hx hgJ
  rw [hgq] at hB hfbq
  rw [hT _ hx' q₀ hq₀, hebx, hxa, hq₀b, hT x hx _ hgJ, hxa] at hB
  rw [hq₀b] at hfbq
  rw [← hfbq] at hB
  rw [e4]
  exact hB

theorem tensor_E2 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {T : Fin 64 → ZMod 2}
    (hT : ∀ x ∈ d.s56V, ∀ q ∈ d.s56J, Bf d z₀ x q = betaT T (eb d x) (fb d q)) (a b : W4) :
    b ⬝ᵥ betaT T a b = zc (z₀ * z₀) * (b ⬝ᵥ a) := by
  obtain ⟨x, hx, hxa⟩ := eb_surj h49 hd hz a
  obtain ⟨q, hq, hqb⟩ := fb_surj hd b
  have h := trace_identity h49 hd hz hx hq
  rw [hT x hx q hq, hxa, hqb] at h
  exact h

theorem exists_mu (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hz : d.S56Z0 z₀) :
    ∃ μ : ZMod 2, ∀ x ∈ d.s56V, ∀ q ∈ d.s56J,
      Bf d z₀ x q = betaT (kapTc (zc (z₀ * z₀)) μ) (eb d x) (fb d q) := by
  obtain ⟨T, hT⟩ := exists_tensor h49 hd hz
  obtain ⟨μ, hμ⟩ := kapA_classify (zc (z₀ * z₀)) T (tensor_E1 h49 hd hz hT) (tensor_E2 h49 hd hz hT)
  exact ⟨μ, fun x hx q hq => by rw [hT x hx q hq, hμ]⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
