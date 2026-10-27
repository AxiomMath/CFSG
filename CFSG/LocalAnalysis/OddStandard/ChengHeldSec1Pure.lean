module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Basic
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1FF

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem cj_cj_swap (b s y : G) : cj (cj b s) y = cj (cj b y) (cj s y) := by
  unfold cj; group

theorem cj_of_w (d : Datum A) {u s₀ y : G} (hu : u ∈ d.Q) {h : G} (hh : h ∈ d.S) :
    cj h (u * s₀ * y) = cj (cj h s₀) y := by
  have h1 : cj h u = h :=
    cj_of_commute (show Commute h u from mem_centralizer_iff.1 (d.Q_le_centralizer_S hu) h hh)
  rw [← cj_cj, ← cj_cj, h1]

theorem cj_mem_S (d : Datum A) {y : G} (hy : y ∈ d.X) {x : G} (hx : x ∈ d.S) : cj x y ∈ d.S := by
  have := d.conj_mem_S (d.X.inv_mem hy) hx
  simpa [cj] using this

theorem cj_mem_X (d : Datum A) {w p : G} (hw : w ∈ d.X) (hp : p ∈ d.S) : cj w p ∈ d.X :=
  d.X.mul_mem (d.X.mul_mem (d.X.inv_mem (d.S_le_X hp)) hw) (d.S_le_X hp)

theorem cj_not_mem_QS (d : Datum A) {w p : G} (hw : w ∉ d.QS) (hp : p ∈ d.S) : cj w p ∉ d.QS := by
  intro h
  apply hw
  have hpQS : p ∈ d.QS := (le_sup_right : d.S ≤ d.QS) hp
  have := d.QS.mul_mem (d.QS.mul_mem hpQS h) (d.QS.inv_mem hpQS)
  simpa [cj, mul_assoc] using this

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

theorem sq_mem_D {x : G} (hx : x ∈ d.S) : x * x ∈ K.c.D := by
  have hx' : x ∈ closure ({d.q, K.c.pi, K.c.tau, K.c.mu, K.c.lam, K.c.ze, K.c.xi} : Set G) :=
    K.c.gen ▸ hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem a ha =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [(q_mul_self d)]; exact one_mem _
    · rw [K.pi_sq]; exact one_mem _
    · rw [K.tau_sq]; exact one_mem _
    · rw [K.mu_sq]; exact one_mem _
    · rw [K.lam_sq]; exact one_mem _
    · rw [K.ze_sq]; exact one_mem _
    · rw [K.xi_sq]; exact one_mem _
  | one => rw [mul_one]; exact one_mem _
  | mul a b ha hb iha ihb =>
    have haS : a ∈ d.S := K.c.gen ▸ ha
    have hbS : b ∈ d.S := K.c.gen ▸ hb
    have hk : (b⁻¹ * a⁻¹ * b * a) ∈ K.c.D := by
      have := K.comm_mem_D (d.S.inv_mem hbS) (d.S.inv_mem haS)
      simpa [commutatorElement_def] using this
    have hbk : b * (b⁻¹ * a⁻¹ * b * a) = (b⁻¹ * a⁻¹ * b * a) * b := K.D_central hk hbS
    have e : a * b * (a * b) = (a * a) * (b * b) * (b⁻¹ * a⁻¹ * b * a) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b * (b⁻¹ * a⁻¹ * b * a)) * b := by group
        _ = (a * a) * b * ((b⁻¹ * a⁻¹ * b * a) * b) := by group
        _ = (a * a) * b * (b * (b⁻¹ * a⁻¹ * b * a)) := by rw [hbk]
        _ = (a * a) * (b * b) * (b⁻¹ * a⁻¹ * b * a) := by group
    rw [e]
    exact mul_mem (mul_mem iha ihb) hk
  | inv a ha iha =>
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [this]
    exact inv_mem iha

theorem cj_mem_D {x y : G} (hx : x ∈ K.c.D) (hy : y ∈ d.X) : cj x y ∈ K.c.D := by
  have hxS : x ∈ d.S := K.D_le_S hx
  have h1 : cj x y ∈ d.S := by
    have := d.conj_mem_S (d.X.inv_mem hy) hxS
    simpa [cj] using this
  refine K.mem_D_of_central h1 fun t ht => ?_
  have ht' : y * t * y⁻¹ ∈ d.S := d.conj_mem_S hy ht
  have hc : (y * t * y⁻¹) * x = x * (y * t * y⁻¹) := K.D_central hx ht'
  calc t * cj x y = y⁻¹ * ((y * t * y⁻¹) * x) * y := by unfold cj; group
    _ = y⁻¹ * (x * (y * t * y⁻¹)) * y := by rw [hc]
    _ = cj x y * t := by unfold cj; group

theorem gi_core {y : G} (hy : y ∈ d.X) (hinv : ∀ s ∈ d.S, cj (cj s y) y = s)
    {p₁ p₂ : G} (hp₁ : p₁ ∈ d.S) (hp₂ : p₂ ∈ d.S)
    (h₁ : p₁ * cj p₁ y ∉ K.c.D) (h₂ : p₂ * cj p₂ y ∉ K.c.D)
    (h₁₂ : p₁ * cj p₁ y * (p₂ * cj p₂ y) ∉ K.c.D)
    {w u s₀ : G} (hu : u ∈ d.Q) (hs₀ : s₀ ∈ d.S) (hw : w = u * s₀ * y) (hw2 : w * w = 1) :
    ∃ p ∈ d.S, ∀ g ∈ d.S, cj g (cj w p) = cj g y := by
  have e1 : ∀ h ∈ d.S, cj h w = cj (cj h s₀) y := fun h hh => by
    rw [hw]; exact cj_of_w d hu hh
  have hS_cj : ∀ a ∈ d.S, ∀ b ∈ d.S, cj a b ∈ d.S := fun a ha b hb => by
    unfold cj; exact d.S.mul_mem (d.S.mul_mem (d.S.inv_mem hb) ha) hb
  have e2 : ∀ h ∈ d.S, cj (cj h w) w = cj h (s₀ * cj s₀ y) := by
    intro h hh
    have hA : cj h s₀ ∈ d.S := hS_cj h hh s₀ hs₀
    have hB : cj (cj h s₀) y ∈ d.S := cj_mem_S d hy hA
    rw [e1 h hh, e1 _ hB, cj_cj_swap (cj (cj h s₀) y) s₀ y, hinv _ hA, cj_cj]
  have e3 : ∀ h ∈ d.S, cj (cj h w) w = h := fun h _ => by
    rw [cj_cj, hw2]; simp [cj]
  have ht : s₀ * cj s₀ y ∈ K.c.D := by
    refine K.mem_D_of_central (d.S.mul_mem hs₀ (cj_mem_S d hy hs₀)) fun h hh => ?_
    have h1 := (e2 h hh).symm.trans (e3 h hh)
    calc h * (s₀ * cj s₀ y) = (s₀ * cj s₀ y) * ((s₀ * cj s₀ y)⁻¹ * h * (s₀ * cj s₀ y)) := by group
      _ = (s₀ * cj s₀ y) * h := by rw [show (s₀ * cj s₀ y)⁻¹ * h * (s₀ * cj s₀ y) = h from h1]
  let Z : Subgroup ↥d.S := K.c.D.subgroupOf d.S
  have hZn : Z.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) = (n : G) * (g : G) := K.D_central hn g.2
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ K.c.D
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  let σ : ↥d.S ≃* ↥d.S := M1b.cS d y hy
  have hσ : ∀ x : ↥d.S, ((σ x : ↥d.S) : G) = cj (x : G) y := fun x => rfl
  have key := ff_gen Z
    (fun a b => by
      rw [mem_subgroupOf]
      exact K.comm_mem_D a.2 b.2)
    (fun a => by
      rw [mem_subgroupOf]
      exact K.sq_mem_D a.2)
    (by
      have h1 : Nat.card Z = 8 := by
        rw [← K.sf.card_D]
        exact Nat.card_congr (subgroupOfEquivOfLe K.D_le_S).toEquiv
      rw [h1, K.sf.card_S])
    σ (fun a => Subtype.ext (by rw [hσ, hσ]; exact hinv a a.2))
    (fun z hz => by
      rw [mem_subgroupOf] at hz ⊢
      rw [hσ]
      exact K.cj_mem_D hz hy)
    ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
    (fun h => h₁ (by rw [mem_subgroupOf] at h; simpa [hσ] using h))
    (fun h => h₂ (by rw [mem_subgroupOf] at h; simpa [hσ] using h))
    (fun h => h₁₂ (by rw [mem_subgroupOf] at h; simpa [hσ] using h))
    ⟨s₀, hs₀⟩ (by
      rw [mem_subgroupOf]
      simpa [hσ] using ht)
  obtain ⟨p, hp⟩ := key
  have hpz : s₀⁻¹ * ((p : G) * cj (p : G) y) ∈ K.c.D := by
    rw [mem_subgroupOf] at hp
    simpa [hσ] using hp
  refine ⟨(p : G), p.2, fun g hg => ?_⟩
  set z : G := s₀⁻¹ * ((p : G) * cj (p : G) y) with hz
  have hs₀z : s₀ = ((p : G) * cj (p : G) y) * z⁻¹ := by rw [hz]; group
  have he : (cj (p : G) y)⁻¹ * cj s₀ y * (p : G) ∈ K.c.D := by
    have hzi : cj z⁻¹ y ∈ K.c.D := K.cj_mem_D (K.c.D.inv_mem hpz) hy
    have hc : (p : G) * cj z⁻¹ y = cj z⁻¹ y * (p : G) := K.D_central hzi p.2
    have e6 : cj s₀ y = (cj (p : G) y * (p : G)) * cj z⁻¹ y := by
      rw [hs₀z, cj_mul, cj_mul, hinv _ p.2]
    have e7 : (cj (p : G) y)⁻¹ * cj s₀ y * (p : G) = cj z⁻¹ y * ((p : G) * (p : G)) := by
      rw [e6]
      calc (cj (p : G) y)⁻¹ * (cj (p : G) y * (p : G) * cj z⁻¹ y) * (p : G)
          = ((p : G) * cj z⁻¹ y) * (p : G) := by group
        _ = (cj z⁻¹ y * (p : G)) * (p : G) := by rw [hc]
        _ = cj z⁻¹ y * ((p : G) * (p : G)) := by group
    rw [e7]
    exact K.c.D.mul_mem hzi (K.sq_mem_D p.2)
  have hpgS : (p : G) * g * (p : G)⁻¹ ∈ d.S :=
    d.S.mul_mem (d.S.mul_mem p.2 hg) (d.S.inv_mem p.2)
  have e4 : cj g (cj w (p : G)) = cj (cj ((p : G) * g * (p : G)⁻¹) w) (p : G) := by
    unfold cj; group
  have e5 : cj (cj (cj ((p : G) * g * (p : G)⁻¹) s₀) y) (p : G) =
      ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G))⁻¹ * cj g y *
        ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G)) := by
    unfold cj; group
  rw [e4, e1 _ hpgS, e5]
  have hc2 : cj g y * ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G)) =
      ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G)) * cj g y := K.D_central he (cj_mem_S d hy hg)
  calc ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G))⁻¹ * cj g y *
        ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G))
      = ((cj (p : G) y)⁻¹ * cj s₀ y * (p : G))⁻¹ *
        (((cj (p : G) y)⁻¹ * cj s₀ y * (p : G)) * cj g y) := by rw [mul_assoc, hc2]
    _ = cj g y := by group

local macro "dnorm " K:term : tactic =>
  `(tactic| simp only [mul_assoc, ($K).sort_pq, ($K).sort_tq, ($K).sort_tp, canc_q,
    ($K).canc_p, ($K).canc_t, ($K).pi_q, ($K).tau_q, ($K).tau_pi, q_mul_self,
    ($K).pi_sq, ($K).tau_sq, one_mul, mul_one])

theorem comm_xi_mu : ⁅K.c.xi, K.c.mu⁆ = K.c.pi * K.c.tau := by
  rw [← commutatorElement_inv, K.comm_mu_xi]
  exact inv_eq_of_mul_eq_one_right (by dnorm K)

theorem comm_ze_mu : ⁅K.c.ze, K.c.mu⁆ = d.q * K.c.pi := by
  rw [← commutatorElement_inv, K.comm_mu_ze]
  exact inv_eq_of_mul_eq_one_right (by dnorm K)

theorem comm_ze_self : ⁅K.c.ze, K.c.ze⁆ = 1 := by simp

theorem comm_xi_self : ⁅K.c.xi, K.c.xi⁆ = 1 := by simp

theorem comm_xi_ze : ⁅K.c.xi, K.c.ze⁆ = 1 := by
  rw [← commutatorElement_inv, K.comm_ze_xi, inv_one]

theorem comm_lam_mu : ⁅K.c.lam, K.c.mu⁆ = 1 := by
  rw [← commutatorElement_inv, K.comm_mu_lam, inv_one]

theorem zexi_mem_S : K.c.ze * K.c.xi ∈ d.S := d.S.mul_mem K.ze_mem_S K.xi_mem_S

theorem nm_F1 : K.c.mu * K.c.lam ∉ K.c.D :=
  K.not_mem_D_of_comm K.ze_mem_S (by
    rw [K.comm_mul_left K.mu_mem_S K.lam_mem_S K.ze_mem_S, K.comm_mu_ze, K.comm_lam_ze]
    dnorm K
    exact K.tau_ne_one)

theorem nm_F2 : K.c.ze * (K.c.ze * K.c.xi) ∉ K.c.D := by
  rw [← mul_assoc, K.ze_sq, one_mul]
  exact K.not_mem_D_of_comm K.mu_mem_S (by
    rw [K.comm_xi_mu]
    exact K.pi_tau_ne_one)

theorem nm_F12 : K.c.mu * K.c.lam * (K.c.ze * (K.c.ze * K.c.xi)) ∉ K.c.D := by
  rw [← mul_assoc K.c.ze, K.ze_sq, one_mul]
  exact K.not_mem_D_of_comm K.ze_mem_S (by
    rw [K.comm_mul_left (d.S.mul_mem K.mu_mem_S K.lam_mem_S) K.xi_mem_S K.ze_mem_S,
      K.comm_mul_left K.mu_mem_S K.lam_mem_S K.ze_mem_S, K.comm_mu_ze, K.comm_lam_ze,
      K.comm_xi_ze]
    dnorm K
    exact K.tau_ne_one)

theorem nm_G1 : K.c.mu * (K.c.ze * K.c.xi) ∉ K.c.D :=
  K.not_mem_D_of_comm K.xi_mem_S (by
    rw [K.comm_mul_left K.mu_mem_S K.zexi_mem_S K.xi_mem_S,
      K.comm_mul_left K.ze_mem_S K.xi_mem_S K.xi_mem_S, K.comm_mu_xi, K.comm_ze_xi, K.comm_xi_self]
    dnorm K
    exact K.pi_tau_ne_one)

theorem nm_G2 : K.c.lam * K.c.ze ∉ K.c.D :=
  K.not_mem_D_of_comm K.xi_mem_S (by
    rw [K.comm_mul_left K.lam_mem_S K.ze_mem_S K.xi_mem_S, K.comm_lam_xi, K.comm_ze_xi]
    dnorm K
    exact K.tau_ne_one)

theorem nm_G12 : K.c.mu * (K.c.ze * K.c.xi) * (K.c.lam * K.c.ze) ∉ K.c.D :=
  K.not_mem_D_of_comm K.ze_mem_S (by
    rw [K.comm_mul_left (d.S.mul_mem K.mu_mem_S K.zexi_mem_S) (d.S.mul_mem K.lam_mem_S K.ze_mem_S)
        K.ze_mem_S, K.comm_mul_left K.mu_mem_S K.zexi_mem_S K.ze_mem_S,
      K.comm_mul_left K.ze_mem_S K.xi_mem_S K.ze_mem_S,
      K.comm_mul_left K.lam_mem_S K.ze_mem_S K.ze_mem_S, K.comm_mu_ze, K.comm_xi_ze,
      K.comm_lam_ze, K.comm_ze_self]
    dnorm K
    exact K.tau_ne_one)

theorem nm_U1 : K.c.mu * K.c.ze ∉ K.c.D :=
  K.not_mem_D_of_comm K.xi_mem_S (by
    rw [K.comm_mul_left K.mu_mem_S K.ze_mem_S K.xi_mem_S, K.comm_mu_xi, K.comm_ze_xi]
    dnorm K
    exact K.pi_tau_ne_one)

theorem nm_U2 : K.c.lam * (K.c.ze * K.c.xi) ∉ K.c.D :=
  K.not_mem_D_of_comm K.mu_mem_S (by
    rw [K.comm_mul_left K.lam_mem_S K.zexi_mem_S K.mu_mem_S,
      K.comm_mul_left K.ze_mem_S K.xi_mem_S K.mu_mem_S, K.comm_lam_mu, K.comm_ze_mu,
      K.comm_xi_mu]
    dnorm K
    exact K.q_tau_ne_one)

theorem nm_U12 : K.c.mu * K.c.ze * (K.c.lam * (K.c.ze * K.c.xi)) ∉ K.c.D :=
  K.not_mem_D_of_comm K.ze_mem_S (by
    rw [K.comm_mul_left (d.S.mul_mem K.mu_mem_S K.ze_mem_S) (d.S.mul_mem K.lam_mem_S K.zexi_mem_S)
        K.ze_mem_S, K.comm_mul_left K.mu_mem_S K.ze_mem_S K.ze_mem_S,
      K.comm_mul_left K.lam_mem_S K.zexi_mem_S K.ze_mem_S,
      K.comm_mul_left K.ze_mem_S K.xi_mem_S K.ze_mem_S, K.comm_mu_ze, K.comm_lam_ze,
      K.comm_ze_self, K.comm_xi_ze]
    dnorm K
    exact K.tau_ne_one)

theorem act2_of_agree {k : Kind} {y w : G}
    (hy : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y)
    (hag : ∀ g ∈ d.S, cj g w = cj g y) :
    k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi w := by
  cases k <;> simp only [Kind.Act2] at hy ⊢ <;>
  exact ⟨(hag _ K.q_mem_S).trans hy.1, (hag _ K.pi_mem_S).trans hy.2.1,
    (hag _ K.tau_mem_S).trans hy.2.2.1, (hag _ K.mu_mem_S).trans hy.2.2.2.1,
    (hag _ K.lam_mem_S).trans hy.2.2.2.2.1, (hag _ K.ze_mem_S).trans hy.2.2.2.2.2.1,
    (hag _ K.xi_mem_S).trans hy.2.2.2.2.2.2⟩

theorem gi_of_kind {k : Kind} {y : G} (hy : y ∈ d.X)
    (hact : k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y)
    {w u s₀ : G} (hu : u ∈ d.Q) (hs₀ : s₀ ∈ d.S) (hw : w = u * s₀ * y) (hw2 : w * w = 1) :
    ∃ p ∈ d.S, k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi (cj w p) := by
  have hA := K.c.autFactsG K.h K.hP K.hQ k hy hact
  have hinv' : ∀ s ∈ d.S, cj (cj s y) y = s := fun s hs => hA.invol s hs
  have core : ∃ p ∈ d.S, ∀ g ∈ d.S, cj g (cj w p) = cj g y := by
    have hact' := hact
    cases k
    · simp only [Kind.Act2] at hact'
      obtain ⟨-, -, -, hmu, -, hze, -⟩ := hact'
      refine K.gi_core hy hinv' (p₁ := K.c.mu) (p₂ := K.c.ze) K.mu_mem_S K.ze_mem_S ?_ ?_ ?_
        hu hs₀ hw hw2
      · rw [hmu]; exact K.nm_F1
      · rw [hze]; exact K.nm_F2
      · rw [hmu, hze]; exact K.nm_F12
    · simp only [Kind.Act2] at hact'
      obtain ⟨-, -, -, hmu, hlam, -, -⟩ := hact'
      refine K.gi_core hy hinv' (p₁ := K.c.mu) (p₂ := K.c.lam) K.mu_mem_S K.lam_mem_S ?_ ?_ ?_
        hu hs₀ hw hw2
      · rw [hmu]; exact K.nm_G1
      · rw [hlam]; exact K.nm_G2
      · rw [hmu, hlam]; exact K.nm_G12
    · simp only [Kind.Act2] at hact'
      obtain ⟨-, -, -, hmu, hlam, -, -⟩ := hact'
      refine K.gi_core hy hinv' (p₁ := K.c.mu) (p₂ := K.c.lam) K.mu_mem_S K.lam_mem_S ?_ ?_ ?_
        hu hs₀ hw hw2
      · rw [hmu]; exact K.nm_U1
      · rw [hlam]; exact K.nm_U2
      · rw [hmu, hlam]; exact K.nm_U12
  obtain ⟨p, hp, hag⟩ := core
  exact ⟨p, hp, K.act2_of_agree hact hag⟩

theorem exists_pure_conj {w : G} (hw : w ∈ d.X) (hwQS : w ∉ d.QS) (hw2 : w * w = 1) :
    ∃ k : Kind, ∃ p ∈ d.S,
      k.Act2 d.q K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi (cj w p) := by
  obtain ⟨k, y, hk, a, ha, rfl⟩ := K.c.cover w hw hwQS
  obtain ⟨u, hu, s₀, hs₀, rfl⟩ := d.mem_QS_iff.1 ha
  obtain ⟨hyX, -, hact⟩ := K.c.rep_mem k y hk
  obtain ⟨p, hp, h⟩ := K.gi_of_kind hyX hact hu hs₀ rfl hw2
  exact ⟨k, p, hp, h⟩

theorem coset_classes {w : G} (hw : w ∈ d.X) (hwQS : w ∉ d.QS) (hw2 : w * w = 1) {z : G}
    (hz : ∃ s ∈ d.S, z = s * w) (hz2 : z * z = 1) :
    ∃ s ∈ d.S, cj z s = w ∨ cj z s = d.q * w := by
  obtain ⟨k, p, hp, hact⟩ := K.exists_pure_conj hw hwQS hw2
  obtain ⟨s₁, hs₁, rfl⟩ := hz
  have hw'X : cj w p ∈ d.X := cj_mem_X d hw hp
  have hw'2 : cj w p * cj w p = 1 := by rw [← cj_mul, hw2]; simp [cj]
  have hz' : ∃ s ∈ d.S, cj (s₁ * w) p = s * cj w p :=
    ⟨cj s₁ p, by unfold cj; exact d.S.mul_mem (d.S.mul_mem (d.S.inv_mem hp) hs₁) hp, by
      rw [cj_mul]⟩
  have hz2' : cj (s₁ * w) p * cj (s₁ * w) p = 1 := by rw [← cj_mul, hz2]; simp [cj]
  obtain ⟨s', hs', h⟩ := K.c.coset_classes_S K.h K.hP K.hQ k hw'X hact hw'2 hz' hz2'
  have hs'' : p * s' * p⁻¹ ∈ d.S := d.S.mul_mem (d.S.mul_mem hp hs') (d.S.inv_mem hp)
  refine ⟨p * s' * p⁻¹, hs'', ?_⟩
  have e1 : cj (s₁ * w) (p * s' * p⁻¹) = cj (cj (cj (s₁ * w) p) s') p⁻¹ := by
    rw [cj_cj, cj_cj, mul_assoc]
  have hqp : cj d.q p⁻¹ = d.q := K.cj_D_QS ((le_sup_right : d.S ≤ d.QS) (d.S.inv_mem hp)) K.q_mem_D
  rcases h with h | h
  · left
    rw [e1, h]
    unfold cj; group
  · right
    rw [e1, h, cj_mul, hqp]
    unfold cj; group

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
