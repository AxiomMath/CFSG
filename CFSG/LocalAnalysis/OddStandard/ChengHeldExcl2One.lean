module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Alg
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Q

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem sq_mem_closure_of_comm {a b c : G} {H : Subgroup G}
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : a * a ∈ H) (hb : b * b ∈ H) (hc : c * c ∈ H) {x : G}
    (hx : x ∈ closure ({a, b, c} : Set G)) : x * x ∈ H := by
  have hgen : ∀ g ∈ ({a, b, c} : Set G), ∀ h ∈ ({a, b, c} : Set G), g * h = h * g := by
    intro g hg h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl <;>
      first
        | rfl
        | exact hab
        | exact hab.symm
        | exact hac
        | exact hac.symm
        | exact hbc
        | exact hbc.symm
  have hpair : ({a, b, c} : Set G).Pairwise Commute := fun g hg h hh _ => hgen g hg h hh
  have := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ x ∈ closure ({a, b, c} : Set G), ∀ y ∈ closure ({a, b, c} : Set G),
      x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  | one => simp
  | mul x y hx hy ihx ihy =>
    have h := hcomm x hx y hy
    have : x * y * (x * y) = (x * x) * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [h]
        _ = (x * x) * (y * y) := by group
    rw [this]
    exact H.mul_mem ihx ihy
  | inv x hx ih =>
    have : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [this]
    exact H.inv_mem ih

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem sq_mem_zpowers_q_of_central_W (hα1 : α = 1) {w : G} (hw : w ∈ K.c.W)
    (hwc : ∀ w' ∈ K.c.W, w * w' = w' * w) : w * w ∈ zpowers d.q := by
  have hZ : w ∈ K.c.W ⊓ centralizer (K.c.W : Set G) :=
    ⟨hw, mem_centralizer_iff.2 fun h hh => (hwc h hh).symm⟩
  rw [K.sf.W_center hα1] at hZ
  have hπV : K.c.pi ∈ K.c.V := subset_closure (by simp)
  have htτV : K.c.t * K.c.tau ∈ K.c.V := subset_closure (by simp)
  have hπS : K.c.pi ∈ d.S := K.c.mem.1
  have htτS : K.c.t * K.c.tau ∈ d.S := mul_mem K.c.t_mem.2 K.c.mem.2.1
  refine sq_mem_closure_of_comm (H := zpowers d.q) (K.t_comm hπS).symm (K.t_comm htτS).symm
    (K.sf.V_comm _ hπV _ htτV) ?_ ?_ ?_ hZ
  · rw [← pow_two, ← K.c.q_eq]
    exact mem_zpowers _
  · rw [K.pi_mul_self']
    exact one_mem _
  · rw [K.sf.V_sq _ htτV]
    exact one_mem _

theorem W_le_P : K.c.W ≤ centralizer (K.c.V : Set G) := fun _ hw =>
  K.qwSub_le_centralizer_V (mem_sup_right hw)

theorem zpowers_q_le_zpowers_t : zpowers d.q ≤ zpowers K.c.t :=
  Subgroup.zpowers_le.2 (by rw [K.c.q_eq]; exact pow_mem (mem_zpowers _) 2)

end Cfg

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem mem_qwSub_of_central_one (hα1 : α = 1) {x : G}
    (hx : x ∈ d.X ⊓ centralizer (K.c.V : Set G))
    (hz : ∀ p ∈ d.X ⊓ centralizer (K.c.V : Set G), x * p = p * x) : x ∈ qwSub K.c := by
  rcases K.centralizer_V_cases hx with h | ⟨y, hy, b, hb, rfl⟩
  · exact h
  · exfalso
    obtain ⟨hyX, -, hact⟩ := K.c.rep_mem Kind.graph y hy
    obtain ⟨u, hu, w', hw', rfl⟩ := K.mem_qwSub_iff.1 hb
    have hmW : K.c.mu * K.c.lam * K.c.xi ∈ K.c.W := K.mlx_mem_W
    set m := K.c.mu * K.c.lam * K.c.xi with hm
    have hcomm : ⁅m⁻¹, w'⁻¹⁆ ∈ ⁅K.c.W, K.c.W⁆ :=
      commutator_mem_commutator (inv_mem hmW) (inv_mem hw')
    rw [K.sf.W_derived hα1, ← K.c.q_eq] at hcomm
    have hcj : cj m w' = m * ⁅m⁻¹, w'⁻¹⁆ := by
      rw [commutatorElement_def]
      unfold cj
      group
    have hcy : cj ⁅m⁻¹, w'⁻¹⁆ y = ⁅m⁻¹, w'⁻¹⁆ := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcomm
      rw [← hk]
      exact cj_of_commute (Commute.zpow_left (K.q_comm_X hyX).symm k)
    have h1 : cj m (u * w' * y) = m :=
      cj_of_commute (hz m ⟨d.S_le_X hmW.1, K.W_le_P hmW⟩).symm
    have h2 : cj m (u * w') = m * ⁅m⁻¹, w'⁻¹⁆ := by
      rw [← cj_cj, cj_of_commute (d.comm_Q_S hu K.mlx_mem_S), hcj]
    have h3 : cj m (u * w' * y) = m * (d.q * K.c.pi) * ⁅m⁻¹, w'⁻¹⁆ := by
      rw [← cj_cj, h2, cj_mul, K.cj_mlx_graph hα1 hact, hcy]
    have h4 : (d.q * K.c.pi) * ⁅m⁻¹, w'⁻¹⁆ = 1 := by
      have h5 : m * ((d.q * K.c.pi) * ⁅m⁻¹, w'⁻¹⁆) = m * 1 := by
        rw [mul_one, ← mul_assoc, ← h3, h1]
      exact mul_left_cancel h5
    have hπ : K.c.pi = d.q⁻¹ * ⁅m⁻¹, w'⁻¹⁆⁻¹ := by
      calc K.c.pi = d.q⁻¹ * (d.q * K.c.pi * ⁅m⁻¹, w'⁻¹⁆) * ⁅m⁻¹, w'⁻¹⁆⁻¹ := by group
        _ = d.q⁻¹ * ⁅m⁻¹, w'⁻¹⁆⁻¹ := by rw [h4, mul_one]
    have hπt : K.c.pi ∈ zpowers K.c.t := by
      apply K.zpowers_q_le_zpowers_t
      rw [hπ]
      exact mul_mem (inv_mem (mem_zpowers _)) (inv_mem hcomm)
    exact K.c.shape_pi_not_mem_zpowers hπt

theorem sq_mem_Q_of_central (hα1 : α = 1) {x : G} (hx : x ∈ d.X ⊓ centralizer (K.c.V : Set G))
    (hz : ∀ p ∈ d.X ⊓ centralizer (K.c.V : Set G), x * p = p * x) : x * x ∈ d.Q := by
  obtain ⟨u, hu, w, hw, rfl⟩ := K.mem_qwSub_iff.1 (K.mem_qwSub_of_central_one hα1 hx hz)
  have huw : ∀ w' ∈ K.c.W, u * w' = w' * u := fun w' hw' => (d.comm_Q_S hu hw'.1).symm
  have hwc : ∀ w' ∈ K.c.W, w * w' = w' * w := by
    intro w' hw'
    have h1 := hz w' ⟨d.S_le_X hw'.1, K.W_le_P hw'⟩
    have : u * (w * w') = u * (w' * w) := by
      calc u * (w * w') = u * w * w' := by group
        _ = w' * (u * w) := h1
        _ = (w' * u) * w := by group
        _ = (u * w') * w := by rw [huw w' hw']
        _ = u * (w' * w) := by group
    exact mul_left_cancel this
  have hw2 := K.sq_mem_zpowers_q_of_central_W hα1 hw hwc
  have hq : zpowers d.q ≤ d.Q := Subgroup.zpowers_le.2 K.q_mem_Q
  have hcm : u * w = w * u := huw w hw
  have : u * w * (u * w) = (u * u) * (w * w) := by
    calc u * w * (u * w) = u * (w * u) * w := by group
      _ = u * (u * w) * w := by rw [← hcm]
      _ = (u * u) * (w * w) := by group
  rw [this]
  exact mul_mem (mul_mem hu hu) (hq hw2)

theorem t_central (hα1 : α = 1) {p : G} (hp : p ∈ d.X ⊓ centralizer (K.c.V : Set G)) :
    K.c.t * p = p * K.c.t := by
  rcases K.centralizer_V_cases hp with hB | ⟨y, hy, b, hb, rfl⟩
  · exact (K.comm_t_of_mem_qwSub hB).symm
  · obtain ⟨-, -, hact⟩ := K.c.rep_mem Kind.graph y hy
    have hα0 : ¬ α = 0 := by omega
    simp only [Kind.Act, hα0, ↓reduceIte] at hact
    have hty : K.c.t * y = y * K.c.t := mul_eq_of_cj_eq hact.1
    have hbt : b * K.c.t = K.c.t * b := K.comm_t_of_mem_qwSub hb
    calc K.c.t * (b * y) = (K.c.t * b) * y := by group
      _ = (b * K.c.t) * y := by rw [hbt]
      _ = b * (K.c.t * y) := by group
      _ = b * (y * K.c.t) := by rw [hty]
      _ = b * y * K.c.t := by group

theorem not_isConj_q_pi_one (hα1 : α = 1) : ¬ IsConj d.q K.c.pi := by
  intro hqπ
  obtain ⟨n₁, hn₁N, hn₁⟩ := K.c.fuse_in_normalizer' K.hα K.h K.hP K.hQ K.hS2 K.hc hqπ
  obtain ⟨c, hcC, -, hmP⟩ := K.exists_mul_mem_normalizer_P (inv_mem hn₁N)
  obtain ⟨m, hm, hmP'⟩ : ∃ m : G, m = c⁻¹ * n₁⁻¹ ∧
      m ∈ normalizer ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) := ⟨_, rfl, hmP⟩
  have hpiV : K.c.pi ∈ K.c.V := subset_closure (by simp)
  have hmq : m * d.q * m⁻¹ = K.c.pi := by
    have h1 : n₁⁻¹ * d.q * n₁ = K.c.pi := hn₁
    have h2 : K.c.pi * c = c * K.c.pi := mem_centralizer_iff.1 hcC K.c.pi hpiV
    calc m * d.q * m⁻¹ = c⁻¹ * (n₁⁻¹ * d.q * n₁) * c := by rw [hm]; group
      _ = c⁻¹ * (K.c.pi * c) := by rw [h1, mul_assoc]
      _ = K.c.pi := by rw [h2]; group
  have htP : K.c.t ∈ d.X ⊓ centralizer (K.c.V : Set G) :=
    ⟨d.S_le_X K.c.t_mem.2, K.t_mem_centralizer_V⟩
  have ht'P : m * K.c.t * m⁻¹ ∈ d.X ⊓ centralizer (K.c.V : Set G) :=
    (mem_normalizer_iff.1 hmP' K.c.t).1 htP
  have ht'c : ∀ p ∈ d.X ⊓ centralizer (K.c.V : Set G),
      (m * K.c.t * m⁻¹) * p = p * (m * K.c.t * m⁻¹) := by
    intro p hp
    have hp' : m⁻¹ * p * m ∈ d.X ⊓ centralizer (K.c.V : Set G) := by
      have h := (mem_normalizer_iff.1 hmP' (m⁻¹ * p * m)).2
      have e : m * (m⁻¹ * p * m) * m⁻¹ = p := by group
      rw [e] at h
      exact h hp
    have h1 := K.t_central hα1 hp'
    calc m * K.c.t * m⁻¹ * p = m * (K.c.t * (m⁻¹ * p * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * p * m) * K.c.t) * m⁻¹ := by rw [h1]
      _ = p * (m * K.c.t * m⁻¹) := by group
  have hsq := K.sq_mem_Q_of_central hα1 ht'P ht'c
  have hπ : K.c.pi = (m * K.c.t * m⁻¹) * (m * K.c.t * m⁻¹) := by
    rw [← hmq, K.c.q_eq, pow_two]
    group
  have hπQ : K.c.pi ∈ d.Q := hπ ▸ hsq
  have hπt : K.c.pi ∈ zpowers K.c.t := by
    rw [← K.c.Q_inf_S_eq K.hc]
    exact ⟨hπQ, K.c.mem.1⟩
  exact K.c.shape_pi_not_mem_zpowers hπt

theorem isConj_q_pi_of_graph_one (hα1 : α = 1) {z : G} (hzQS : z ∉ d.QS) (hzq : IsConj d.q z)
    (hact : Kind.graph.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) :
    IsConj d.q K.c.pi := by
  have hα0 : ¬ α = 0 := by omega
  simp only [Kind.Act, hα0, ↓reduceIte] at hact
  have hcomm : z * K.c.t = K.c.t * z := (mul_eq_of_cj_eq hact.1).symm
  exact K.c.fuse_of_commutes K.hα K.h K.hP K.hQ K.hc hzQS hzq hcomm

theorem isConj_q_pi_of_field_one (hα1 : α = 1) {z : G} (hzX : z ∈ d.X) (hzQS : z ∉ d.QS)
    (hz2 : z * z = 1) (hzq : IsConj d.q z)
    (hact : Kind.field.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi z) :
    IsConj d.q K.c.pi := by
  obtain ⟨g₀, hg₀, hgX⟩ := d.exists_conj_config K.h hzq
  have hα0 : ¬ α = 0 := by omega
  have hsfix := K.cj_mlx_field hact
  simp only [Kind.Act, hα0, ↓reduceIte] at hact
  obtain ⟨hzt, -, hzτ, -, -, -, -⟩ := hact
  have hsS : K.c.mu * K.c.lam * K.c.xi ∈ d.S := K.mlx_mem_S
  have hxs : (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi) = d.q * K.c.pi := K.mlx_sq
  have hsz' : (K.c.mu * K.c.lam * K.c.xi) * z = z * (K.c.mu * K.c.lam * K.c.xi) :=
    mul_eq_of_cj_eq hsfix
  generalize K.c.mu * K.c.lam * K.c.xi = s at hsS hxs hsz'
  have hpi2 : K.c.pi * K.c.pi = 1 := K.pi_mul_self'
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hqπ : d.q * K.c.pi = K.c.pi * d.q := (K.q_comm_S' K.c.mem.1).symm
  have hxS : d.q * K.c.pi ∈ d.S := hxs ▸ mul_mem hsS hsS
  have hxz : (d.q * K.c.pi) * z = z * (d.q * K.c.pi) := by
    rw [← hxs]
    calc s * s * z = s * (s * z) := by group
      _ = s * (z * s) := by rw [hsz']
      _ = (s * z) * s := by group
      _ = (z * s) * s := by rw [hsz']
      _ = z * (s * s) := by group
  have hx2 : (d.q * K.c.pi) * (d.q * K.c.pi) = 1 := by
    calc d.q * K.c.pi * (d.q * K.c.pi) = d.q * (K.c.pi * d.q) * K.c.pi := by group
      _ = d.q * (d.q * K.c.pi) * K.c.pi := by rw [← hqπ]
      _ = (d.q * d.q) * (K.c.pi * K.c.pi) := by group
      _ = 1 := by rw [hqq, hpi2, mul_one]
  have hx1 : d.q * K.c.pi ≠ 1 := by
    intro h1
    apply K.c.pi_ne_q K.hα K.h K.hP K.hQ
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hqq]
  have hx' : g₀ * (d.q * K.c.pi) * g₀⁻¹ ∈ d.QS := by
    have hsX : g₀ * s * g₀⁻¹ ∈ d.X := hgX _ (d.S_le_X hsS) hsz'
    have e : g₀ * (d.q * K.c.pi) * g₀⁻¹ = (g₀ * s * g₀⁻¹) * (g₀ * s * g₀⁻¹) := by
      rw [← hxs]
      group
    rw [e]
    exact K.c.sq_mem_QS K.hα K.h K.hP K.hQ hsX
  obtain ⟨-, hπ2⟩ := K.fuse_aux hzX hzQS hg₀ hgX (d.S_le_X hxS) (mem_sup_right hxS) hxz hx2 hx1 hx'
  have h1 : K.c.tau * z = z * (K.c.pi * K.c.tau) := mul_eq_of_cj_eq hzτ
  have h2 : z * K.c.tau = (K.c.pi * K.c.tau) * z := by
    calc z * K.c.tau = z * K.c.tau * (z * z) := by rw [hz2, mul_one]
      _ = z * (K.c.tau * z) * z := by group
      _ = z * (z * (K.c.pi * K.c.tau)) * z := by rw [h1]
      _ = (z * z) * (K.c.pi * K.c.tau) * z := by group
      _ = (K.c.pi * K.c.tau) * z := by rw [hz2, one_mul]
  have hτπ : cj K.c.pi K.c.tau = K.c.pi := cj_of_commute (cm_eq_one_iff.1 K.c.frame.pi_tau)
  unfold cj at hτπ
  have hcjz : cj z K.c.tau = K.c.pi * z := by
    unfold cj
    calc K.c.tau⁻¹ * z * K.c.tau = K.c.tau⁻¹ * (z * K.c.tau) := by group
      _ = K.c.tau⁻¹ * ((K.c.pi * K.c.tau) * z) := by rw [h2]
      _ = (K.c.tau⁻¹ * K.c.pi * K.c.tau) * z := by group
      _ = K.c.pi * z := by rw [hτπ]
  have hzt' : z * K.c.t * z = K.c.t⁻¹ := mul_mul_eq_of_cj_eq hz2 hzt
  have htinv2 : K.c.t⁻¹ * K.c.t⁻¹ = d.q := by
    rw [K.c.q_eq]
    have h4 : K.c.t ^ 2 * K.c.t ^ 2 = 1 := by
      rw [← pow_add]
      exact K.c.frame.t4
    calc K.c.t⁻¹ * K.c.t⁻¹ = (K.c.t * K.c.t)⁻¹ := by group
      _ = (K.c.t ^ 2)⁻¹ := by rw [pow_two]
      _ = K.c.t ^ 2 := inv_eq_of_mul_eq_one_right h4
  have hcjt : cj z K.c.t = d.q * z := by
    unfold cj
    calc K.c.t⁻¹ * z * K.c.t = K.c.t⁻¹ * z * K.c.t * (z * z) := by rw [hz2, mul_one]
      _ = K.c.t⁻¹ * (z * K.c.t * z) * z := by group
      _ = K.c.t⁻¹ * K.c.t⁻¹ * z := by rw [hzt']
      _ = d.q * z := by rw [htinv2]
  have hπt : cj K.c.pi K.c.t = K.c.pi := cj_of_commute (K.t_comm K.c.mem.1)
  have hzz : IsConj z (z * (d.q * K.c.pi)) := by
    have e : K.c.pi * (d.q * z) = z * (d.q * K.c.pi) := by
      calc K.c.pi * (d.q * z) = (K.c.pi * d.q) * z := by group
        _ = (d.q * K.c.pi) * z := by rw [← hqπ]
        _ = z * (d.q * K.c.pi) := hxz
    refine (isConj_of_cj_eq hcjz).trans ?_
    rw [← e]
    exact isConj_of_cj_eq (s := K.c.t) (by rw [cj_mul, hπt, hcjt])
  exact hzq.trans (hzz.trans hπ2.symm)

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
