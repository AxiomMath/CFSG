module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitSylow
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Fuse
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Open
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitBasic

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.V_le_W (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : c.V ≤ c.W := fun v hv =>
  c.mem_W_of_comm (c.V_le_S h hv) fun v' hv' => (c.sFacts hα h hP hQ).V_comm v hv v' hv'

theorem Chart4.alpha_eq_zero_of_isConj
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hfus : IsConj d.q c.pi) : α = 0 := by
  by_contra hne
  have hα1 : α = 1 := by omega
  obtain ⟨g, hg, hW, -⟩ := c.fuse_in_normalizer hα h hP hQ hS2 hc hfus
  have hder : ⁅c.W, c.W⁆ = zpowers (c.t ^ 2) := (c.sFacts hα h hP hQ).W_derived hα1
  have hq : d.q ∈ ⁅c.W, c.W⁆ := by rw [hder, c.q_eq]; exact mem_zpowers _
  have hWg : ∀ w ∈ c.W, g⁻¹ * w * g ∈ c.W := fun w hw =>
    (hW (g⁻¹ * w * g)).2 (by simpa [mul_assoc] using hw)
  have hle : ⁅c.W, c.W⁆ ≤ (⁅c.W, c.W⁆).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g⁻¹).toMonoidHom ⁅a, b⁆ = ⁅g⁻¹ * a * g, g⁻¹ * b * g⁆ := by
      simp [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator (hWg a ha) (hWg b hb)
  have hπ : c.pi ∈ ⁅c.W, c.W⁆ := by
    have := Subgroup.mem_comap.1 (hle hq)
    rw [← hg]
    simpa using this
  rw [hder] at hπ
  exact c.shape_pi_not_mem_zpowers (zpowers_le.2 (pow_mem (mem_zpowers c.t) 2) hπ)

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {u : G} {n : ℕ} (hu : u ^ (2 ^ n) = 1) :
    IsPGroup 2 (zpowers u) := by
  have hdvd : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hu
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, ha])

theorem Chart4.exists_pow_four_eq_q (_c : Chart4 d α) (h : Hyp G A) {x : G} (hx : x ∈ d.Q)
    (hx4 : x ^ 4 ≠ 1) : ∃ u ∈ d.Q, u ^ 4 = d.q := by
  have hQp : IsPGroup 2 d.Q := d.X_sylow.isPGroup.to_inf_left
  obtain ⟨m, hm⟩ := hQp.exists_card_eq
  have hdvd : orderOf x ∣ 2 ^ m := by
    have h1 : orderOf (⟨x, hx⟩ : d.Q) ∣ Nat.card d.Q := orderOf_dvd_natCard _
    rw [hm, Subgroup.orderOf_mk] at h1
    exact h1
  obtain ⟨k, hk, hka⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk3 : 3 ≤ k := by
    by_contra hlt
    apply hx4
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hka]
    exact (Nat.pow_dvd_pow 2 (by omega : k ≤ 2) : 2 ^ k ∣ 2 ^ 2)
  refine ⟨x ^ (2 ^ (k - 3)), pow_mem hx _, ?_⟩
  have hdv : 2 ^ (k - 1) ∣ orderOf x := by
    rw [hka]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow : (x ^ (2 ^ (k - 3))) ^ 4 = x ^ (2 ^ (k - 1)) := by
    rw [← pow_mul]
    congr 1
    have : k - 1 = (k - 3) + 2 := by omega
    rw [this, pow_add]
    norm_num
  have hord : orderOf (x ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdv, hka, Nat.pow_div (by omega) (by norm_num)]
    have : k - (k - 1) = 1 := by omega
    rw [this]
  rw [hpow]
  exact eq_of_orderOf_two_of_isCyclic (d.Q_isCyclic h) (pow_mem hx _) (d.q_mem_Q h) hord d.q_ord

theorem Chart4.Q_le_zpowers_t_of_isConj
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) (hk : c.kinds = {Kind.unitary})
    (hfus : IsConj d.q c.pi) : d.Q ≤ zpowers c.t := by
  by_contra hnle
  obtain ⟨x, hxQ, hxt⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hx4 : x ^ 4 ≠ 1 := fun h4 => hxt (c.mem_zpowers_t_of_pow_four h hxQ h4)
  obtain ⟨u, huQ, hu4⟩ := c.exists_pow_four_eq_q h hxQ hx4
  obtain ⟨g, hg, hW, -⟩ := c.fuse_in_normalizer hα h hP hQ hS2 hc hfus
  have hSf := c.sFacts hα h hP hQ
  have hVW := c.V_le_W hα h hP hQ
  have hpiW : c.pi ∈ c.W := hVW (subset_closure (by simp))
  have hu'C : g⁻¹ * u * g ∈ centralizer (c.W : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : g * w * g⁻¹ ∈ c.W := (hW w).1 hw
    have h1 := d.comm_Q_S huQ hw'.1
    calc w * (g⁻¹ * u * g) = g⁻¹ * ((g * w * g⁻¹) * u) * g := by group
      _ = g⁻¹ * (u * (g * w * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * u * g) * w := by group
  have hu'4 : (g⁻¹ * u * g) ^ 4 = c.pi := by
    have := conj_pow (a := g⁻¹) (b := u) (i := 4)
    simp only [inv_inv] at this
    rw [this, hu4, hg]
  have hu'2 : IsPGroup 2 (zpowers (g⁻¹ * u * g)) := by
    refine isPGroup_zpowers_of_pow_eq_one (n := 3) ?_
    have h8 : (g⁻¹ * u * g) ^ (2 ^ 3) = ((g⁻¹ * u * g) ^ 4) ^ 2 := by
      rw [← pow_mul]
      norm_num
    rw [h8, hu'4]
    exact c.frame.pi2
  have hXW : d.X ≤ normalizer (c.W : Set G) := fun x hx =>
    mem_normalizer_iff.2 fun w => (c.X_normalizes hα h hP hQ hS2 hc hx).1 w
  obtain ⟨k, hkC, hkX⟩ := exists_conj_mem_of_centralizer (c.X_sylow_G_of_facts hα h hP hQ) hXW
    hu'C hu'2
  have hpC : k⁻¹ * (g⁻¹ * u * g) * k ∈ centralizer (c.W : Set G) :=
    mul_mem (mul_mem (inv_mem hkC) hu'C) hkC
  have hp4 : (k⁻¹ * (g⁻¹ * u * g) * k) ^ 4 = c.pi := by
    have := conj_pow (a := k⁻¹) (b := g⁻¹ * u * g) (i := 4)
    simp only [inv_inv] at this
    rw [this, hu'4]
    have hk' := mem_centralizer_iff.1 hkC c.pi hpiW
    calc k⁻¹ * c.pi * k = k⁻¹ * (c.pi * k) := by group
      _ = k⁻¹ * (k * c.pi) := by rw [hk']
      _ = c.pi := by group
  have hVc : ∀ v ∈ c.V, (k⁻¹ * (g⁻¹ * u * g) * k) * v = v * (k⁻¹ * (g⁻¹ * u * g) * k) :=
    fun v hv => (mem_centralizer_iff.1 hpC v (hVW hv)).symm
  obtain ⟨-, hgraph, -⟩ := c.rep_of_kinds_unitary hk
  rcases c.centralizing_V hα h hP hQ hS2 hkX hVc with ⟨a, ha, w, hw, hpaw⟩ | ⟨y', hy', -⟩
  swap
  · rw [hgraph] at hy'
    exact absurd hy' (by simp)
  have hcomm : Commute a w := (d.comm_Q_S ha hw.1).symm
  have hw4 : w ^ 4 = 1 := c.W_pow_four hα h hP hQ w hw
  have ha4 : a ^ 4 = c.pi := by
    have h4 := hp4
    rw [hpaw, hcomm.mul_pow, hw4, mul_one] at h4
    exact h4
  have hpiQ : c.pi ∈ d.Q := ha4 ▸ pow_mem ha 4
  have hmem : c.pi ∈ d.Q ⊓ d.S := ⟨hpiQ, c.mem.1⟩
  rw [c.Q_inf_S_eq hc] at hmem
  exact c.shape_pi_not_mem_zpowers hmem

end CFSG.OddStandard.ChengHeld
