module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Act
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2UniqWAux
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelDerived

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem conj_QSy (d : Datum A) {u s y x : G} (hu : u ∈ d.Q) (hx : x ∈ d.S) :
    (u * s * y)⁻¹ * x * (u * s * y) = y⁻¹ * (s⁻¹ * x * s) * y := by
  have h1 : x * u = u * x := mem_centralizer_iff.1 (d.Q_le_centralizer_S hu) x hx
  have h2 : u⁻¹ * x * u = x := by
    calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
      _ = u⁻¹ * (u * x) := by rw [h1]
      _ = x := by group
  calc (u * s * y)⁻¹ * x * (u * s * y) = y⁻¹ * s⁻¹ * (u⁻¹ * x * u) * s * y := by group
    _ = y⁻¹ * (s⁻¹ * x * s) * y := by rw [h2]; group

theorem sq_QSy (d : Datum A) {u s y : G} (hu : u ∈ d.Q) (hs : s ∈ d.S) (hy : y ∈ d.X)
    (hyy : y * y ∈ d.Q) :
    u * s * y * (u * s * y) = (u * (y * u * y⁻¹) * (y * y)) * (s * (y⁻¹ * s * y)) := by
  have hQS : ∀ q ∈ d.Q, ∀ s ∈ d.S, s * q = q * s := fun q hq s hs =>
    mem_centralizer_iff.1 (d.Q_le_centralizer_S hq) s hs
  have h1 : s * (y * u * y⁻¹) = (y * u * y⁻¹) * s := hQS _ (d.conj_mem_Q hy hu) s hs
  have h2 : s * (y * y) = (y * y) * s := hQS _ hyy s hs
  calc u * s * y * (u * s * y)
      = u * (s * (y * u * y⁻¹)) * ((y * y) * (y⁻¹ * s * y)) := by group
    _ = u * ((y * u * y⁻¹) * s) * ((y * y) * (y⁻¹ * s * y)) := by rw [h1]
    _ = u * (y * u * y⁻¹) * (s * (y * y)) * (y⁻¹ * s * y) := by group
    _ = u * (y * u * y⁻¹) * ((y * y) * s) * (y⁻¹ * s * y) := by rw [h2]
    _ = _ := by group

theorem Chart4.V_le_S (c : Chart4 d α) (h : Hyp G A) : c.V ≤ d.S := by
  unfold Chart4.V
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact d.q_mem_S h
  · exact c.mem.1
  · exact d.S.mul_mem c.t_mem.2 c.mem.2.1

theorem Chart4.W_comm_V (c : Chart4 d α) {w v : G} (hw : w ∈ c.W) (hv : v ∈ c.V) :
    w * v = v * w := (mem_centralizer_iff.1 hw.2 v hv).symm

theorem Chart4.mem_W_of_comm (c : Chart4 d α) {s : G} (hs : s ∈ d.S)
    (hcomm : ∀ v ∈ c.V, s * v = v * s) : s ∈ c.W :=
  ⟨hs, mem_centralizer_iff.2 fun v hv => (hcomm v hv).symm⟩

theorem Chart4.t_mem_W (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (hα : α ≤ 1) : c.t ∈ c.W := by
  have hS := c.sFacts hα h hP hQ
  have ht : c.t ∈ d.S ⊓ centralizer (d.S : Set G) := by rw [hS.center]; exact mem_zpowers _
  refine c.mem_W_of_comm c.t_mem.2 fun v hv => ?_
  exact (mem_centralizer_iff.1 ht.2 v (c.V_le_S h hv)).symm

open Classical in
theorem Chart4.cover_pieces (c : Chart4 d α) {W' : Subgroup G} (hW' : W' ≤ d.X) :
    ∃ rp : Kind → G, (∀ w ∈ W', ∃ v ∈ ({1, rp Kind.field, rp Kind.graph, rp Kind.unitary} :
      Finset G), w * v⁻¹ ∈ W' ⊓ d.QS) ∧
      ∀ k, rp k ≠ 1 → ∃ w ∈ W', ∃ y, c.rep k = some y ∧ ∃ n ∈ d.QS, w = n * y := by
  classical
  let rp : Kind → G := fun k =>
    if hk : ∃ w ∈ W', ∃ y, c.rep k = some y ∧ ∃ n ∈ d.QS, w = n * y then hk.choose else 1
  have hrp : ∀ k, rp k ≠ 1 → ∃ w ∈ W', ∃ y, c.rep k = some y ∧ ∃ n ∈ d.QS, w = n * y := by
    intro k hk
    by_contra hcon
    exact hk (by simp only [rp, hcon, ↓reduceDIte])
  refine ⟨rp, ?_, hrp⟩
  intro w hw
  by_cases hwQS : w ∈ d.QS
  · exact ⟨1, by simp, by simpa using (⟨hw, hwQS⟩ : w ∈ W' ⊓ d.QS)⟩
  · obtain ⟨k, y₀, hrep, u, hu, rfl⟩ := c.cover w (hW' hw) hwQS
    have hk : ∃ w' ∈ W', ∃ y, c.rep k = some y ∧ ∃ n ∈ d.QS, w' = n * y :=
      ⟨u * y₀, hw, y₀, hrep, u, hu, rfl⟩
    have hspec : rp k = hk.choose := by simp only [rp, hk, ↓reduceDIte]
    obtain ⟨hw', y, hy, n, hn, hwn⟩ := hk.choose_spec
    rw [hrep] at hy
    obtain rfl : y₀ = y := Option.some_injective _ hy
    refine ⟨rp k, by cases k <;> simp, ?_⟩
    have hmem : u * y₀ * (rp k)⁻¹ ∈ W' := mul_mem hw (W'.inv_mem (by rw [hspec]; exact hw'))
    have hQS' : u * y₀ * (rp k)⁻¹ ∈ d.QS := by
      rw [hspec]
      have : u * y₀ * (hk.choose)⁻¹ = u * n⁻¹ := by rw [hwn]; group
      rw [this]
      exact mul_mem hu (d.QS.inv_mem hn)
    exact ⟨hmem, hQS'⟩

theorem Datum.comm_Q_S (d : Datum A) {q s : G} (hq : q ∈ d.Q) (hs : s ∈ d.S) : s * q = q * s :=
  mem_centralizer_iff.1 (d.Q_le_centralizer_S hq) s hs

theorem Chart4.ewit_eq_V (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (hS2 : chSec2OK = true) {W' E : Subgroup G} (hW' : W' ≤ d.X)
    (hW'card : Nat.card W' = 64) (hW'4 : ∀ x ∈ W', x ^ 4 = 1) (hES : E ≤ d.S)
    (hE8 : Nat.card E = 8) (hE2 : ∀ a ∈ E, a * a = 1) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEc : ∀ x ∈ W', ∀ a ∈ E, x * a = a * x) : E = c.V := by
  rcases c.ea8_fact hα h hP hS2 hES hEab hE2 hE8 with hEV | ⟨hC16, hexp⟩
  · exact hEV
  exfalso
  have hS := c.sFacts hα h hP hQ
  set W₀ : Subgroup G := W' ⊓ d.QS with hW₀
  have htE : c.t ∈ centralizer (E : Set G) := by
    have ht : c.t ∈ d.S ⊓ centralizer (d.S : Set G) := by rw [hS.center]; exact mem_zpowers _
    exact centralizer_le (fun a ha => hES ha) ht.2
  have hW₀le : W₀ ≤ d.S ⊓ centralizer (E : Set G) := by
    intro x hx
    obtain ⟨hxW, hxQS⟩ := hx
    obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hxQS
    have hsE : s ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h1 := hEc _ hxW a ha
      have h2 : a * u = u * a := d.comm_Q_S hu (hES ha)
      have h3 : u * (s * a) = u * (a * s) := by
        calc u * (s * a) = u * s * a := by group
          _ = a * (u * s) := h1
          _ = (a * u) * s := by group
          _ = (u * a) * s := by rw [h2]
          _ = u * (a * s) := by group
      exact (mul_left_cancel h3).symm
    have hs4 : s ^ 4 = 1 := hexp s ⟨hs, hsE⟩
    have hcomm : Commute u s := (d.comm_Q_S hu hs).symm
    have hu4 : u ^ 4 = 1 := by
      have := hW'4 _ hxW
      rw [hcomm.mul_pow, hs4, mul_one] at this
      exact this
    have hut : u ∈ zpowers c.t := c.mem_zpowers_t_of_pow_four h hu hu4
    have hu' : u ∈ d.S ⊓ centralizer (E : Set G) :=
      ⟨(zpowers_le.2 c.t_mem.2) hut, (zpowers_le.2 htE) hut⟩
    exact mul_mem hu' ⟨hs, hsE⟩
  have hW₀card : Nat.card W₀ ≤ 16 := (Subgroup.card_le_of_le hW₀le).trans hC16
  obtain ⟨rp, hcov, hrp⟩ := c.cover_pieces hW'
  have hcard := card_le_mul_of_cover (W₀ := W₀) _ hcov
  rw [hW'card] at hcard
  have hrp1 : ∀ k, rp k ≠ 1 := by
    intro k hk1
    classical
    have hws : ({1, rp Kind.field, rp Kind.graph, rp Kind.unitary} : Finset G).card ≤ 3 := by
      cases k
      · have : ({1, rp Kind.field, rp Kind.graph, rp Kind.unitary} : Finset G) ⊆
            {1, rp Kind.graph, rp Kind.unitary} := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl | rfl | rfl <;> simp_all
        exact (Finset.card_le_card this).trans Finset.card_le_three
      · have : ({1, rp Kind.field, rp Kind.graph, rp Kind.unitary} : Finset G) ⊆
            {1, rp Kind.field, rp Kind.unitary} := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl | rfl | rfl <;> simp_all
        exact (Finset.card_le_card this).trans Finset.card_le_three
      · have : ({1, rp Kind.field, rp Kind.graph, rp Kind.unitary} : Finset G) ⊆
            {1, rp Kind.field, rp Kind.graph} := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl | rfl | rfl <;> simp_all
        exact (Finset.card_le_card this).trans Finset.card_le_three
    have h48 := Nat.mul_le_mul hws hW₀card
    omega
  obtain ⟨w₁, hw₁, y₁, hrep₁, n₁, hn₁, rfl⟩ := hrp Kind.field (hrp1 _)
  obtain ⟨w₂, hw₂, y₂, hrep₂, n₂, hn₂, rfl⟩ := hrp Kind.graph (hrp1 _)
  obtain ⟨hy₁, -, hact₁⟩ := c.rep_mem _ _ hrep₁
  obtain ⟨hy₂, -, hact₂⟩ := c.rep_mem _ _ hrep₂
  obtain ⟨u₁, hu₁, s₁, hs₁, rfl⟩ := d.mem_QS_iff.1 hn₁
  obtain ⟨u₂, hu₂, s₂, hs₂, rfl⟩ := d.mem_QS_iff.1 hn₂
  refine c.pairFix_fact hα h hP hS2 hy₁ hy₂ hact₁ hact₂ hs₁ hs₂ hES hE2 hE8 fun a ha => ?_
  have hae := hES ha
  refine ⟨?_, ?_⟩
  · have h1 := hEc _ hw₁ a ha
    rw [← conj_QSy d hu₁ hae]
    calc (u₁ * s₁ * y₁)⁻¹ * a * (u₁ * s₁ * y₁) = (u₁ * s₁ * y₁)⁻¹ * ((u₁ * s₁ * y₁) * a) := by
          rw [h1]; group
      _ = a := by group
  · have h1 := hEc _ hw₂ a ha
    rw [← conj_QSy d hu₂ hae]
    calc (u₂ * s₂ * y₂)⁻¹ * a * (u₂ * s₂ * y₂) = (u₂ * s₂ * y₂)⁻¹ * ((u₂ * s₂ * y₂) * a) := by
          rw [h1]; group
      _ = a := by group

theorem Chart4.inter_QS_le_W (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) {W' : Subgroup G} (hW'4 : ∀ x ∈ W', x ^ 4 = 1)
    (hVc : ∀ x ∈ W', ∀ v ∈ c.V, x * v = v * x) : W' ⊓ d.QS ≤ c.W := by
  rintro x ⟨hxW, hxQS⟩
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hxQS
  have hsW : s ∈ c.W := c.mem_W_of_comm hs fun v hv => by
    have h1 := hVc _ hxW v hv
    have h2 : v * u = u * v := d.comm_Q_S hu (c.V_le_S h hv)
    have h3 : u * (s * v) = u * (v * s) := by
      calc u * (s * v) = u * s * v := by group
        _ = v * (u * s) := h1
        _ = (v * u) * s := by group
        _ = (u * v) * s := by rw [h2]
        _ = u * (v * s) := by group
    exact mul_left_cancel h3
  have hs4 : s ^ 4 = 1 := c.W_pow_four hα h hP hQ s hsW
  have hcomm : Commute u s := (d.comm_Q_S hu hs).symm
  have hu4 : u ^ 4 = 1 := by
    have := hW'4 _ hxW
    rw [hcomm.mul_pow, hs4, mul_one] at this
    exact this
  have hut : u ∈ zpowers c.t := c.mem_zpowers_t_of_pow_four h hu hu4
  exact mul_mem ((zpowers_le.2 (c.t_mem_W h hP hQ hα)) hut) hsW

theorem Chart4.centralizing_outside (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true) {x : G} (hx : x ∈ d.X)
    (hxQS : x ∉ d.QS) (hVc : ∀ v ∈ c.V, x * v = v * x) :
    ∃ y, c.rep Kind.graph = some y ∧ ∃ u ∈ d.Q, ∃ s ∈ c.W, x = u * s * y := by
  obtain ⟨k, y, hrep, n, hn, rfl⟩ := c.cover x hx hxQS
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 hn
  obtain ⟨hyX, -, hact⟩ := c.rep_mem k y hrep
  have hconj : ∀ v ∈ c.V, y⁻¹ * (s⁻¹ * v * s) * y = v := by
    intro v hv
    rw [← conj_QSy d hu (c.V_le_S h hv)]
    have := hVc v hv
    calc (u * s * y)⁻¹ * v * (u * s * y) = (u * s * y)⁻¹ * (v * (u * s * y)) := by group
      _ = (u * s * y)⁻¹ * ((u * s * y) * v) := by rw [← this]
      _ = v := by group
  by_cases hk : k = Kind.graph
  · subst hk
    refine ⟨y, hrep, u, hu, s, c.mem_W_of_comm hs fun v hv => ?_, rfl⟩
    have h1 := hconj v hv
    have h2 := c.graph_fixes_V hα h hP hQ hact v hv
    have h3 : s⁻¹ * v * s = v := by
      have : y⁻¹ * (s⁻¹ * v * s) * y = y⁻¹ * v * y := h1.trans h2.symm
      exact mul_left_cancel (mul_right_cancel this)
    calc s * v = s * (s⁻¹ * v * s) := by rw [h3]
      _ = v * s := by group
  · obtain ⟨v, hv, hne⟩ := c.notCent_V_fact hα h hP hS2 k hk hyX hact s hs
    exact absurd (hconj v hv) hne

theorem Chart4.unique_W
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    {W' : Subgroup G} (hW' : W' ≤ d.X) (hiso : Nonempty (↥W' ≃* ↥c.W)) : W' = c.W := by
  classical
  obtain ⟨e⟩ := hiso
  have hS := c.sFacts hα h hP hQ
  have hW4 := c.W_pow_four hα h hP hQ
  have hVS := c.V_le_S h
  have hVW : c.V ≤ c.W := fun v hv =>
    c.mem_W_of_comm (hVS hv) fun v' hv' => hS.V_comm v hv v' hv'
  obtain ⟨E, hEW', hE8, hE2, hEab, hEinv, hEc, hEsq⟩ := exists_Ewit e hVW hS.card_V hS.V_comm
    hS.V_sq hS.W_invol (fun w hw v hv => c.W_comm_V hw hv) (c.sq_V_fact hα h hP hS2)
  have hW'4 : ∀ x ∈ W', x ^ 4 = 1 := fun x hx => by
    have h1 := hW4 (e ⟨x, hx⟩ : G) (e ⟨x, hx⟩).2
    have h2 : (e ⟨x, hx⟩) ^ 4 = 1 := Subtype.ext (by simpa using h1)
    have h3 : (⟨x, hx⟩ : ↥W') ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h2, map_one]
    exact congrArg Subtype.val h3
  have hW'card : Nat.card W' = 64 := (Nat.card_congr e.toEquiv).trans hS.card_W
  have hES : E ≤ d.S := fun a ha => by
    obtain ⟨z, hz, hzz⟩ := hEsq a ha
    have : a ∈ d.QS := hzz ▸ c.sq_mem_QS hα h hP hQ (hW' hz)
    exact c.involutions_in_S' hα h hP hQ hc this (hE2 a ha)
  have hEV : E = c.V := c.ewit_eq_V hα h hP hQ hS2 hW' hW'card hW'4 hES hE8 hE2 hEab hEc
  have hVc : ∀ x ∈ W', ∀ v ∈ c.V, x * v = v * x := fun x hx v hv => hEc x hx v (hEV ▸ hv)
  have hW₁W := c.inter_QS_le_W hα h hP hQ hW'4 hVc
  by_cases hall : ∀ x ∈ W', x ∈ d.QS
  · exact Subgroup.eq_of_le_of_card_ge (fun x hx => hW₁W ⟨hx, hall x hx⟩)
      (by rw [hW'card, hS.card_W])
  push Not at hall
  obtain ⟨x₀, hx₀W, hx₀QS⟩ := hall
  obtain ⟨y, hrepg, u₀, hu₀, s₀, hs₀W, rfl⟩ :=
    c.centralizing_outside hα h hP hQ hS2 (hW' hx₀W) hx₀QS (hVc _ hx₀W)
  obtain ⟨hyX, -, hact⟩ := c.rep_mem Kind.graph y hrepg
  have hyyQ : y * y ∈ d.Q := c.sq_mem_Q hα h hP hQ Kind.graph hyX hact
  have hcov : ∀ w ∈ W', ∃ v ∈ ({1, u₀ * s₀ * y} : Finset G), w * v⁻¹ ∈ W' ⊓ d.QS := by
    intro w hw
    by_cases hwQS : w ∈ d.QS
    · exact ⟨1, by simp, by simpa using (⟨hw, hwQS⟩ : w ∈ W' ⊓ d.QS)⟩
    · obtain ⟨y', hrep', u, hu, s, hsW, rfl⟩ :=
        c.centralizing_outside hα h hP hQ hS2 (hW' hw) hwQS (hVc _ hw)
      rw [hrepg] at hrep'
      obtain rfl : y = y' := Option.some_injective _ hrep'
      refine ⟨u₀ * s₀ * y, by simp, mul_mem hw (W'.inv_mem hx₀W), ?_⟩
      have : u * s * y * (u₀ * s₀ * y)⁻¹ = u * s * (u₀ * s₀)⁻¹ := by group
      rw [this]
      exact mul_mem (d.mem_QS_iff.2 ⟨u, hu, s, hsW.1, rfl⟩)
        (d.QS.inv_mem (d.mem_QS_iff.2 ⟨u₀, hu₀, s₀, hs₀W.1, rfl⟩))
  have hW₁card : 32 ≤ Nat.card ↥(W' ⊓ d.QS) := by
    have hcard := card_le_mul_of_cover (W₀ := W' ⊓ d.QS) _ hcov
    have h2 : ({1, u₀ * s₀ * y} : Finset G).card ≤ 2 := Finset.card_le_two
    rw [hW'card] at hcard
    have := Nat.mul_le_mul_right (Nat.card ↥(W' ⊓ d.QS)) h2
    omega
  by_cases hα0 : α = 0
  ·
    exfalso
    subst hα0
    have hWab : ∀ a ∈ c.W, ∀ b ∈ c.W, a * b = b * a := hS.W_comm_iff.2 rfl
    have hW'ab : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := fun a ha b hb => by
      have h1 := hWab _ (e ⟨a, ha⟩).2 _ (e ⟨b, hb⟩).2
      have h2 : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h1
      exact congrArg Subtype.val (e.injective h2)
    have hzt : cj c.t y = c.t⁻¹ := by
      have h' := hact
      simp [Kind.Act] at h'
      exact h'.1
    have hW₁V : W' ⊓ d.QS ≤ c.V := by
      intro x hx
      have hxW := hW₁W hx
      have hcomm := hW'ab _ hx₀W x hx.1
      have h1 : (u₀ * s₀ * y)⁻¹ * x * (u₀ * s₀ * y) = x := by
        calc (u₀ * s₀ * y)⁻¹ * x * (u₀ * s₀ * y)
            = (u₀ * s₀ * y)⁻¹ * (x * (u₀ * s₀ * y)) := by group
          _ = (u₀ * s₀ * y)⁻¹ * ((u₀ * s₀ * y) * x) := by rw [← hcomm]
          _ = x := by group
      rw [conj_QSy d hu₀ hxW.1] at h1
      have h2 : s₀⁻¹ * x * s₀ = x := by
        have := hWab _ hs₀W _ hxW
        calc s₀⁻¹ * x * s₀ = s₀⁻¹ * (x * s₀) := by group
          _ = s₀⁻¹ * (s₀ * x) := by rw [this]
          _ = x := by group
      rw [h2] at h1
      exact (c.centralizer_graph_eq_V hα h hP hQ hyX hact hzt x hxW.1).1 h1
    have := Subgroup.card_le_of_le hW₁V
    rw [hS.card_V] at this
    omega
  · exfalso
    have hα1 : α = 1 := by omega
    obtain ⟨cc, hccdef⟩ : ∃ cc : G, cc = u₀ * (y * u₀ * y⁻¹) * (y * y) := ⟨_, rfl⟩
    have hsq0 := sq_QSy d hu₀ hs₀W.1 hyX hyyQ
    rw [← hccdef] at hsq0
    have hccQ : cc ∈ d.Q := by
      rw [hccdef]
      exact mul_mem (mul_mem hu₀ (d.conj_mem_Q hyX hu₀)) hyyQ
    have hx0sq : (u₀ * s₀ * y) * (u₀ * s₀ * y) ∈ c.W :=
      hW₁W ⟨mul_mem hx₀W hx₀W, c.sq_mem_QS hα h hP hQ (hW' hx₀W)⟩
    have hccS : cc ∈ d.S := by
      have h1 : cc = ((u₀ * s₀ * y) * (u₀ * s₀ * y)) * (s₀ * (y⁻¹ * s₀ * y))⁻¹ := by
        rw [hsq0]; group
      rw [h1]
      exact mul_mem hx0sq.1
        (d.S.inv_mem (mul_mem hs₀W.1 (d.conj_inv_mem_S hyX s₀ hs₀W.1)))
    have hcc_t : cc ∈ zpowers c.t := by rw [← c.Q_inf_S_eq hc]; exact ⟨hccQ, hccS⟩
    refine c.graph_fact hα1 h hP hS2 hyX hact hs₀W hcc_t (W' ⊓ d.QS) hW₁W hW₁card ?_
    intro x hx
    have hxW := hW₁W hx
    have hxS := hxW.1
    obtain ⟨w, hw⟩ : ∃ w : G, w = (u₀ * s₀ * y) * x := ⟨_, rfl⟩
    have hwW' : w ∈ W' := by rw [hw]; exact mul_mem hx₀W hx.1
    have hww : w * w = (cc * s₀ * (y⁻¹ * s₀ * y)) * (y⁻¹ * (s₀⁻¹ * x * s₀) * y) * x := by
      have h1 := conj_QSy d hu₀ hxS (s := s₀) (y := y)
      calc w * w = ((u₀ * s₀ * y) * (u₀ * s₀ * y)) *
            ((u₀ * s₀ * y)⁻¹ * x * (u₀ * s₀ * y)) * x := by rw [hw]; group
        _ = (cc * (s₀ * (y⁻¹ * s₀ * y))) * (y⁻¹ * (s₀⁻¹ * x * s₀) * y) * x := by rw [hsq0, h1]
        _ = _ := by group
    rw [← hww]
    have hw4 : (w * w) * (w * w) = 1 := by
      have := hW'4 w hwW'
      calc (w * w) * (w * w) = w ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    have hwwE : w * w ∈ E := hEinv _ (mul_mem hwW' hwW') hw4
    refine ⟨hEV ▸ hwwE, fun h1 => ?_⟩
    have hwE : w ∈ E := hEinv w hwW' h1
    have hwS : w ∈ d.S := hES hwE
    have hx0 : u₀ * s₀ * y ∈ d.QS := by
      have : u₀ * s₀ * y = w * x⁻¹ := by rw [hw]; group
      rw [this]
      exact mul_mem (mem_sup_right hwS) (d.QS.inv_mem hx.2)
    exact hx₀QS hx0

end CFSG.OddStandard.ChengHeld
