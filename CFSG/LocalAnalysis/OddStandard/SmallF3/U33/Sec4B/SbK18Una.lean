module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

private lemma comm_mem_V [Finite G] {Q Y V B : Subgroup G} {m : G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hBQ : B ≤ Q) (hYQ : Y ≤ Q) (hVY : V ≤ Y)
    (hQBY : ∀ q ∈ Q, ∃ b ∈ B, ∃ y ∈ Y, q = b * y) (hBY : ∀ x ∈ B, x ∈ Y → x ∈ V)
    (hmB : ∀ b ∈ B, m * b * m⁻¹ ∈ B)
    (hmQY : ∀ q ∈ Q, m * q * m⁻¹ * q⁻¹ ∈ Y)
    (hmYV : ∀ y ∈ Y, m * y * m⁻¹ * y⁻¹ ∈ V)
    {q : G} (hq : q ∈ Q) : m * q * m⁻¹ * q⁻¹ ∈ V := by
  obtain ⟨b, hbB, y, hyY, rfl⟩ := hQBY q hq
  have hbQ : b ∈ Q := hBQ hbB
  have hyQ : y ∈ Q := hYQ hyY
  set c : G := m * b * m⁻¹ * b⁻¹ with hc
  set d : G := m * y * m⁻¹ * y⁻¹ with hd
  have hcB : c ∈ B := by
    rw [hc]
    exact B.mul_mem (hmB b hbB) (B.inv_mem hbB)
  have hcY : c ∈ Y := by
    rw [hc]
    exact hmQY b hbQ
  have hcV : c ∈ V := hBY c hcB hcY
  have hdV : d ∈ V := by
    rw [hd]
    exact hmYV y hyY
  have hcQ : c ∈ Q := hYQ (hVY hcV)
  have hdQ : d ∈ Q := hYQ (hVY hdV)
  have hmb : m * b * m⁻¹ = c * b := by rw [hc]; group
  have hmy : m * y * m⁻¹ = d * y := by rw [hd]; group
  have hsplit : m * (b * y) * m⁻¹ = (m * b * m⁻¹) * (m * y * m⁻¹) := by group
  have hbyinv : (b * y)⁻¹ = y⁻¹ * b⁻¹ := by group
  have hbd : b * d = d * b := hQab b hbQ d hdQ
  have key : m * (b * y) * m⁻¹ * (b * y)⁻¹ = c * d := by
    calc
      m * (b * y) * m⁻¹ * (b * y)⁻¹
          = (m * b * m⁻¹) * (m * y * m⁻¹) * (b * y)⁻¹ := by rw [hsplit]
      _ = (m * b * m⁻¹) * (m * y * m⁻¹) * (y⁻¹ * b⁻¹) := by rw [hbyinv]
      _ = (c * b) * (d * y) * (y⁻¹ * b⁻¹) := by rw [hmb, hmy]
      _ = c * d := by
            rw [show (c * b) * (d * y) * (y⁻¹ * b⁻¹) = c * (b * d) * b⁻¹ by group, hbd]
            group
  rw [key]
  exact V.mul_mem hcV hdV

private lemma sq_centralizes [Finite G] {Q Y V B : Subgroup G} {m : G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hBQ : B ≤ Q) (hYQ : Y ≤ Q) (hVY : V ≤ Y)
    (hQBY : ∀ q ∈ Q, ∃ b ∈ B, ∃ y ∈ Y, q = b * y) (hBY : ∀ x ∈ B, x ∈ Y → x ∈ V)
    (hV2 : ∀ v ∈ V, v * v = 1)
    (hmQ : ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (hmB : ∀ b ∈ B, m * b * m⁻¹ ∈ B)
    (hmQY : ∀ q ∈ Q, m * q * m⁻¹ * q⁻¹ ∈ Y)
    (hmYV : ∀ y ∈ Y, m * y * m⁻¹ * y⁻¹ ∈ V)
    (hmV : ∀ v ∈ V, m * v * m⁻¹ = v) :
    ∀ q ∈ Q, (m * m) * q = q * (m * m) := by
  intro q hq
  set e : G := m * q * m⁻¹ * q⁻¹ with he
  have heV : e ∈ V := by
    rw [he]
    exact comm_mem_V hQab hBQ hYQ hVY hQBY hBY hmB hmQY hmYV hq
  have hmq : m * q * m⁻¹ = e * q := by rw [he]; group
  have hconj : (m * m) * q * (m * m)⁻¹ = q := by
    have hsplit1 : (m * m) * q * (m * m)⁻¹ = m * (m * q * m⁻¹) * m⁻¹ := by group
    rw [hsplit1, hmq]
    have hsplit2 : m * (e * q) * m⁻¹ = (m * e * m⁻¹) * (m * q * m⁻¹) := by group
    rw [hsplit2, hmV _ heV, hmq, ← mul_assoc, hV2 _ heV, one_mul]
  calc
    (m * m) * q = ((m * m) * q * (m * m)⁻¹) * (m * m) := by group
    _ = q * (m * m) := by rw [hconj]

private lemma actions_commute [Finite G] {Q Y V B : Subgroup G} {m n : G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hBQ : B ≤ Q) (hYQ : Y ≤ Q) (hVY : V ≤ Y)
    (hQBY : ∀ q ∈ Q, ∃ b ∈ B, ∃ y ∈ Y, q = b * y) (hBY : ∀ x ∈ B, x ∈ Y → x ∈ V)
    (hmB : ∀ b ∈ B, m * b * m⁻¹ ∈ B) (hnB : ∀ b ∈ B, n * b * n⁻¹ ∈ B)
    (hmQY : ∀ q ∈ Q, m * q * m⁻¹ * q⁻¹ ∈ Y)
    (hnQY : ∀ q ∈ Q, n * q * n⁻¹ * q⁻¹ ∈ Y)
    (hmYV : ∀ y ∈ Y, m * y * m⁻¹ * y⁻¹ ∈ V)
    (hnYV : ∀ y ∈ Y, n * y * n⁻¹ * y⁻¹ ∈ V)
    (hmV : ∀ v ∈ V, m * v * m⁻¹ = v) (hnV : ∀ v ∈ V, n * v * n⁻¹ = v) :
    ∀ q ∈ Q, m * (n * q * n⁻¹) * m⁻¹ = n * (m * q * m⁻¹) * n⁻¹ := by
  intro q hq
  set em : G := m * q * m⁻¹ * q⁻¹ with hem
  set en : G := n * q * n⁻¹ * q⁻¹ with hen
  have hemV : em ∈ V := by
    rw [hem]
    exact comm_mem_V hQab hBQ hYQ hVY hQBY hBY hmB hmQY hmYV hq
  have henV : en ∈ V := by
    rw [hen]
    exact comm_mem_V hQab hBQ hYQ hVY hQBY hBY hnB hnQY hnYV hq
  have hemQ : em ∈ Q := hYQ (hVY hemV)
  have henQ : en ∈ Q := hYQ (hVY henV)
  have hmq : m * q * m⁻¹ = em * q := by rw [hem]; group
  have hnq : n * q * n⁻¹ = en * q := by rw [hen]; group
  have hL : m * (n * q * n⁻¹) * m⁻¹ = en * em * q := by
    rw [hnq]
    have hsplit : m * (en * q) * m⁻¹ = (m * en * m⁻¹) * (m * q * m⁻¹) := by group
    rw [hsplit, hmV _ henV, hmq]
    group
  have hR : n * (m * q * m⁻¹) * n⁻¹ = em * en * q := by
    rw [hmq]
    have hsplit : n * (em * q) * n⁻¹ = (n * em * n⁻¹) * (n * q * n⁻¹) := by group
    rw [hsplit, hnV _ hemV, hnq]
    group
  rw [hL, hR]
  exact congrArg (· * q) (hQab en henQ em hemQ)

theorem comm_sq_centralize_of_unipotent [Finite G] {Q Y V B : Subgroup G} {m n : G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hBQ : B ≤ Q) (hYQ : Y ≤ Q) (hVY : V ≤ Y)
    (hQBY : ∀ q ∈ Q, ∃ b ∈ B, ∃ y ∈ Y, q = b * y) (hBY : ∀ x ∈ B, x ∈ Y → x ∈ V)
    (hV2 : ∀ v ∈ V, v * v = 1)
    (hmQ : ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (hnQ : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q)
    (hmB : ∀ b ∈ B, m * b * m⁻¹ ∈ B) (hnB : ∀ b ∈ B, n * b * n⁻¹ ∈ B)
    (hmQY : ∀ q ∈ Q, m * q * m⁻¹ * q⁻¹ ∈ Y) (hnQY : ∀ q ∈ Q, n * q * n⁻¹ * q⁻¹ ∈ Y)
    (hmYV : ∀ y ∈ Y, m * y * m⁻¹ * y⁻¹ ∈ V) (hnYV : ∀ y ∈ Y, n * y * n⁻¹ * y⁻¹ ∈ V)
    (hmV : ∀ v ∈ V, m * v * m⁻¹ = v) (hnV : ∀ v ∈ V, n * v * n⁻¹ = v) :
    (∀ q ∈ Q, (m * n * m⁻¹ * n⁻¹) * q = q * (m * n * m⁻¹ * n⁻¹)) ∧
      ∀ q ∈ Q, (m * m) * q = q * (m * m) := by
  have hmN : m ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype (fun q hq => hmQ q hq)
  have hnN : n ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype (fun q hq => hnQ q hq)
  constructor
  · intro q hq
    have hxQ : m⁻¹ * n⁻¹ * q * n * m ∈ Q := by
      have hnm : n * m ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.mul_mem _ hnN hmN
      have hqiff : q ∈ Q ↔ (n * m)⁻¹ * q * (n * m) ∈ Q :=
        (Subgroup.mem_normalizer_iff''.mp hnm) q
      have hxEq : m⁻¹ * n⁻¹ * q * n * m = (n * m)⁻¹ * q * (n * m) := by group
      rw [hxEq]
      exact hqiff.mp hq
    have hE := actions_commute hQab hBQ hYQ hVY hQBY hBY hmB hnB hmQY hnQY hmYV hnYV hmV hnV
      (m⁻¹ * n⁻¹ * q * n * m) hxQ
    have hL : m * (n * (m⁻¹ * n⁻¹ * q * n * m) * n⁻¹) * m⁻¹
        = (m * n * m⁻¹ * n⁻¹) * q * (m * n * m⁻¹ * n⁻¹)⁻¹ := by group
    have hR : n * (m * (m⁻¹ * n⁻¹ * q * n * m) * m⁻¹) * n⁻¹ = q := by group
    rw [hL, hR] at hE
    calc
      (m * n * m⁻¹ * n⁻¹) * q
          = ((m * n * m⁻¹ * n⁻¹) * q * (m * n * m⁻¹ * n⁻¹)⁻¹) * (m * n * m⁻¹ * n⁻¹) := by
            group
      _ = q * (m * n * m⁻¹ * n⁻¹) := by rw [hE]
  · exact sq_centralizes hQab hBQ hYQ hVY hQBY hBY hV2 hmQ hmB hmQY hmYV hmV

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
