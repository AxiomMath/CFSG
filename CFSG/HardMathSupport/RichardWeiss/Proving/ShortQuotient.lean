module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortCommutator

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open scoped commutatorElement

variable {G : Type*} [Group G]

structure ShortData (Q L V S : Subgroup G) : Prop where
  hQM : Q ≤ L ⊔ S
  hQS : Q ≤ S
  hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L
  hMV : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V
  hVQ : V ≤ Q
  hQV : ∀ q ∈ Q, ∀ v ∈ V, q * v = v * q
  hV2 : ∀ v ∈ V, v * v = 1
  hperf : ⁅L, L⁆ = L
  hshort : ⁅Q, L⁆ ≤ V

variable {Q L V S : Subgroup G}

namespace ShortData

variable (D : ShortData Q L V S)
include D

theorem conj_eq (q : G) (hq : q ∈ Q) (l : G) (hl : l ∈ L) :
    ∃ v ∈ V, l * q * l⁻¹ = v * q := by
  have h : ⁅l, q⁆ ∈ V := by
    have := Subgroup.commutator_mem_commutator hl hq
    rw [Subgroup.commutator_comm] at this
    exact D.hshort this
  refine ⟨⁅l, q⁆, h, ?_⟩
  simp only [commutatorElement_def]; group

theorem comm_mul_left {z : G} (hz : z ∈ V) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hab : a * b * a⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)
  have h : z * (a * b * a⁻¹) = (a * b * a⁻¹) * z := (D.hQV _ hab z hz).symm
  have h2 : z * a * b * a⁻¹ * z⁻¹ = a * b * a⁻¹ := by
    calc z * a * b * a⁻¹ * z⁻¹ = z * (a * b * a⁻¹) * z⁻¹ := by group
      _ = (a * b * a⁻¹) * z * z⁻¹ := by rw [h]
      _ = a * b * a⁻¹ := by group
  simp only [commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = (z * a * b * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

theorem comm_mul_right {z : G} (hz : z ∈ V) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have h := D.comm_mul_left hz hb ha
  have e1 : ⁅a, z * b⁆ = (⁅z * b, a⁆)⁻¹ := (commutatorElement_inv _ _).symm
  rw [e1, h, ← commutatorElement_inv]; simp

theorem conj_commutator {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) {l : G} (hl : l ∈ L) :
    l * ⁅x, y⁆ * l⁻¹ = ⁅x, y⁆ := by
  obtain ⟨v₁, hv₁, h₁⟩ := D.conj_eq x hx l hl
  obtain ⟨v₂, hv₂, h₂⟩ := D.conj_eq y hy l hl
  have e : l * ⁅x, y⁆ * l⁻¹ = ⁅l * x * l⁻¹, l * y * l⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, h₁, h₂, D.comm_mul_left hv₁ hx (Q.mul_mem (D.hVQ hv₂) hy),
    D.comm_mul_right hv₂ hx hy]

theorem conj_sq {y : G} (hy : y ∈ Q) {l : G} (hl : l ∈ L) :
    l * (y * y) * l⁻¹ = y * y := by
  obtain ⟨v, hv, h⟩ := D.conj_eq y hy l hl
  have e : l * (y * y) * l⁻¹ = (l * y * l⁻¹) * (l * y * l⁻¹) := by group
  rw [e, h]
  have hc : y * v = v * y := D.hQV y hy v hv
  calc v * y * (v * y) = v * (y * v) * y := by group
    _ = v * (v * y) * y := by rw [hc]
    _ = (v * v) * y * y := by group
    _ = y * y := by rw [D.hV2 v hv]; group

end ShortData

end CFSG.HardMathSupport.RichardWeiss.Proving
