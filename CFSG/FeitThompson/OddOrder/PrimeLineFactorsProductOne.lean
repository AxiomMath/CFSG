module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Multiplicative Subgroup

variable {G : Type*} [Group G]

private theorem mul_inv_mul_mul_mul_mul_of_commute {a b₁ b₂ b₃ : G}
    (hab₂ : Commute a b₂) (hab₃ : Commute a b₃) (h₁₂ : Commute b₁ b₂) (h₁₃ : Commute b₁ b₃) :
    a * b₂⁻¹ * a * (b₁ * b₂ * b₃) = b₃ * a ^ 2 * b₁ := by
  have e1 : b₂⁻¹ * a = a * b₂⁻¹ := hab₂.symm.inv_left.eq
  have e2 : b₂⁻¹ * b₁ = b₁ * b₂⁻¹ := h₁₂.symm.inv_left.eq
  calc a * b₂⁻¹ * a * (b₁ * b₂ * b₃)
      = a * (b₂⁻¹ * a) * b₁ * b₂ * b₃ := by group
    _ = a * (a * b₂⁻¹) * b₁ * b₂ * b₃ := by rw [e1]
    _ = a * a * (b₂⁻¹ * b₁) * b₂ * b₃ := by group
    _ = a * a * (b₁ * b₂⁻¹) * b₂ * b₃ := by rw [e2]
    _ = a * a * b₁ * b₃ := by group
    _ = a * a * (b₃ * b₁) := by rw [mul_assoc, h₁₃.eq]
    _ = b₃ * (a * a) * b₁ := by rw [← mul_assoc, ← (hab₃.mul_left hab₃).eq]
    _ = b₃ * a ^ 2 * b₁ := by rw [sq]

private theorem inv_mul_eq_mul_inv_of_mul_eq_mul {A B q₁ q₂ : G} (h : A * q₁ = B * q₂) :
    B⁻¹ * A = q₂ * q₁⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]

theorem mul_mul_mem_of_conj_word_eq {P₀ Q : Subgroup G} [IsMulCommutative P₀]
    (hnorm : P₀ ≤ normalizer (Q : Set G)) {s y t r₁ r₂ r₃ : G} (hs : s ∈ P₀) (hy : y ∈ Q)
    (ht : t = y⁻¹ * s * y) (h₁ : r₁ ∈ P₀) (h₂ : r₂ ∈ P₀) (h₃ : r₃ ∈ P₀)
    (hw : t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁) : r₁ * r₂ * r₃ ∈ Q := by
  have hconj : ∀ r ∈ P₀, ∀ c ∈ Q, r * c * r⁻¹ ∈ Q := fun r hr c hc =>
    (mem_normalizer_iff.mp (hnorm hr) c).mp hc
  have hconj' : ∀ r ∈ P₀, ∀ c ∈ Q, r⁻¹ * c * r ∈ Q := fun r hr c hc => by
    simpa using hconj r⁻¹ (inv_mem hr) c hc
  set c := s⁻¹ * t with hcdef
  have hcQ : c ∈ Q := by
    have h : c = s⁻¹ * y⁻¹ * s * y := by rw [hcdef, ht]; group
    rw [h]
    exact mul_mem (by simpa using hconj' s hs y⁻¹ (inv_mem hy)) hy
  have ht' : t = s * c := by rw [hcdef]; group
  have hL : t * r₂⁻¹ * t = s * r₂⁻¹ * s * (s⁻¹ * (r₂ * c * r₂⁻¹) * s * c) := by
    rw [ht']; group
  have hR : r₃ * t ^ 2 * r₁ = r₃ * s ^ 2 * r₁ * (r₁⁻¹ * (s⁻¹ * c * s * c) * r₁) := by
    rw [ht']; simp only [sq]; group
  have hq₁ : s⁻¹ * (r₂ * c * r₂⁻¹) * s * c ∈ Q :=
    mul_mem (hconj' s hs _ (hconj r₂ h₂ c hcQ)) hcQ
  have hq₂ : r₁⁻¹ * (s⁻¹ * c * s * c) * r₁ ∈ Q :=
    hconj' r₁ h₁ _ (mul_mem (hconj' s hs c hcQ) hcQ)
  have hEq : s * r₂⁻¹ * s * (s⁻¹ * (r₂ * c * r₂⁻¹) * s * c)
      = r₃ * s ^ 2 * r₁ * (r₁⁻¹ * (s⁻¹ * c * s * c) * r₁) := by rw [← hL, hw, hR]
  have hmem : (r₃ * s ^ 2 * r₁)⁻¹ * (s * r₂⁻¹ * s) ∈ Q := by
    rw [inv_mul_eq_mul_inv_of_mul_eq_mul hEq]
    exact mul_mem hq₂ (inv_mem hq₁)
  have hkey : (r₃ * s ^ 2 * r₁)⁻¹ * (s * r₂⁻¹ * s) = (r₁ * r₂ * r₃)⁻¹ := by
    have h := mul_inv_mul_mul_mul_mul_of_commute (a := s) (b₁ := r₁) (b₂ := r₂) (b₃ := r₃)
      (setLike_mul_comm hs h₂) (setLike_mul_comm hs h₃)
      (setLike_mul_comm h₁ h₂) (setLike_mul_comm h₁ h₃)
    rw [← h]; group
  rw [hkey] at hmem
  simpa using inv_mem hmem

theorem mul_mul_eq_one_of_conj_word_eq {P₀ Q : Subgroup G} [IsMulCommutative P₀]
    (hcop : (Nat.card P₀).Coprime (Nat.card Q)) (hnorm : P₀ ≤ normalizer (Q : Set G))
    {s y t r₁ r₂ r₃ : G} (hs : s ∈ P₀) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y)
    (h₁ : r₁ ∈ P₀) (h₂ : r₂ ∈ P₀) (h₃ : r₃ ∈ P₀)
    (hw : t * r₂⁻¹ * t = r₃ * t ^ 2 * r₁) : r₁ * r₂ * r₃ = 1 :=
  disjoint_def.mp (disjoint_of_coprime_natCard hcop) (mul_mem (mul_mem h₁ h₂) h₃)
    (mul_mul_mem_of_conj_word_eq hnorm hs hy ht h₁ h₂ h₃ hw)

theorem isMulCommutative_map {A : Type*} [CommGroup A] (S : Subgroup A) (f : A →* G) :
    IsMulCommutative ↥(S.map f) := by
  rw [isMulCommutative_iff_of_setLike]
  rintro a ha b hb
  rw [Subgroup.mem_map] at ha hb
  obtain ⟨x, -, rfl⟩ := ha
  obtain ⟨z, -, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem natCard_map_primeSubfield {p q : ℕ} (hp : p.Prime) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = p ^ q) (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe) :
    Nat.card ((AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup).map Pe) = p := by
  have := Fact.mk hp
  have : CharP F p := charP_of_card_eq_prime_pow hF
  rw [Subgroup.card_map_of_injective hPe, ← Subfield.card_bot F p]
  exact Nat.card_congr
    { toFun := fun x => ⟨toAdd x.1, x.2⟩, invFun := fun x => ⟨ofAdd x.1, x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

theorem map_ofAdd_mem_map_primeSubfield {F : Type*} [Field F] (Pe : Multiplicative F →* G) {z : F}
    (hz : z ∈ (⊥ : Subfield F)) :
    Pe (ofAdd z) ∈ (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup).map Pe :=
  ⟨ofAdd z, hz, rfl⟩

theorem mul_mul_eq_one_of_conj_word_eq_primeSubfield
    {p q : ℕ} (hp : p.Prime) {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = p ^ q)
    (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    {Q : Subgroup G} (hQ : (Nat.card Q).Coprime p)
    (hnorm : ∀ z ∈ (⊥ : Subfield F), Pe (ofAdd z) ∈ normalizer (Q : Set G))
    {y : G} (hy : y ∈ Q) {t : G} (ht : t = y⁻¹ * Pe (ofAdd (1 : F)) * y)
    {z₁ z₂ z₃ : F} (hz₁ : z₁ ∈ (⊥ : Subfield F)) (hz₂ : z₂ ∈ (⊥ : Subfield F))
    (hz₃ : z₃ ∈ (⊥ : Subfield F))
    (hw : t * (Pe (ofAdd z₂))⁻¹ * t = Pe (ofAdd z₃) * t ^ 2 * Pe (ofAdd z₁)) :
    Pe (ofAdd z₁) * Pe (ofAdd z₂) * Pe (ofAdd z₃) = 1 := by
  set P₀ := (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup).map Pe with hP₀
  have : IsMulCommutative P₀ := isMulCommutative_map _ _
  have hcop : (Nat.card P₀).Coprime (Nat.card Q) := by
    rw [hP₀, natCard_map_primeSubfield hp hF Pe hPe]
    exact hQ.symm
  refine mul_mul_eq_one_of_conj_word_eq hcop ?_
    (map_ofAdd_mem_map_primeSubfield Pe (one_mem _)) hy ht
    (map_ofAdd_mem_map_primeSubfield Pe hz₁) (map_ofAdd_mem_map_primeSubfield Pe hz₂)
    (map_ofAdd_mem_map_primeSubfield Pe hz₃) hw
  rintro x hx
  rw [hP₀, Subgroup.mem_map] at hx
  obtain ⟨w, hw', rfl⟩ := hx
  exact hnorm (toAdd w) hw'

end CFSG.FeitThompson

end
