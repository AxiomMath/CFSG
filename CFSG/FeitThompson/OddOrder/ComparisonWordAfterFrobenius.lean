module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
import CFSG.FeitThompson.OddOrder.ThreeNormalFormsComparisonWord
import CFSG.FeitThompson.OddOrder.NormalFormFrobeniusTransport

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {F : Type*} [Field F]

theorem conj_mul_pow_of_mem_normalizer (U : Subgroup G) [IsMulCommutative U] {g x y : G}
    (hg : g ∈ normalizer (U : Set G)) (hx : x ∈ U) (hy : y ∈ U) (n : ℕ) :
    (g * x * g⁻¹ * y) ^ n = g * x ^ n * g⁻¹ * y ^ n := by
  have hgx : g * x * g⁻¹ ∈ U := ((Subgroup.mem_normalizer_iff (H := U) (g := g)).1 hg x).1 hx
  rw [Commute.mul_pow (setLike_mul_comm hgx hy), conj_pow]

theorem mul_conj_pow_of_mem_normalizer (U : Subgroup G) [IsMulCommutative U] {g x y : G}
    (hg : g ∈ normalizer (U : Set G)) (hx : x ∈ U) (hy : y ∈ U) (n : ℕ) :
    (y * (g * x * g⁻¹)) ^ n = y ^ n * (g * x ^ n * g⁻¹) := by
  have hgx : g * x * g⁻¹ ∈ U := ((Subgroup.mem_normalizer_iff (H := U) (g := g)).1 hg x).1 hx
  rw [Commute.mul_pow (setLike_mul_comm hy hgx), conj_pow]

theorem comparison_word_pow_of_normalForms {Q U : Subgroup G} [IsMulCommutative Q]
    [IsMulCommutative U] {s y t A B : G} (hsQ : s ∈ normalizer (Q : Set G)) (hy : y ∈ Q)
    (ht : t = y⁻¹ * s * y) (htU : t ∈ normalizer (U : Set G))
    (hAB : (A⁻¹ * s * A) * (B⁻¹ * s * B) = s ^ 2)
    {u₁ u₂ u₃ v₁ v₂ v₃ r₁ r₂ r₃ w₁ w₂ w₃ : G}
    (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hu₃ : u₃ ∈ U)
    (hv₁ : v₁ ∈ U) (hv₂ : v₂ ∈ U) (hv₃ : v₃ ∈ U) (n : ℕ)
    (h₁ : s * ((t ^ 3)⁻¹ * A⁻¹ * t ^ 3) * (s ^ 2)⁻¹ = u₁ ^ n * r₁ * v₁ ^ n)
    (h₂ : s ^ 3 * ((t ^ 2)⁻¹ * (A * B⁻¹) * t ^ 2) * s⁻¹ = u₂ ^ n * r₂ * v₂ ^ n)
    (h₃ : s ^ 2 * (t⁻¹ * B * t) * (s ^ 3)⁻¹ = u₃ ^ n * r₃ * v₃ ^ n)
    (hw₁ : w₁ = t * v₂ * t⁻¹ * u₃) (hw₂ : w₂ = v₃ * (t ^ 2 * u₁ * (t ^ 2)⁻¹))
    (hw₃ : w₃ = v₁ * (t⁻¹ * u₂ * t)) :
    t * r₂⁻¹ * t = w₁ ^ n * r₃ * w₂ ^ n * t ^ 2 * r₁ * w₃ ^ n := by
  have e₁ : w₁ ^ n = t * v₂ ^ n * t⁻¹ * u₃ ^ n := by
    rw [hw₁]; exact conj_mul_pow_of_mem_normalizer U htU hv₂ hu₃ n
  have e₂ : w₂ ^ n = v₃ ^ n * (t ^ 2 * u₁ ^ n * (t ^ 2)⁻¹) := by
    rw [hw₂]; exact mul_conj_pow_of_mem_normalizer U (pow_mem htU 2) hu₁ hv₃ n
  have e₃ : w₃ ^ n = v₁ ^ n * (t⁻¹ * u₂ ^ n * t) := by
    have h := mul_conj_pow_of_mem_normalizer U (inv_mem htU) hu₂ hv₁ n
    rw [hw₃]; simpa using h
  rw [e₁, e₂, e₃]
  exact comparison_word_of_normalForms hsQ hy ht hAB h₁ h₂ h₃ rfl rfl rfl

theorem comparison_word_and_pow
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {P U : Subgroup G}
    (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U) (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (_hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹).toMonoidHom) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) (_hyc : y ∈ ⁅Q, P₀⁆)
    {a b : normOneUnits F} (hab : ((a : Fˣ) : F) + ((b : Fˣ) : F) = 2)
    {u₁ u₂ u₃ v₁ v₂ v₃ : normOneUnits F} {c₁ c₂ c₃ : F}
    (hc₁ : c₁ ∈ (⊥ : Subfield F)) (hc₂ : c₂ ∈ (⊥ : Subfield F)) (hc₃ : c₃ ∈ (⊥ : Subfield F))
    {r₁ r₂ r₃ : G} (hr₁ : r₁ = (Pe (ofAdd c₁) : G)) (hr₂ : r₂ = (Pe (ofAdd c₂) : G))
    (hr₃ : r₃ = (Pe (ofAdd c₃) : G))
    (h₁ : s * ((t ^ 3)⁻¹ * (Ue a : G)⁻¹ * t ^ 3) * (s ^ 2)⁻¹ = (Ue u₁ : G) * r₁ * (Ue v₁ : G))
    (h₂ : s ^ 3 * ((t ^ 2)⁻¹ * ((Ue a : G) * (Ue b : G)⁻¹) * t ^ 2) * s⁻¹
      = (Ue u₂ : G) * r₂ * (Ue v₂ : G))
    (h₃ : s ^ 2 * (t⁻¹ * (Ue b : G) * t) * (s ^ 3)⁻¹ = (Ue u₃ : G) * r₃ * (Ue v₃ : G))
    {w₁ w₂ w₃ : G} (hw₁ : w₁ = t * (Ue v₂ : G) * t⁻¹ * (Ue u₃ : G))
    (hw₂ : w₂ = (Ue v₃ : G) * (t ^ 2 * (Ue u₁ : G) * (t ^ 2)⁻¹))
    (hw₃ : w₃ = (Ue v₁ : G) * (t⁻¹ * (Ue u₂ : G) * t)) :
    t * r₂⁻¹ * t = w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃ ∧
      t * r₂⁻¹ * t = w₁ ^ p * r₃ * w₂ ^ p * t ^ 2 * r₁ * w₃ ^ p := by
  subst hr₁ hr₂ hr₃
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have hchar : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  have hPmul : ∀ z w : F, (Pe (ofAdd (z + w)) : G) = (Pe (ofAdd z) : G) * (Pe (ofAdd w) : G) := by
    intro z w; rw [ofAdd_add, map_mul, Subgroup.coe_mul]
  have hQcomm : IsMulCommutative Q :=
    IsMulCommutative.of_comm fun x z => Subtype.ext (hQab x x.2 z z.2)
  have hUcomm : IsMulCommutative U := by
    refine IsMulCommutative.of_comm fun x z => ?_
    have h := mul_comm (Ue.symm x) (Ue.symm z)
    calc x * z = Ue (Ue.symm x * Ue.symm z) := by simp
      _ = Ue (Ue.symm z * Ue.symm x) := by rw [h]
      _ = z * x := by simp
  have hUpow : ∀ (z : normOneUnits F) (n : ℕ), (Ue (z ^ n) : G) = (Ue z : G) ^ n := by
    intro z n; rw [map_pow, Subgroup.coe_pow]
  have hsP₀ : s ∈ P₀ := by rw [hP₀, hs]; exact apply_ofAdd_mem_primeLine _ (one_mem _)
  have hsQ : s ∈ normalizer (Q : Set G) := hQnorm hsP₀
  have htP₁ : t ∈ P₁ := by rw [hP₁, ht]; exact ⟨s, hsP₀, by simp [MulAut.conj]⟩
  have htU : t ∈ normalizer (U : Set G) := hP₁U htP₁
  refine ⟨comparison_word_of_add_eq_two (P := fun z => (Pe (ofAdd z) : G)) hPmul hs hsQ hy ht
    hab (fun z => hact z a) (fun z => hact z b) h₁ h₂ h₃ hw₁ hw₂ hw₃, ?_⟩
  have habp :
      (((a ^ p : normOneUnits F) : Fˣ) : F) + (((b ^ p : normOneUnits F) : Fˣ) : F) = 2 := by
    have h2 : ((2 : F)) ^ p = 2 := (Subfield.mem_bot_iff_pow_eq_self F p).1 (by simp)
    have h : (((a : Fˣ) : F) + ((b : Fˣ) : F)) ^ p = 2 := by rw [hab, h2]
    rw [add_pow_char] at h
    simpa using h
  have key := fun (i j k : ℤ) (c : F) (hc : c ∈ (⊥ : Subfield F)) (z u v : normOneUnits F) =>
    mul_pow_mul_eq_of_mul_mul_eq (q := q) hp hq hqp hcard hcop Pe Ue hPU hact
      (H := P ⊔ U) (P₀ := P₀) (P₁ := P₁) (Q := Q) rfl hP₀ hs hQab hQp hQnorm hy hP₁ hP₁U ht
      (i := i) (j := j) (k := k) (a := z) (u := u) (v := v) (c := c) hc
  have k₁ : s * ((t ^ 3)⁻¹ * (Ue (a ^ p) : G)⁻¹ * t ^ 3) * (s ^ 2)⁻¹
      = (Ue u₁ : G) ^ p * (Pe (ofAdd c₁) : G) * (Ue v₁ : G) ^ p := by
    have h := key 1 3 2 c₁ hc₁ a⁻¹ u₁ v₁ (by simpa using h₁)
    rw [show (Ue (a ^ p) : G)⁻¹ = (Ue a⁻¹ : G) ^ p by
      rw [hUpow a p, map_inv, Subgroup.coe_inv, inv_pow]]
    simpa using h
  have k₂ : s ^ 3 * ((t ^ 2)⁻¹ * ((Ue (a ^ p) : G) * (Ue (b ^ p) : G)⁻¹) * t ^ 2) * s⁻¹
      = (Ue u₂ : G) ^ p * (Pe (ofAdd c₂) : G) * (Ue v₂ : G) ^ p := by
    have h := key 3 2 1 c₂ hc₂ (a * b⁻¹) u₂ v₂ (by simpa using h₂)
    rw [show (Ue (a ^ p) : G) * (Ue (b ^ p) : G)⁻¹ = (Ue (a * b⁻¹) : G) ^ p by
      rw [hUpow a p, hUpow b p, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        Commute.mul_pow (setLike_mul_comm (Ue a).2 (inv_mem (Ue b).2)), inv_pow]]
    simpa using h
  have k₃ : s ^ 2 * (t⁻¹ * (Ue (b ^ p) : G) * t) * (s ^ 3)⁻¹
      = (Ue u₃ : G) ^ p * (Pe (ofAdd c₃) : G) * (Ue v₃ : G) ^ p := by
    have h := key 2 1 3 c₃ hc₃ b u₃ v₃ (by simpa using h₃)
    rw [hUpow b p]
    simpa using h
  have hAB : ((Ue (a ^ p) : G)⁻¹ * s * (Ue (a ^ p) : G))
      * ((Ue (b ^ p) : G)⁻¹ * s * (Ue (b ^ p) : G)) = s ^ 2 := by
    rw [hs, hact 1 (a ^ p), hact 1 (b ^ p), one_mul, one_mul, ← hPmul, habp,
      ← one_add_one_eq_two, hPmul, pow_two]
  exact comparison_word_pow_of_normalForms hsQ hy ht htU hAB (Ue u₁).2 (Ue u₂).2 (Ue u₃).2
    (Ue v₁).2 (Ue v₂).2 (Ue v₃).2 p k₁ k₂ k₃ hw₁ hw₂ hw₃

end

end CFSG.FeitThompson
