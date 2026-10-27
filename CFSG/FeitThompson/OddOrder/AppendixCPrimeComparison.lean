module

public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
import CFSG.FeitThompson.OddOrder.InversionClosurePrimeBound
import CFSG.FeitThompson.OddOrder.DoubleNormNontrivialPoint
import CFSG.FeitThompson.OddOrder.GroupInversionClosure

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Multiplicative Subgroup

variable {p q m : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

theorem conj_mem_of_conj_law {P U : Subgroup G} (Pe : Multiplicative F ≃* P)
    (Ue : normOneSubgroup F m ≃* U)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    (w : normOneSubgroup F m) {x : G} (hx : x ∈ P) :
    (Ue w : G)⁻¹ * x * (Ue w : G) ∈ P := by
  obtain ⟨z, rfl⟩ : ∃ z : F, ((Pe (ofAdd z) : P) : G) = x := ⟨toAdd (Pe.symm ⟨x, hx⟩), by simp⟩
  rw [hact]
  exact (Pe _).2

theorem le_normalizer_of_conj_law {P U : Subgroup G} (Pe : Multiplicative F ≃* P)
    (Ue : normOneSubgroup F m ≃* U)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G)) :
    P ⊔ U ≤ normalizer (P : Set G) := by
  refine sup_le le_normalizer fun g hg => ?_
  obtain ⟨w, rfl⟩ : ∃ w : normOneSubgroup F m, ((Ue w : U) : G) = g := ⟨Ue.symm ⟨g, hg⟩, by simp⟩
  have hinv : ((Ue w⁻¹ : U) : G) = ((Ue w : U) : G)⁻¹ := by rw [map_inv, Subgroup.coe_inv]
  refine mem_set_normalizer_iff.2 fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · have := conj_mem_of_conj_law Pe Ue hact w⁻¹ hn
    rwa [hinv, inv_inv] at this
  · have := conj_mem_of_conj_law Pe Ue hact w hn
    simpa [mul_assoc] using this

theorem prime_le_of_appendixC_config [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneSubgroup F m ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G)) :
    p ≤ q := by
  by_contra hlt
  have hqp : q < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  have hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m := fun z hz =>
    inv_mem_normOneShiftSet_of_mem hp hq hqp hcard hm hcop Pe Ue hPU hact hH hP₀ rfl hQab hQp
      hQnorm hy hP₁ hP₁U rfl hz
  exact absurd (le_of_exists_ne_one_mem_normOneShiftSet hq hcard hm hcop hinv
    (exists_ne_one_mem_normOneShiftSet_of_config hp hq hqp hcard hm hcop)) (by omega)

end CFSG.FeitThompson
