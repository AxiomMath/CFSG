module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.OddOrder.CommutatorConjugatorReduction
import CFSG.FeitThompson.OddOrder.ShiftedInversePreservesNormPoints
import CFSG.FeitThompson.OddOrder.MobiusNormIteration

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Multiplicative Subgroup

variable {p q m : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

private theorem primeLine_eq_map_zpowers_ofAdd_one [Fact p.Prime] [CharP F p]
    (Pe : Multiplicative F →* G) :
    primeLine Pe = (Subgroup.zpowers (ofAdd (1 : F))).map Pe := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨c, hc, rfl⟩ := mem_primeLine.1 hg
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp hc
    refine ⟨ofAdd (1 : F) ^ n, ⟨n, rfl⟩, ?_⟩
    rw [← ofAdd_zsmul, ← hn, zsmul_eq_mul, mul_one]
  · rintro g ⟨w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := hw
    change Pe (ofAdd (1 : F) ^ n) ∈ primeLine Pe
    rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one]
    exact apply_ofAdd_mem_primeLine _ (Subfield.intCast_mem _ _)

theorem inv_mem_normOneShiftSet_of_mem [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneSubgroup F m ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y)
    {a : F} (ha : a ∈ normOneShiftSet F m) :
    a⁻¹ ∈ normOneShiftSet F m := by
  have hfin : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ q := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  have hm0 : m ≠ 0 := ne_zero_of_eq_div hp hq.pos hm
  have hP₀' : P₀ = (Subgroup.zpowers (ofAdd (1 : F))).map (P.subtype.comp Pe.toMonoidHom) := by
    rw [hP₀, primeLine_eq_map_zpowers_ofAdd_one (p := p)]
  have hQab' : IsMulCommutative ↥Q := isMulCommutative_iff_of_setLike.2 hQab
  obtain ⟨y₀, hy₀c, hy₀eq, -⟩ := exists_mem_commutator_map_conj_inv_eq_of_appendixC
    hp hq hqp hcardF hm hcop Pe Ue hPU hact (H := H) (P₁ := P₁) hH hs hP₀' hQab' hQp hQnorm hy
    hP₁ hP₁U ht
  have hy₀Q : y₀ ∈ Q := (Subgroup.le_normalizer_iff_commutator_le_left.1 hQnorm) hy₀c
  have hmaps := mapsTo_shiftedInv_normOneShiftImage hp hq hqp hcard hm hcop Pe Ue hPU hact
    (H := H) (P₀ := P₀) (P₁ := P₀.map (MulAut.conj y₀⁻¹ : G →* G)) (Q := Q) hH hP₀ hs hQab hQp
    hQnorm hy₀Q rfl (hy₀eq ▸ hP₁U) (t := y₀⁻¹ * s * y₀) rfl hy₀c
  rw [hs] at hmaps
  have hinv : ∀ b ∈ normOneShiftImage fun w => (Ue w : G),
      b⁻¹ ∈ normOneShiftImage fun w => (Ue w : G) := fun b hb =>
    inv_mem_normOneShiftImage_of_mapsTo_shiftedInv hp hq hqp hcardF hm hcop Pe Ue y₀ hmaps hb
  have ha0 : a ≠ 0 := ne_zero_of_mem_normOneShiftSet hm0 ha
  have huM : Units.mk0 a ha0 ∈ normOneSubgroup F m := by
    rw [mem_normOneSubgroup, Units.ext_iff]
    simpa using (mem_normOneShiftSet.1 ha).1
  set u : normOneSubgroup F m := ⟨Units.mk0 a ha0, huM⟩ with hu
  have huval : ((u : Fˣ) : F) = a := rfl
  have huE : u ∈ normOneShiftSubset F m := by
    rw [mem_normOneShiftSubset, huval]
    exact (mem_normOneShiftSet.1 ha).2
  obtain ⟨v, hv, hveq⟩ :=
    mem_normOneShiftImage.1 (hinv (Ue u : G) (mem_normOneShiftImage.2 ⟨u, huE, rfl⟩))
  have hvu : v = u⁻¹ := by
    refine Ue.injective (Subtype.ext ?_)
    rw [hveq, map_inv, Subgroup.coe_inv]
  rw [hvu] at hv
  have hval : (((u⁻¹ : normOneSubgroup F m) : Fˣ) : F) = a⁻¹ := by
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val, huval]
  refine mem_normOneShiftSet.2 ⟨?_, ?_⟩
  · have h := pow_eq_one_of_mem_normOneSubgroup (u⁻¹ : normOneSubgroup F m).2
    rwa [hval] at h
  · have h := mem_normOneShiftSubset.1 hv
    rwa [hval] at h

theorem normOneShiftSet_inv [Finite G]
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p) (hcard : Nat.card F = p ^ q)
    (hm : m = (p ^ q - 1) / (p - 1)) (hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneSubgroup F m ≃* U)
    (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneSubgroup F m),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹ : G →* G)) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y) :
    (normOneShiftSet F m)⁻¹ = normOneShiftSet F m := by
  have key : ∀ a ∈ normOneShiftSet F m, a⁻¹ ∈ normOneShiftSet F m := fun a ha =>
    inv_mem_normOneShiftSet_of_mem hp hq hqp hcard hm hcop Pe Ue hPU hact hH hP₀ hs hQab hQp
      hQnorm hy hP₁ hP₁U ht ha
  refine Set.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)
  · simpa using key a⁻¹ (Set.mem_inv.1 ha)
  · exact Set.mem_inv.2 (by simpa using key a ha)

end CFSG.FeitThompson
