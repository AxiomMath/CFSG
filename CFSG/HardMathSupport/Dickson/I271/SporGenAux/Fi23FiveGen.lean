module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenKit
public import Certificates.Certificate17254

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.Fi23 CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census


theorem fi23J_card_five : (Nat.card J).factorization 5 = 2 :=
  factorization_sq_of_eq Nat.prime_five
    (by rw [card_J]; norm_num : Nat.card J = 5 ^ 2 * 163578818931720192) (by norm_num)

noncomputable def fi23EquivCarrier : NativeSporadic.Carrier .Fi23 ≃* J := fi23EquivJ


theorem fi23CG_spec :
    ∃ e f s₁ s₂ : J, Subgroup.closure ({s₁, s₂} : Set J) = ⊤ ∧ e ^ 5 = 1 ∧ f ^ 5 = 1 ∧
      e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧ s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  obtain ⟨e, f, s₁, s₂, hs, heJ, hfJ, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate17254
  have hs₁ : s₁ ∈ J := hs ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hs₂ : s₂ ∈ J := hs ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨⟨e, heJ⟩, ⟨f, hfJ⟩, ⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ?_, Subtype.ext (by simpa using he),
    Subtype.ext (by simpa using hf), Subtype.ext (by simpa using hef),
    fun h => he1 (by simpa using congrArg Subtype.val h),
    fun k hk h => hfe k hk (by simpa using congrArg Subtype.val h),
    Subtype.ext (by simpa using h₁), Subtype.ext (by simpa using h₂)⟩
  have hc := Subgroup.closure_closure_coe_preimage
    (k := ({s₁, s₂} : Set (GL (Fin 253) (ZMod 3))))
  rw [hs] at hc
  refine Eq.trans ?_ hc
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem centGen_fi23J_five : CentGen 5 J := by
  obtain ⟨e, f, s₁, s₂, hs, he, hf, hef, he1, hfe, h₁, h₂⟩ := fi23CG_spec
  exact centGen_of_data Nat.prime_five fi23J_card_five hs he hf hef he1 hfe h₁ h₂
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem sporPair_Fi23_five
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) : SporPair .Fi23 5 := by
  have h1 := sporPair_five_of_model (name := .Fi23) (M := J) hSpM hOut hBr
  have h2 := h1 fi23EquivCarrier
  have h3 := h2 fi23J_card_five
  exact h3 centGen_fi23J_five

end CFSG.HardMathSupport.Dickson.I271
