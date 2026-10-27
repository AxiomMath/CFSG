module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenKit
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import Certificates.Certificate17253

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem suzCG_spec :
    ∃ e f s₁ s₂ : suzM, Subgroup.closure ({s₁, s₂} : Set suzM) = ⊤ ∧ e ^ 5 = 1 ∧ f ^ 5 = 1 ∧
      e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧ s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  obtain ⟨e, f, s₁, s₂, hs, heM, hfM, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate17253
  have hs₁ : s₁ ∈ suzM := hs ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hs₂ : s₂ ∈ suzM := hs ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨⟨e, heM⟩, ⟨f, hfM⟩, ⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ?_, Subtype.ext (by simpa using he),
    Subtype.ext (by simpa using hf), Subtype.ext (by simpa using hef),
    fun h => he1 (by simpa using congrArg Subtype.val h),
    fun k hk h => hfe k hk (by simpa using congrArg Subtype.val h),
    Subtype.ext (by simpa using h₁), Subtype.ext (by simpa using h₂)⟩
  have hc := Subgroup.closure_closure_coe_preimage (k := ({s₁, s₂} : Set (Equiv.Perm (Fin 1782))))
  rw [hs] at hc
  refine Eq.trans ?_ hc
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem suzM_card_five :
    (Nat.card suzM).factorization 5 = 2 :=
  factorization_sq_of_eq Nat.prime_five
    (by rw [suzM_card]; norm_num : Nat.card suzM = 5 ^ 2 * 17933819904) (by norm_num)

theorem centGen_suzM_five :
    CentGen 5 suzM := by
  obtain ⟨e, f, s₁, s₂, hs, he, hf, hef, he1, hfe, h₁, h₂⟩ := suzCG_spec
  exact centGen_of_data Nat.prime_five suzM_card_five hs he hf hef he1 hfe h₁ h₂
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem sporPair_Suz_five
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) : SporPair .Suz 5 :=
  sporPair_five_of_model hSpM hOut hBr suzEquivM suzM_card_five centGen_suzM_five

end CFSG.HardMathSupport.Dickson.I271
