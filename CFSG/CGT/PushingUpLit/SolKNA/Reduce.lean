module

public import CFSG.CGT.PushingUpLit.SolKAb.Residue
public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Quot
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (rightConjugate_le_rightConjugate
  exists_rightConjugate_eq_of_isSylowOf)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime oUpperTwoPrime_le mem_oUpperTwoPrime
  normalizer_le_normalizer_oUpperTwoPrime)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (pCoreOf)
open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg IsCommSubgroup isPGroup_sylowImg)
open CFSG.ComponentClassification.AschbacherKnownGroup CFSG.Assembly.LowTwoRank

section Perfect

variable {G : Type} [Group G] {K : Subgroup G}

omit [Group G] in
theorem le_oUpperTwoPrime_of_isPGroup {G : Type} [Group G] {K P : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup 2 P) : P ≤ oUpperTwoPrime K := fun x hx => by
  obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
  exact mem_oUpperTwoPrime (hPK hx) (n := m) (by simpa using congrArg Subtype.val hm)

theorem oUpperTwoPrime_oUpperTwoPrime (K : Subgroup G) :
    oUpperTwoPrime (oUpperTwoPrime K) = oUpperTwoPrime K := by
  refine le_antisymm (oUpperTwoPrime_le _) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, k, hk⟩
  exact mem_oUpperTwoPrime (mem_oUpperTwoPrime hx hk) hk

end Perfect

section Reduction

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem sylowImg_le_oUpperTwoPrime (R : Sylow 2 K) : sylowImg R ≤ oUpperTwoPrime K :=
  le_oUpperTwoPrime_of_isPGroup (Subgroup.map_subtype_le _) (isPGroup_sylowImg R)

theorem isSylowOf_oUpperTwoPrime (R : Sylow 2 K) :
    IsSylowOf 2 (sylowImg R) (oUpperTwoPrime K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.IsSylowOf.of_le (⟨R, rfl⟩ : IsSylowOf 2 (sylowImg R) K)
    (sylowImg_le_oUpperTwoPrime R) (oUpperTwoPrime_le K)

theorem even_card_oUpperTwoPrime (S : STSetting G K) : Even (Nat.card (oUpperTwoPrime K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  have hR2 : 2 ∣ Nat.card (sylowImg R) := by
    rcases (isPGroup_sylowImg R).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) (S.sylowImg_ne_bot R)
    · exact h
  exact even_iff_two_dvd.mpr (hR2.trans (Subgroup.card_dvd_of_le (sylowImg_le_oUpperTwoPrime R)))

theorem normalizer_oUpperTwoPrime_eq (S : STSetting G K) :
    Subgroup.normalizer (oUpperTwoPrime K : Set G) = Subgroup.normalizer (K : Set G) :=
  le_antisymm (CFSG.ComponentClassification.Asc76.Sec5.normalizer_le_normalizer_of_tightlyEmbedded
    S.tight (oUpperTwoPrime_le K) (even_card_oUpperTwoPrime S))
    (normalizer_le_normalizer_oUpperTwoPrime K)

theorem stSetting_oUpperTwoPrime (S : STSetting G K) : STSetting G (oUpperTwoPrime K) := by
  have hN := normalizer_oUpperTwoPrime_eq S
  refine ⟨S.simple, S.nonab, ⟨even_card_oUpperTwoPrime S, fun g hg => ?_⟩, ?_, ?_⟩
  · rw [hN] at hg
    have hle : oUpperTwoPrime K ⊓ rightConjugate (oUpperTwoPrime K) g ≤ K ⊓ rightConjugate K g :=
      inf_le_inf (oUpperTwoPrime_le K) (rightConjugate_le_rightConjugate (oUpperTwoPrime_le K) g)
    exact (S.tight.2 g hg).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  · rw [hN]
    exact S.max
  · rw [hN]
    exact S.fstar

end Reduction

section Outcomes

@[expose] def Outcome5 (G : Type) [Group G] (K P : Subgroup G) : Prop :=
  (∃ H : Subgroup G, H ≤ pCoreOf 2 K ∧ H ≤ P ∧
      Nonempty (↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      H.relIndex P ≤ 2) ∧
    StatedClassicalModel G .PSL 3 2 2

@[expose] def Outcome6 (G : Type) [Group G] (K P : Subgroup G) : Prop :=
  P = pCoreOf 2 K ∧
    ((∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s))

@[expose] def Outcome56 (G : Type) [Group G] (K P : Subgroup G) : Prop :=
  Outcome5 G K P ∨ Outcome6 G K P

variable {G : Type} [Group G] {K P : Subgroup G}

theorem mtOutcome_of_outcome56 (R : Sylow 2 K) (h : Outcome56 G K (sylowImg R)) :
    MTOutcome G K R := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

variable [Finite G]

end Outcomes

end CFSG.CGT.PushingUpLit.SolKNA
