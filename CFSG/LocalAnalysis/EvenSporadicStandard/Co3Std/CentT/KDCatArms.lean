module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCatReduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCatCo3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.NoFixedDoubleCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuter

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_Sp62)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (not_alt_of_card)
open CFSG.SeitzReduction.SymplecticPilot (CatSp2mEvenOuterExact)

@[expose] def KDSurvivor (S : Type) [Group S] : Prop :=
  LieModel S .POmegaPlus 4 2 1 ∨ LieModel S .PSU 6 2 1 ∨ IsSporadic S .Fi22

@[expose] def KDTrivialMultiplier (S : Type) [Group S] : Prop :=
  LieModel S .PSp 3 2 2 ∨ LieModel S .PSL 6 2 1 ∨ LieModel S .PSL 7 2 1 ∨
    LieModel S .PSU 7 2 1 ∨ LieModel S .POmegaMinus 4 2 1

theorem rows_sp62 (s : TauCeti.SporadicName) (hd : 1451520 ∣ AGLEmbedding.sporOrd s) :
    (SporadicInnerRow s 1451520 → s = .Co3) ∧ (SporadicOuterRow s 1451520 → s = .Fi22) := by
  cases s <;> first
    | exact absurd hd (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow]; decide)

theorem center_eq_bot_of_simple_nonab {X : Type} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : a ∈ center X := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)


theorem kd_arms {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (I : ArmInputs)
    (hEven : CatSp2mEvenOuterExact 3) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {Dbar : Subgroup S} (hle : Dbar ≤ fixedSubgroup σ)
    (hD : IsComponent (Dbar.subgroupOf (fixedSubgroup σ))) (hDm : LieModel ↥Dbar .PSp 3 2 1) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧ (KDSurvivor S ∨ KDTrivialMultiplier S) := by
  set D' : Subgroup ↥(fixedSubgroup σ) := Dbar.subgroupOf (fixedSubgroup σ) with hD'
  let e : ↥D' ≃* ↥Dbar := Subgroup.subgroupOfEquivOfLe hle
  have hDm' : LieModel ↥D' .PSp 3 2 1 := LieModel.of_mulEquiv e.symm hDm
  haveI hsimple : IsSimpleGroup ↥D' :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hDm'
  haveI : Group.IsPerfect ↥D' := hD.1.1
  have hnaD : ∃ a b : ↥D', a * b ≠ b * a :=
    exists_noncomm_of_perfect_simple Group.IsPerfect.commutator_eq_top
  have hZ : center ↥D' = ⊥ := center_eq_bot_of_simple_nonab hnaD
  have hcardDbar : Nat.card ↥Dbar = 1451520 := CFSG.EvenSmallLie.SympSix.card_of_lieModel hDm
  have hcardD : Nat.card ↥D' = 1451520 := (Nat.card_congr e.toEquiv).trans hcardDbar
  have hcardQ : Nat.card (↥D' ⧸ center ↥D') = 1451520 := by
    rw [← hcardD]
    exact Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, ⟨eA⟩⟩ | ⟨-, hodd⟩ | ⟨heven, hout, -⟩ | ⟨s', ⟨es⟩⟩
  ·
    exact absurd ⟨eA⟩ (not_alt_of_card (a := 9) (by omega) hcardQ
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]))
  ·
    rcases hodd with ⟨τ', n', p, f', hp, hp2, hadm', hY⟩ | hL8
    · obtain ⟨-, h1, h2⟩ := I.order _ τ' n' p f' hadm' hY
      rw [hcardQ] at h1 h2
      exact absurd ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩ not_oddLieOrder_Sp62
    · have h504 := card_eq_504_of_lieModel_psl28 I.order hL8
      omega
  ·
    obtain ⟨hov, -⟩ := hEven S ‹IsSimpleGroup S› hna heven σ hσ hout 1 D' hD hDm'
    refine ⟨hout, ?_⟩
    rcases hov with h | h | h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  ·
    obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hcardQ] at hdvd hin hout
    obtain ⟨hr1, hr2⟩ := rows_sp62 s' hdvd
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · have hs := hr1 (hin hinn)
      subst hs
      exact (kd_false_of_co3 hna es hσ hinn hle hcardDbar).elim
    · have hs := hr2 (hout hinn)
      subst hs
      exact ⟨hinn, Or.inl (Or.inr (Or.inr ⟨es⟩))⟩

end CFSG.EvenSporadicStandard.Co3Std.CentT
