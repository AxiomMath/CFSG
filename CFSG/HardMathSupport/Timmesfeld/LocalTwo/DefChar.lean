module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Families
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharClassical
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharOrth
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharExceptional
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterClassical
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreAssembly
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA1
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreC
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreReeD4
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterRank
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar
open CFSG.HardMathSupport.Timmesfeld.Coordinator (DefCharInnerCoreFree)

@[expose] def DefCharOuterRankTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → 5 < p → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem defCharOuterRankTwo_of_families (h : ∀ k, DefCharOuterRankTwoFam k) :
    DefCharOuterRankTwo := by
  intro S _ _ hS hnab idx hidx p hp hp5 hch D hD hcard
  have hne : idx.1.characteristic ≠ 2 := by rw [hch]; omega
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 hne
  exact h k S hS hnab idx hk hidx p hp hp5 hch D hD hcard

section

theorem defCharOuterRankTwo_proved : DefCharOuterRankTwo :=
  defCharOuterRankTwo_of_families fun k => by
    classical
    by_cases hk : k.IsClassical
    · cases k with
      | A => exact defCharOuterRankTwoFamA
      | twistedA => exact defCharOuterRankTwoFamTwistedA
      | B => exact defCharOuterRankTwoFamB
      | C => exact defCharOuterRankTwoFamC
      | D => exact defCharOuterRankTwoFamD
      | twistedD => exact defCharOuterRankTwoFamTwistedD
      | _ => exact absurd hk (by simp [DefCharFamily.IsClassical])
    · cases k with
      | E6 => exact defCharOuterRankTwoFamE6
      | E7 => exact defCharOuterRankTwoFamE7
      | E8 => exact defCharOuterRankTwoFamE8
      | F4 => exact defCharOuterRankTwoFamF4
      | G2 => exact defCharOuterRankTwoFamG2
      | twistedE6 => exact defCharOuterRankTwoFamTwistedE6
      | trialityD4 => exact defCharOuterRankTwoFamTrialityD4
      | reeG2 => exact defCharOuterRankTwoFamReeG2
      | _ => exact absurd trivial hk

end

theorem localTwoBalanceDefCharGtFive_of (hOut : DefCharOuterRankTwo)
    (hCore : DefCharInnerCoreFree) : LocalTwoBalanceDefCharGtFive := by
  intro S _ _ hS hnab idx hidx p hp hp5 hch D hD hcard H hH _
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨x, ⟨hxD, hxI⟩, hx1⟩ := hOut S hS hnab idx hidx p hp hp5 hch D hD hcard
  have hxp : orderOf x = p := orderOf_eq_prime (hD.2 x hxD) hx1
  have hle : localDeltaIn p H D ≤
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
    unfold localDeltaIn
    exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
  rw [hCore S hS hnab idx hidx p hp hp2 hch x hxI hxp H hH] at hle
  exact le_bot_iff.1 hle

section

theorem localTwoBalanceDefCharGtFive_of_dFour (h4 : DefCharInnerCoreFreeFamDFour) :
    LocalTwoBalanceDefCharGtFive :=
  localTwoBalanceDefCharGtFive_of defCharOuterRankTwo_proved (defCharInnerCoreFree_of_dFour h4)

theorem localTwoBalanceDefCharGtFive_of_dFourImage (hres : DFourPrimeCentralizerInImage) :
    LocalTwoBalanceDefCharGtFive :=
  localTwoBalanceDefCharGtFive_of_dFour (defCharInnerCoreFreeFamDFour_of_image hres)

end

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
