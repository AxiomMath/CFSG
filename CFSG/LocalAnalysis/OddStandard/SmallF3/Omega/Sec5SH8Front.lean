module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.GroupTheory.PCore.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (HasDihedralSylowTwo)

theorem sec5sh8_hasDihedralSylowTwo {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : Nonempty (↥P ≃* DihedralGroup 4)) : HasDihedralSylowTwo X := by
  intro S
  have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
  exact ⟨2, by norm_num,
    ⟨(Sylow.equiv S P).trans (hP.some.trans (MulEquiv.cast hpow.symm))⟩⟩

theorem sec5sh8_eq_top_or_not_normalComplement {X : Type} [Group X] [Finite X]
    (hO : CFSG.oddCore X = ⊥) (P : Sylow 2 X) :
    (P : Subgroup X) = ⊤ ∨ ¬ CFSG.HasNormalPComplement 2 X := by
  by_cases hcomp : CFSG.HasNormalPComplement 2 X
  · left
    have hcore : CFSG.pPrimeCore 2 X = ⊥ := by
      have e : {K : Subgroup X | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} =
          {N : Subgroup X | N.Normal ∧ Odd (Nat.card N)} := by
        ext K
        simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
      rw [CFSG.pPrimeCore, e]
      exact hO
    have hQ : IsPGroup 2 (X ⧸ CFSG.pPrimeCore 2 X) :=
      CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) X hcomp
    have hX : IsPGroup 2 X :=
      hQ.of_injective (QuotientGroup.mk' (CFSG.pPrimeCore 2 X)) (by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore])
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hcard : Nat.card (P : Subgroup X) = 2 ^ (Nat.card X).factorization 2 :=
      P.card_eq_multiplicity
    rw [hn, Nat.Prime.factorization_pow Nat.prime_two] at hcard
    simp at hcard
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, hn]
  · exact Or.inr hcomp

end CFSG.OddStandard.SmallF3.Omega
