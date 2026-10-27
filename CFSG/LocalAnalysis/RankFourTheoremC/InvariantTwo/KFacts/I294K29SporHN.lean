module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut
public import Certificates.Certificate425002
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporWit
public import CFSG.RankThree.PartOne.KS.HNFiveCheck
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.KS.HNFive CFSG.Monster.B.Pinned

section Census

variable {G : Type} [Group G] [Finite G] {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G}
  {BU : Fin k → GL (Fin 4) (ZMod 5)} {cr : Fin k → Fin 4 → ℕ}

theorem rankThreeWitness_hn_five_of {m : ℕ}
    (hcard : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m) (hR : Rel q z x r Mm XU cx BU cr) :
    ∀ s : G, orderOf s = 5 → RankThreeWitness 5 s :=
  Certificates.certificate425002 hcard hm hR

end Census

section CertificateInstances


theorem sporadicClassWitnessNative_HN_five :
    ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .HN) →
      ∀ x : S, orderOf x = 5 → RankThreeWitness 5 x := by
  intro S _ _ ⟨eS⟩ s hs
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let e : CFSG.Blueprint.NativeSporadic.HN ≃* CFSG.Sporadic.GLQ.HNTwoRank.J :=
    CFSG.Sporadic.GLQ.HNTwoRank.hnEquivJ
  let ι : CFSG.Blueprint.NativeSporadic.HN →* CFSG.Sporadic.GLQ.HNTwoRank.GLHN :=
    CFSG.Sporadic.GLQ.HNTwoRank.J.subtype.comp (e : CFSG.Blueprint.NativeSporadic.HN →*
      CFSG.Sporadic.GLQ.HNTwoRank.J)
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ r, ι (e.symm ⟨Rg r, Rg_mem r⟩) = Rg r := fun r => by
    show ((e (e.symm ⟨Rg r, Rg_mem r⟩) : CFSG.Sporadic.GLQ.HNTwoRank.J) :
      CFSG.Sporadic.GLQ.HNTwoRank.GLHN) = Rg r
    rw [MulEquiv.apply_symm_apply]
  have hrel : Rel (fun j => e.symm ⟨Rg (iQ j), Rg_mem _⟩) (e.symm ⟨Rg iZ, Rg_mem _⟩)
      (e.symm ⟨Rg iX, Rg_mem _⟩) (fun j => e.symm ⟨Rg (iR j), Rg_mem _⟩) Mm XU cx BU cr := by
    apply Rel.of_injective ι hι
    simp only [hιe]
    exact hnFive_rel
  have hfin : Finite CFSG.Blueprint.NativeSporadic.HN :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.HN = 5 ^ 6 * 17473978368 := by
    rw [CFSG.Sporadic.HN.card_HN]; norm_num
  have hw := rankThreeWitness_hn_five_of hcard (by norm_num) hrel (eS s)
    ((MulEquiv.orderOf_eq eS s).trans hs)
  exact @RankThreeWitness.of_mulEquiv S CFSG.Blueprint.NativeSporadic.HN _ inferInstance _ 5 _
    eS s hw

end CertificateInstances

section CertificateInstancesNative


theorem sporadicClassWitnessAt_HN_five : SporadicClassWitnessAt .HN 5 :=
  sporadicClassWitnessAt_of_native sporadicClassWitnessNative_HN_five

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
