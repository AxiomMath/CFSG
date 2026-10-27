module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Small
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2P
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem five_le_pow_of_ne_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : p ^ f ≠ 3) : 5 ≤ p ^ f := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hge : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have h2p := hp.two_le
  obtain ⟨k, hk⟩ := hodd
  omega

theorem exists_mulEquiv_adjoint_of_lieModel {Y : Type} [Group Y] {p f : ℕ}
    (hM : LieModel Y .G2 0 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Y ≃* adjointGroup Tag.G2 K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := untwisted_of_lieModel_G2 hM
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)⟩⟩

theorem cf67CoreFull_G2_core
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) :
    CF67CoreFull (adjointGroup Tag.G2 K) := by
  classical
  intro hs hn r V Z h2 h3
  obtain ⟨hr, hrodd, -⟩ := id h2
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  by_cases hq3 : Nat.card K = 3
  · exact g2_three_false_of_n2 K hq3 hr h2
  · by_cases hrp : r = p
    · subst hrp
      exact g2_false_of_rp hp2 hf K hK h2 h3
    · by_cases hinn : ∀ v ∈ V, IsInnerAut v
      · exact g2_false_of_inner hp hp2 hf K hK hr hrodd hrp hn h2 h3 hinn
      · push Not at hinn
        exact g2_false_of_field hp hp2 hf K hK hr hrodd h2 h3 hinn

theorem cf67CoreFull_G2
    (Y : Type) [Group Y] [Finite Y] (hY : FG2 Y) : CF67CoreFull Y := by
  obtain ⟨p, f, hp, hf, hp2, hM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjoint_of_lieModel hM
  exact CF67CoreFull.of_mulEquiv e (cf67CoreFull_G2_core hp hp2 hf K hK)

theorem cf67CoreDeriv_G2_cover (J : Type) [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hY : FG2 (J ⧸ Subgroup.center J)) (r : ℕ) (hr : r.Prime)
    (hd : r ∣ Nat.card (Subgroup.center J)) : CF67CoreDeriv (J ⧸ Subgroup.center J) r := by
  obtain ⟨p, f, hp, hf, hp2, hM⟩ := hY
  by_cases hq : p ^ f = 3
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjoint_of_lieModel hM
    refine CF67CoreDeriv.of_mulEquiv e ?_
    intro _ _ V Z h2 _
    exact g2_three_false_of_n2 K (hK.trans hq) hr h2
  · exfalso
    have hcen := g2_center_eq_bot hJ hM (five_le_pow_of_ne_three hp hp2 hf hq)
    rw [hcen, Subgroup.card_bot] at hd
    exact absurd (Nat.le_of_dvd one_pos hd) (by have := hr.two_le; omega)

theorem cf67G2_of_core :
    CF67G2 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_G2 Y hY)
    (fun J _ _ hJ hY r hr _ hd => cf67CoreDeriv_G2_cover J hJ hY r hr hd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
