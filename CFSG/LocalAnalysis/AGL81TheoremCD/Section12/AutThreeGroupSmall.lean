module

import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Open.LocalVocabulary
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Monster.B.TwoA.Base.ElemAut
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

private theorem exists_frattiniQuotient_coordinates {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 3 W) (hsmall : Nat.card (W ⧸ frattini W) ≤ 9) :
    ∃ d : ℕ, d ≤ 2 ∧ Nat.card (W ⧸ frattini W) = 3 ^ d ∧
      Nonempty ((W ⧸ frattini W) ≃* Multiplicative (Fin d → ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcomm, hpow, -, hdata⟩ := CFSG.GroupTheory.frattini_elementary_quotient hW
  obtain ⟨d, hcard, -⟩ := hdata
  refine ⟨d, ?_, hcard, ?_⟩
  · have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [hcard, h9] at hsmall
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hsmall
  · exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
      (fun a b => hcomm.is_comm.comm a b) hpow hcard

private theorem card_GL_fin_le_two (d : ℕ) (hd : d ≤ 2) :
    Nat.card (GL (Fin d) (ZMod 3)) = 1 ∨
      Nat.card (GL (Fin d) (ZMod 3)) = 2 ∨
        Nat.card (GL (Fin d) (ZMod 3)) = 48 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  interval_cases d
  · exact Or.inl (by rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp)
  · exact Or.inr (Or.inl (by
      rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp [Fin.prod_univ_one]))
  · exact Or.inr (Or.inr (by
      rw [CFSG.SectionRank.Ccomm.card_GL_zmod]; simp [Fin.prod_univ_two]))

private theorem prime_dvd_card_GL_fin_le_two {r d : ℕ} (hr : r.Prime) (hd : d ≤ 2)
    (hdvd : r ∣ Nat.card (GL (Fin d) (ZMod 3))) : r = 2 ∨ r = 3 := by
  rcases card_GL_fin_le_two d hd with h | h | h
  · rw [h] at hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hr.ne_one
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (h ▸ hdvd))
  · have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h, h48] at hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)

theorem prime_dvd_card_mulAut_eq_two_or_three {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 3 W) (hsmall : Nat.card (W ⧸ frattini W) ≤ 9)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card (MulAut W)) : r = 2 ∨ r = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdle, -, ⟨e⟩⟩ := exists_frattiniQuotient_coordinates hW hsmall
  let φ : MulAut W →* MulAut (W ⧸ frattini W) :=
    CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction (frattini W)
  have hker : IsPGroup 3 φ.ker :=
    CFSG.RankThreeEvenClassification.Helpers.frattini_automorphism_kernel_isPGroup
      3 Nat.prime_three hW
  have hkerCard : Nat.card φ.ker * Nat.card φ.range = Nat.card (MulAut W) :=
    Subgroup.card_ker_mul_card_range φ
  have hrangeDvd : Nat.card φ.range ∣ Nat.card (MulAut (W ⧸ frattini W)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have hGLcard : Nat.card (MulAut (W ⧸ frattini W)) =
      Nat.card (GL (Fin d) (ZMod 3)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  rw [← hkerCard] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with hkerDvd | hrangeDvd'
  · right
    obtain ⟨m, hm⟩ := hker.exists_card_eq
    rw [hm] at hkerDvd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow hkerDvd)
  · exact prime_dvd_card_GL_fin_le_two hr hdle (by
      rw [← hGLcard]
      exact hrangeDvd'.trans hrangeDvd)

theorem not_dvd_card_mulAut_of_five_le {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 3 W) (hsmall : Nat.card (W ⧸ frattini W) ≤ 9)
    {d : ℕ} (hd : d.Prime) (h5 : 5 ≤ d) : ¬ d ∣ Nat.card (MulAut W) := by
  intro hdvd
  rcases prime_dvd_card_mulAut_eq_two_or_three hW hsmall hd hdvd with h | h <;> omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
