module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallZ
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits CFSG.Timmesfeld QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {p f : ℕ} [Fact p.Prime]

theorem minusLift_of_chain_frame (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X]
    (θ : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRf : ∀ a ≤ s, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (s + 5) (minusCoeffs_irr p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus (minusDatum (s + 5) (minusCoeffs_irr p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum (s + 5) (minusCoeffs_irr p f)))
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        ((R a).map (spinAction (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) i →
      IsFundamental (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        ((R b).map (spinAction (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j,
      IsFundamental (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        ((R s).map (spinAction (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) i →
      IsFundamental (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (Rtw.map (spinAction (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (t : Bool),
      (∀ a (ha : a ≤ s), R a = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame s (s + 1) (by omega) (by omega) (by omega) true
          true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
        (minusCoeffs p f).2).toHypFrame (s + 2) (s + 3) (by omega) (by omega) (by omega)
          true t).map (MulAut.conj x).toMonoidHom) ∧ MinusLift θ σ := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (s + 5) p f :=
    ⟨Fact.out, hf1, by show 4 ≤ s + 5; omega⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (s + 5 - 1) ⊕ Fin (s + 5 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f _ (by omega)]
    omega
  have hQ : (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f))
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := s) hs
    (minusFrame (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hdim cq hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact ⟨x, t, hxR, hxtw, hxM, (toralNormal_minus_of_frame_chain hp2 hq hs θ hker σ hσ2 hσr x t
    hxR hxtw hxM hfix hfixtw hfixM hnorm0).2⟩

end CFSG.ClassicalInvolution.RouteD.TwinSmall
