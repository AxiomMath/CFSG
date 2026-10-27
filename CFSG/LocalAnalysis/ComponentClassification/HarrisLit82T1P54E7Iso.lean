module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Model
public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessCentralCoverRows
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.Foundations
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.CentralExt
  CFSG.ClassicalInvolution.ModelFacts

variable {p f : ℕ} [Fact p.Prime]

theorem gcd_two_pow_sub_one (hp2 : p ≠ 2) : Nat.gcd 2 (p ^ f - 1) = 2 := by
  obtain ⟨k, hk⟩ := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow (n := f)
  rw [hk, Nat.add_sub_cancel]
  exact Nat.gcd_eq_left (dvd_mul_right 2 k)

theorem nonempty_mulEquiv_E7sc {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y)
    (hZ : IsPGroup 2 (center Y)) (hp2 : p ≠ 2) {n : ℕ}
    (hL : LieModel (Y ⧸ center Y) .E7 n p f) (hq : 5 ≤ p ^ f) {t : Y} (ht2 : orderOf t = 2)
    (ht : t ∈ center Y) : Nonempty (E7sc p f ≃* Y) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYm : UntwistedChevalleyModel (Y ⧸ center Y) .E7 (p ^ f) := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by simp [classicalTags])
    · exact hm
    · exact absurd ht (by simp [reeTitsTags])
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hYm
  obtain ⟨-, ⟨eM⟩⟩ := MinusculeClosed.e7_hopfMultiplier (K := K) (by rw [hK]; exact hq)
  have hM : Nat.card (Open.griessHopfMultiplier (AdjointQuotient .E7 K)) = 2 := by
    rw [Nat.card_congr eM.toEquiv, hK, gcd_two_pow_sub_one hp2]
    simp
  obtain ⟨-, h2, h3⟩ := GriessCentralCovers.central_covers_of_card_two hM
  have hcY : Nat.card (center Y) = 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 (center Y)) := inferInstance
    have hS : (S : Subgroup (center Y)) = ⊤ := (S.is_maximal' (hZ.to_subgroup ⊤) le_top).symm
    have hle : Nat.card (center Y) ≤ 2 := by
      have := h2 Y hY ⟨e₁⟩ S
      rwa [hS, Subgroup.card_top] at this
    have hdvd : 2 ∣ Nat.card (center Y) := by
      rw [← ht2, ← Subgroup.orderOf_mk t ht]
      exact orderOf_dvd_natCard _
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hQ7 : IsQuasisimple (E7sc p f) := isQuasisimple_e7 (GaloisField p f)
  have : Finite (E7sc p f) := by
    have : Finite (Module.End (GaloisField p f) (Fin e7Data.d →₀ GaloisField p f)) :=
      Module.finite_of_finite (GaloisField p f)
    infer_instance
  have hX : UntwistedChevalleyModel (E7sc p f ⧸ center (E7sc p f)) .E7 (p ^ f) :=
    untwistedChevalleyModel_of_surjective hQ7 (GaloisField.card p f hf)
      (e7Isogeny (GaloisField p f)) (e7Isogeny_surjective _)
      (exists_ne_one_of_surjective_adjointGroup (by decide) (e7Isogeny_surjective _))
      (MulEquiv.refl _)
  obtain ⟨e₂⟩ := ClassicalInvolution.Upgrade.untwistedChevalleyModel_unique hX
    ⟨K, inferInstance, inferInstance, hK, ⟨e₁⟩⟩
  exact h3 (E7sc p f) Y hQ7 hY (card_center_E7sc hp2 hf) hcY ⟨e₂.trans e₁⟩ ⟨e₁⟩

end CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row
