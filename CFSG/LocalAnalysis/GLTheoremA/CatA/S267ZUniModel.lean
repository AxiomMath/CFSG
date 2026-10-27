module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

abbrev PU (h : UnitaryFieldData ℓ f K) : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem not_three_two_of_ne_two (hℓp : ℓ.Prime) (hℓ : ℓ ≠ 2) : ¬(3 = 3 ∧ ℓ ^ f = 2) := by
  rintro ⟨-, h2⟩
  rcases f with _ | f
  · norm_num at h2
  · exact hℓ ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).1
      (h2 ▸ dvd_pow_self ℓ (Nat.succ_ne_zero f)))

noncomputable def PUEquivStated (h : UnitaryFieldData ℓ f K) :
    PU h ≃* StatedProj (StatedSU 3 (ℓ ^ f) K) :=
  (nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 3))).some.trans
    (unitaryPSUEquiv h (by norm_num))

theorem exists_mulEquiv_PU {Q : TauCeti.PrimePower} {S : Type} [Group S]
    (hS : catalogIs S (onLie (· = .twistedA 2 Q))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData Q.p Q.exponent K),
      Nat.card K = (Q.p ^ Q.exponent) ^ 2 ∧ Nonempty (S ≃* PU h) := by
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hS
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .twistedA 2 Q at hi
  subst hi
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 Q hv e₀
  have h : UnitaryFieldData Q.p Q.exponent K :=
    ⟨Q.prime_p, Q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  exact ⟨K, inferInstance, inferInstance, h, hK, ⟨e₁.trans (PUEquivStated h).symm⟩⟩

theorem center_PU_eq_bot [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) :
    Subgroup.center (PU h) = ⊥ := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (3, ℓ ^ f) ≠ (3, 2) := fun he =>
    not_three_two_of_ne_two (f := f) h.prime hℓ ⟨rfl, (Prod.ext_iff.1 he).2⟩
  have hZ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_center_bot_pu hK (le_refl 3) hnq
  rw [eq_bot_iff]
  intro z hz
  have hz' : PUEquivStated h z ∈ Subgroup.center (StatedProj (StatedSU 3 (ℓ ^ f) K)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y, rfl⟩ := (PUEquivStated h).surjective y
    rw [← map_mul, ← map_mul, hz y]
  rw [hZ, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact (PUEquivStated h).injective (hz'.trans (map_one _).symm)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
