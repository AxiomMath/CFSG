module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Dih
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem card_D (hs : Setting46e t L 3 4 S w z V i₀ j₀) : Nat.card ↥(S ⊓ L) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := hs.standing.isSylowOf_inf hs.sylow
  rw [hSyl.card_eq]
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hs.standing.config.lieModel
  have hbar : Nat.card (Bar L) = 3280 * 81 := by
    rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num)
      hF]
    norm_num
  have hL : Nat.card ↥L = Nat.card (Bar L) * Nat.card ↥(pPrimeCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [hL, factorization_two_mul_odd (by rw [hbar]; norm_num) hodd, hbar,
    factorization_two_mul_odd (by norm_num) (by decide),
    show (3280 : ℕ) = 2 ^ 4 * 205 by norm_num,
    factorization_two_mul_odd (by norm_num) (by decide), Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]
  norm_num

theorem nonempty_D_equiv (hs : Setting46e t L 3 4 S w z V i₀ j₀) :
    Nonempty (↥(S ⊓ L) ≃* DihedralGroup 8) := by
  obtain ⟨m, -, ⟨e⟩⟩ := hs.setup.dihedral
  have h1 := hs.card_D
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h1
  have hm : 2 ^ m = 2 ^ 3 := by omega
  have hm3 : m = 3 := Nat.pow_right_injective le_rfl hm
  subst hm3
  exact ⟨e⟩

theorem card_Dstar (hs : Setting46e t L 3 4 S w z V i₀ j₀) (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (i j : ℕ) :
    Nat.card ↥(S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 8 := by
  have h1 := relIndex_mul_card
    (inf_le_left : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ S ⊓ L)
  rw [hs.setup.relIndex_Dstar hFC hKC i j, hs.card_D] at h1
  omega

theorem exists_x (hs : Setting46e t L 3 4 S w z V i₀ j₀) (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (i j : ℕ) :
    ∃ x ∈ S ⊓ L, x ∉ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∧
      x * x = 1 := by
  have hσ := hs.setup
  set Ds := S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hDsdef
  obtain ⟨e⟩ := hs.nonempty_D_equiv
  obtain ⟨m, hm, ⟨eDs⟩⟩ := hσ.dihedral_Dstar hFC hKC i j
  have hDsD : Ds ≤ S ⊓ L := inf_le_left
  have hcard : 2 * Nat.card Ds = Nat.card ↥(S ⊓ L) := by
    rw [hs.card_Dstar hFC hKC i j, hs.card_D]
  have hnab : ∃ a ∈ Ds, ∃ b ∈ Ds, a * b ≠ b * a := by
    refine ⟨eDs.symm (r 1), (eDs.symm (r 1)).2, eDs.symm (sr 0), (eDs.symm (sr 0)).2, ?_⟩
    intro h1
    have h2 : eDs.symm (r 1) * eDs.symm (sr 0) = eDs.symm (sr 0) * eDs.symm (r 1) :=
      Subtype.ext h1
    have h3 := congrArg eDs h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, r_mul_sr,
      sr_mul_r, sr.injEq, zero_sub, zero_add] at h3
    have h4 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hZ : ∀ c ∈ S ⊓ L, (∀ d ∈ S ⊓ L, c * d = d * c) → c ∈ Ds := by
    intro c hc' hcc
    have h1 : c ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) :=
      mem_inf.mpr ⟨hc', Subgroup.mem_centralizer_iff.mpr fun d hd => (hcc d hd).symm⟩
    rw [hσ.center_D] at h1
    rcases eq_one_or_eq_of_mem_zpowers_two hσ.z_order h1 with rfl | rfl
    · exact one_mem _
    · exact hσ.z_mem_Dstar hFC hKC i j
  obtain ⟨x, hxD, hxDs, hx2, -⟩ := L415.exists_involution_not_mem (m := 3) e hDsD hcard hnab hZ
  exact ⟨x, hxD, hxDs, hx2⟩

end Setting46e

end CFSG.ComponentClassification.HarrisLit
