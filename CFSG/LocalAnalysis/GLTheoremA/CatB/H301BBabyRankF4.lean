module

public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate2323

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS Subgroup

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

private theorem factorization_three_mul {a c : ℕ} (hc : ¬ 3 ∣ c) :
    (3 ^ a * c).factorization 3 = a := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero 3)
  rw [Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hc, add_zero]


theorem card_le_of_babyInv_three {X : NativeSporadic.B} (hX : BabyInv 3 X)
    (E : Subgroup NativeSporadic.B) (hEX : E ≤ centralizer ({X} : Set NativeSporadic.B))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : IsConj X (CFSG.Monster.Existence.babyRep 5) :=
    CFSG.Monster.Existence.babyTableIII.2 3 X _ hX
      CFSG.Monster.Existence.babyInv_three_babyRep_five
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, b5, -⟩ :=
    CFSG.Monster.B.CTIB.native_four_involution_classes
  have hrank : Matrix.rank (X.val.val - 1) = 2158 := by
    rw [CFSG.Monster.Existence.rank_sub_one_of_isConj hconj]
    exact b5
  obtain ⟨L, -, -, -, ⟨φ⟩, hLc, -⟩ :=
    CFSG.Monster.B.CTIB.native_rank_2158_distance_three_product_final.2.2 X hX.1 hrank
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 6 ∣ Nat.card L by rw [hLc]; norm_num)
  have hQc : Nat.card (Q.map L.subtype) = 3 ^ (Nat.card
      (⊤ : Subgroup (centralizer ({X} : Set NativeSporadic.B)))).factorization 3 := by
    rw [card_map_of_injective L.subtype_injective, hQ, card_top, hX.2,
      show babyCentOrder 3 = 3 ^ 6 * 36336094412800 by decide +kernel,
      factorization_three_mul (by norm_num)]
  have hE₁ := hE.subgroupOf (centralizer ({X} : Set NativeSporadic.B))
  obtain ⟨g, -, hg⟩ := H1017.exists_conj_into_of_card
    (H := (⊤ : Subgroup (centralizer ({X} : Set NativeSporadic.B)))) le_top hQc le_top
    hE₁.isPGroup
  have hle := hg.trans (map_subtype_le Q)
  have h := CFSG.StandardType.TableBF4Two.card_le_adjointF4 (Nat.card_zmod 2)
    (((hE₁.map (MulAut.conj g).toMonoidHom).subgroupOf L).map φ.toMonoidHom)
  rwa [card_map_of_injective φ.injective, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    card_map_of_injective (MulAut.conj g).injective,
    Nat.card_congr (subgroupOfEquivOfLe hEX).toEquiv] at h

end CFSG.LocalAnalysis.GLTheoremA.H301B
