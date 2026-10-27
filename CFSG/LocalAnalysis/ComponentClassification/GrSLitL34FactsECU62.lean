module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_psl2_of_statedSp_three {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) (Φ : X ≃* StatedSp 3 k) {P : Subgroup X}
    (hP : IsPComponent 2 P) {p m : ℕ} (hp2 : p ≠ 2) :
    ¬ Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 2 p m := by
  intro hL
  have hk' : Nat.card k = 2 ^ 1 := by rw [hk, pow_one]
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp 3 k) hk' (by norm_num) ⟨MulEquiv.refl _⟩
  have : IsSimpleGroup (StatedProj (StatedSp 3 k)) :=
    ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k 3 (by norm_num)
      (Or.inr (Or.inr ⟨hk, le_rfl⟩))
  have : IsSimpleGroup (StatedSp 3 k) := eProj.symm.isSimpleGroup
  have hXs : IsSimpleGroup X := Φ.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub := ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 P).mp hP).1
  have htop : P = ⊤ := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hXs hsub with h | h
    · exfalso
      have hnt := GrSLit.nontrivial_of_isPComponent hP
      rw [h] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · exact h
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans Φ)
  obtain ⟨h1, -⟩ := SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
    (X := P ⧸ Open.fusionZStar P) hk' (r := 3) (by norm_num) ⟨eZ⟩
  have hcl : StatedClassicalModel (P ⧸ Open.fusionZStar P) .PSL 2 p m := by
    rcases hL with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact h
    all_goals exfalso; revert h; decide
  have := h1 p m hp2 hcl
  omega

theorem noOddPSL2_U62 {J : Type} [Group J] (hm : Blueprint.LieModel J .PSU 6 2 1) :
    NoOddPSL2 J := by
  intro α hα hαo P hP p m hp2 hL
  have hadm : StatedLieAdmissible .PSU 6 2 1 := admissible_of_lieModel hm
  have : Finite J := by
    obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
    have : Finite K := h.finite
    exact Finite.of_equiv _ ψ.symm.toEquiv
  rcases even_unitary_outer_fixed_cases hadm hm α hα hαo with hch | ⟨k, _, _, hk, r, -, hr, ⟨Φ⟩⟩
  · exact not_isPComponent_of_isCharacteristicP hch P hP
  · obtain rfl : r = 3 := by omega
    exact not_psl2_of_statedSp_three (by rw [hk, pow_one]) Φ hP hp2 hL

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
