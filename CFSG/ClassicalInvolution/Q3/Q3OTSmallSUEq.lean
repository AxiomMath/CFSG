module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.ClassicalInvolution.RouteD.TypeABridge
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.ExceptionalSL3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups


theorem psu_model_equiv_P (hadm : StatedLieAdmissible .PSU 4 3 1) :
    ∃ (P : GL (Fin 4) (GaloisField 3 (2 * 1)))
      (hP : conjTr (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1)
        (P : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) *
          (P : Matrix (Fin 4) (Fin 4) (GaloisField 3 (2 * 1))) = antidiag 4),
      ∀ R : Subgroup (SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4),
        R ∈ fundamentalSubgroups .PSU
            (Unitary.rootDatum (card_galoisField_two_mul 3 1 le_rfl) 4) ↔
          R.map (Unitary.conjEquiv P hP).toMonoidHom ∈
            longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) (by norm_num : 2 ≤ 4) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have : NeZero (2 * 1) := ⟨by norm_num⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 hf
  have hn2 : 2 ≤ 4 := by norm_num
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix hF 4
  obtain ⟨k, γ, hγlong, hγ, hγ'⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_longest_root_psu
    Fact.out hadm
  obtain ⟨i₀, hR₀⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hF hp2
    hn2 hγ hγ' P hP
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSU 4 3 1 Fact.out
    trivial hadm (by decide) (by decide)
  have hM : Generic.modelUniv .PSU 4 3 1 Fact.out =
      ⟨↥(Unitary.SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4),
        Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4⟩ :=
    (rfl : Generic.modelUniv .PSU 4 3 1 Fact.out =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .PSU 4 3 1 Fact.out).trans
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv_PSU hf)
  have hs : ∀ R1 ∈ fundamentalSubgroups .PSU
        (Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4),
      ∀ R2 ∈ fundamentalSubgroups .PSU (Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4),
        ∃ g : Unitary.SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4,
          R2 = conjSub g R1 := by
    suffices key : ∀ M : LieUniversal, M =
        ⟨↥(Unitary.SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4),
          Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4⟩ →
        FundamentalSingleClass .PSU M.D →
        ∀ R1 ∈ fundamentalSubgroups .PSU
            (Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4),
          ∀ R2 ∈ fundamentalSubgroups .PSU
              (Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4),
            ∃ g : Unitary.SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4,
              R2 = conjSub g R1 from key _ hM hsingle
    intro M hM' hs'
    subst hM'
    exact hs'
  refine ⟨P, hP, fun R => ?_⟩
  obtain ⟨R0, hR0f, hR0L⟩ : ∃ R0 : Subgroup (Unitary.SU (unitaryInvolution
      (GaloisField 3 (2 * 1)) 3 1) 4), R0 ∈ fundamentalSubgroups .PSU
        (Unitary.rootDatum (card_galoisField_two_mul 3 1 hf) 4) ∧
      R0.map (Unitary.conjEquiv P hP).toMonoidHom ∈
        longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hn2 :=
    ⟨_, ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩, ⟨i₀, hR₀⟩⟩
  constructor
  · intro hR
    obtain ⟨g, rfl⟩ := hs R0 hR0f R hR
    show (R0.map (MulAut.conj g).toMonoidHom).map (Unitary.conjEquiv P hP).toMonoidHom ∈ _
    rw [map_map_conj]
    exact longRootSetU_conjInvariant hn2 _ _ hR0L
  · intro hL
    obtain ⟨i, hi⟩ := hL
    obtain ⟨i', hi'⟩ := hR0L
    obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_conj_of_isLongRootSU2 hi hi'
    have hRR : R = conjSub ((Unitary.conjEquiv P hP).symm c) R0 := by
      apply Subgroup.map_injective (f := (Unitary.conjEquiv P hP).toMonoidHom)
        (Unitary.conjEquiv P hP).injective
      rw [hc]
      show _ = (R0.map (MulAut.conj ((Unitary.conjEquiv P hP).symm c)).toMonoidHom).map _
      rw [map_map_conj]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [hRR]
    obtain ⟨g, γ', hγ', rfl⟩ := hR0f
    exact ⟨(Unitary.conjEquiv P hP).symm c * g, γ', hγ', (conjSub_mul _ _ _).symm⟩

end CFSG.ClassicalInvolution.Q3.Q3OT
