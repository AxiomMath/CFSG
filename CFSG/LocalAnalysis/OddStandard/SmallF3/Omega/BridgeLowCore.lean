module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadPlus)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem odd_card_zmod3 : Odd (Nat.card (ZMod 3)) := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

private theorem card_zmod3_eq_three_pow_one : Nat.card (ZMod 3) = 3 ^ 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

theorem isQuasisimple_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  obtain ⟨-, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_five_derived
      (K := ZMod 3) (W := V) odd_card_zmod3 Q hQ' hdim
  rw [omegaGroup_eq_commutator hQ (by omega)]
  exact hq

theorem lieModel_quotient_center_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) :
    LieModel (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) .PSp 2 3 1 := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hq := isQuasisimple_omegaGroup_five hQ hdim
  have hM : IsComponent (omegaGroup hQ) := ⟨hq, (omegaGroup_normal hQ).isSubnormal⟩
  exact (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_five
    (p := 3) (e := 1) (by norm_num) (by norm_num) le_rfl card_zmod3_eq_three_pow_one
    Q hQ' hdim hM).2

theorem isQuasisimple_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hQm : (quadPlus 3 (ZMod 3)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_quadPlus 3 (ZMod 3)
  have h2V : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hdim' : Module.finrank (ZMod 3) V =
      Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 → ZMod 3) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [hdim]
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ hQm hdim'
    (hs.trans (quadSign_quadPlus 3).symm)
  obtain ⟨eω⟩ := nonempty_omegaGroup_mulEquiv hQ hQm e h2V
  have hq0 : CFSG.IsQuasisimple
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 (ZMod 3)))) :=
    CFSG.ComponentClassification.CatalogueBOrthogonal.derived_quasisimple
      (quadPlus 3 (ZMod 3)) (by decide)
      (CFSG.ComponentClassification.CatLeafProof.KleinSix.quadPlus_nondegenerate (K := ZMod 3))
      (K := ZMod 3)
      (CFSG.ComponentClassification.CatLeafProof.KleinSix.finrank_singularT (K := ZMod 3)).ge
      (fun x hx =>
        CFSG.ComponentClassification.CatLeafProof.KleinSix.singularT_singular
          (K := ZMod 3) x hx)
  have hq_model : CFSG.IsQuasisimple (omegaGroup hQm) := by
    rw [omegaGroup_eq_commutator hQm (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp)]
    exact hq0
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eω.symm hq_model

theorem lieModel_quotient_center_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    LieModel (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) .PSL 4 3 1 := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by omega)).mpr hs
  obtain ⟨T, hTdim2, hTQ⟩ := hplus
  have hT : ∃ T : Submodule (ZMod 3) V, Module.finrank (ZMod 3) T = 3 ∧ ∀ x ∈ T, Q x = 0 :=
    ⟨T, by omega, hTQ⟩
  have hq := isQuasisimple_omegaGroup_six_plus hQ hdim hs
  have hM : IsComponent (omegaGroup hQ) := ⟨hq, (omegaGroup_normal hQ).isSubnormal⟩
  exact (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_split_six
    (p := 3) (e := 1) (by norm_num) (by norm_num) le_rfl card_zmod3_eq_three_pow_one
    Q hQ' hdim hT hM).2

theorem isQuasisimple_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hno : ¬ ∃ T : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
    rintro ⟨T, hTdim, hTQ⟩
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q := ⟨T, by omega, hTQ⟩
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by omega)).mp hplus
    have hc := congrArg (fun u : ℤˣ => (u : ℤ))
      (show (-1 : ℤˣ) = 1 from by rw [← hs, h1])
    norm_num at hc
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived
      (K := ZMod 3) (W := V) odd_card_zmod3 Q hQ' hdim hno
  rw [omegaGroup_eq_commutator hQ (by omega)]
  exact hq

theorem lieModel_quotient_center_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    LieModel (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) .PSU 4 3 1 := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hno : ¬ ∃ T : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
    rintro ⟨T, hTdim, hTQ⟩
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q := ⟨T, by omega, hTQ⟩
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by omega)).mp hplus
    have hc := congrArg (fun u : ℤˣ => (u : ℤ))
      (show (-1 : ℤˣ) = 1 from by rw [← hs, h1])
    norm_num at hc
  have hq := isQuasisimple_omegaGroup_six_minus hQ hdim hs
  have hM : IsComponent (omegaGroup hQ) := ⟨hq, (omegaGroup_normal hQ).isSubnormal⟩
  exact (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_six
    (p := 3) (e := 1) (by norm_num) (by norm_num) le_rfl card_zmod3_eq_three_pow_one
    Q hQ' hdim hno hM).2

end CFSG.OddStandard.SmallF3.Omega
