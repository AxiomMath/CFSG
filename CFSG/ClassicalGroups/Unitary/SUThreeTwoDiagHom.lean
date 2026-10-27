module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoQData
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalInvolution.Phan.AutSU2
import all CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

set_option autoImplicit false

namespace CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape CFSG.AGLEmbedding.SUQ

section Abstract

variable {H : Type} [Group H] {S D Z F G : H}

theorem closure_heisSubgroup_union_eq_top [Finite H] (hH : Nat.card H = 216)
    (h : Heis3Rel S D Z) (hZ : Z ≠ 1) (hF4 : F ^ 4 = 1) (hF2 : F ^ 2 ≠ 1) (hG2 : G ^ 2 = F ^ 2)
    (hGF : G * F * G⁻¹ = F⁻¹) :
    Subgroup.closure ((heisSubgroup h : Set H) ∪ {F, G}) = ⊤ := by
  classical
  set C := Subgroup.closure ((heisSubgroup h : Set H) ∪ {F, G}) with hC
  set q := quatHom hF4 hG2 hGF with hq
  have hqinj : Function.Injective q := quatHom_injective hF4 hF2 hG2 hGF
  have hEC : heisSubgroup h ≤ C := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hFC : F ∈ C := Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))
  have hGC : G ∈ C := Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  have hqC : q.range ≤ C := by
    rintro _ ⟨(i | i), rfl⟩
    · rw [hq, quatHom_a]
      exact zpow_mem hFC _
    · rw [hq, quatHom_xa]
      exact mul_mem hGC (zpow_mem hFC _)
  have h27 : 27 ∣ Nat.card C := card_heisSubgroup hH h hZ ▸ Subgroup.card_dvd_of_le hEC
  have h8 : 8 ∣ Nat.card C := by
    have hq8 : Nat.card q.range = 8 := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hqinj, Subgroup.card_top,
        Nat.card_eq_fintype_card, QuaternionGroup.card]
    exact hq8 ▸ Subgroup.card_dvd_of_le hqC
  have h216 : 216 ∣ Nat.card C := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 8) h27 h8
    simpa using this
  have hle : Nat.card C ∣ 216 := hH ▸ Subgroup.card_subgroup_dvd_card C
  exact Subgroup.eq_top_of_card_eq _ (by rw [hH]; exact Nat.dvd_antisymm hle h216)

end Abstract

section Model

open CFSG.GH74.QTGen4.Leaves.F112 CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem unit_pow_three (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have h : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← h]
  exact pow_card_eq_one'

omit [Finite K] [CharP K 2] in
theorem pow_three_eq_one (hK : Nat.card K = 4) {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := congrArg Units.val (unit_pow_three hK (Units.mk0 c hc))
  simpa using this

theorem unitaryInvolution_two_one_apply (c : K) : unitaryInvolution K 2 1 c = c ^ 2 := by
  rw [unitaryInvolution_apply, pow_one]

theorem mem_normOne_two_one (hK : Nat.card K = 4) (u : Kˣ) :
    u ∈ normOne (unitaryInvolution K 2 1) := by
  rw [mem_normOne, unitaryInvolution_two_one_apply, ← pow_succ]
  exact pow_three_eq_one hK u.ne_zero

theorem conjTr_diagGL_mul_self (hK : Nat.card K = 4) {m : ℕ} (t : Fin m → Kˣ) :
    conjTr (unitaryInvolution K 2 1) ((diagGL t : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      ((diagGL t : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
  diagGL_conjTr_mul_self t fun i => (mem_normOne _).1 (mem_normOne_two_one hK (t i))

@[expose] noncomputable def dconjSu (hK : Nat.card K = 4) {m : ℕ} (t : Fin m → Kˣ) :
    Su K 2 1 m →* Su K 2 1 m :=
  (diagConj 2 1 (by rw [hK]; norm_num) fun i => ⟨t i, mem_normOne_two_one hK (t i)⟩).toMonoidHom

theorem coe_dconjSu (hK : Nat.card K = 4) {m : ℕ} (t : Fin m → Kˣ) (X : Su K 2 1 m) :
    ((dconjSu hK t X : Su K 2 1 m) : GL (Fin m) K) = diagGL t * (X : GL (Fin m) K) * (diagGL t)⁻¹ :=
  rfl

@[expose] noncomputable def omegaUnit (o : OmegaData K) : Kˣ :=
  ⟨o.ω, o.ω ^ 2, by rw [← pow_succ', o.cube], by rw [← pow_succ, o.cube]⟩

@[expose] noncomputable def omegaDiag (o : OmegaData K) : Fin 3 → Kˣ := ![omegaUnit o, 1, 1]

omit [Finite K] [CharP K 2] in
theorem coe_diagGL_omegaDiag (o : OmegaData K) :
    ((diagGL (omegaDiag o) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![o.ω, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_diagGL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite K] [CharP K 2] in
theorem coe_diagGL_omegaDiag_inv (o : OmegaData K) :
    (((diagGL (omegaDiag o))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![o.ω ^ 2, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite K] in
theorem mat_dconjOmega_F (o : OmegaData K) :
    !![o.ω, 0, 0; 0, 1, 0; 0, 0, 1] * mF o.ω * !![o.ω ^ 2, 0, 0; 0, 1, 0; 0, 0, 1] =
      mF o.ω * mG o.ω := by
  have hω := o.hω
  have h2 := o.h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mF, mG, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

omit [Finite K] in
theorem mat_dconjOmega_G (o : OmegaData K) :
    !![o.ω, 0, 0; 0, 1, 0; 0, 0, 1] * mG o.ω * !![o.ω ^ 2, 0, 0; 0, 1, 0; 0, 0, 1] =
      mF o.ω := by
  have hω := o.hω
  have h2 := o.h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mF, mG, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

end Model

end CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag
