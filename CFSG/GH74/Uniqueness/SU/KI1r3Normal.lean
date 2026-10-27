module

public import CFSG.GH74.Uniqueness.SU.KI1r3Basic
public import CFSG.GH74.GLS.C3.Layer2.GenLemmas
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.Uniqueness.SU.KInputsR3
public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem isElementaryAbelian_of_isElemAbelian {E : Subgroup H} (hE : Open.IsElemAbelian 2 E) :
    IsElementaryAbelian 2 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE

theorem Cfg.exists_E8_above {T : Sylow 2 H} {x : H} (h : Cfg H T x) {A : Subgroup H}
    (hAT : A ≤ (T : Subgroup H)) (hTA : (T : Subgroup H) ≤ normalizer (A : Set H))
    (hel : Open.IsElemAbelian 2 A) (hcard : Nat.card A = 4) :
    ∃ E : Subgroup H, A ≤ E ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  have hT2 : IsPGroup 2 (T : Subgroup H) := T.isPGroup'
  have hTrank : 3 ≤ Open.pRank 2 (T : Subgroup H) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T]
    exact h.rank
  have hNEp : SU1.IsNormalEp2 2 (T : Subgroup H) A := ⟨hAT, hTA, hel, by simpa using hcard⟩
  obtain ⟨-, -, hrk⟩ := SU1.ig10_20_ii Nat.prime_two hT2 hNEp
  obtain ⟨E, hEQ, hEel, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := centralizer (A : Set H) ⊓ (T : Subgroup H)) (k := 3) (by rw [hrk]; exact hTrank)
  have hEcomm : ∀ e ∈ E, ∀ u ∈ A, e * u = u * e := by
    intro e he u hu
    have := (Subgroup.mem_inf.mp (hEQ he)).1
    exact (Subgroup.mem_centralizer_iff.mp this u hu).symm
  have hEU := SU1.IsElemAbelian.sup hEel hel hEcomm
  refine ⟨E ⊔ A, le_sup_right, hEU, ?_⟩
  have h1 : Nat.card E ≤ Nat.card ↥(E ⊔ A) := Subgroup.card_le_of_le le_sup_left
  omega

theorem Cfg.normal_elemAb {T : Sylow 2 H} {x : H} (h : Cfg H T x) {A : Subgroup H} [hAn : A.Normal]
    (hA : Open.IsElemAbelian 2 A) (hne : A ≠ ⊥) :
    Nat.card A = 4 ∧ ∃ a ∈ A, x * a * x⁻¹ ≠ a := by
  have hxx := h.mul_self_x
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hA
  have hA2 : IsPGroup 2 A := by
    have := isElementaryAbelian_of_isElemAbelian hA
    exact IsElementaryAbelian.isPGroup 2 A
  have hAT : A ≤ (T : Subgroup H) := hA2.le_sylow_of_normal T
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [Subgroup.eq_bot_iff_card, hk]
    simp
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hc := CFSG.ABGLocalTools.le_center_of_normal_of_card_eq_two hAn (by rw [hk]; simp)
    apply hne
    rw [h.cen] at hc
    exact le_bot_iff.mp hc
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push Not at hk3
    have h8 : 8 ≤ Nat.card A := by
      rw [hk]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    have hxN : ∀ v ∈ A, x * v * x⁻¹ ∈ A := fun v hv => hAn.conj_mem v hv x
    have hx2 : ∀ v ∈ A, x ^ 2 * v = v * x ^ 2 := by
      intro v _; rw [pow_two, hxx]; simp
    have : IsElementaryAbelian 2 A := isElementaryAbelian_of_isElemAbelian hA
    have hsq := CFSG.GH74.GLS.C3.Layer2.card_le_sq_card_fixed A hxN hx2
    have hCel : Open.IsElemAbelian 2 (A ⊓ centralizer ({x} : Set H)) :=
      SU1.IsElemAbelian.mono inf_le_left hA
    have hC4 : 4 ≤ Nat.card ↥(A ⊓ centralizer ({x} : Set H)) := by
      obtain ⟨j, hj⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hCel
      by_contra hlt
      push Not at hlt
      have hj1 : j ≤ 1 := by
        by_contra hj2
        push Not at hj2
        have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
        omega
      have h2 : Nat.card ↥(A ⊓ centralizer ({x} : Set H)) ≤ 2 := by
        rw [hj]
        calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
          _ = 2 := by norm_num
      have : Nat.card ↥(A ⊓ centralizer ({x} : Set H)) ^ 2 ≤ 4 := by nlinarith
      omega
    by_cases hxC : x ∈ A ⊓ centralizer ({x} : Set H)
    · have hxA : x ∈ A := (Subgroup.mem_inf.mp hxC).1
      exact h.no_E8 hA h8 1 (by simpa using hxA)
    · have hcomm : ∀ u ∈ A ⊓ centralizer ({x} : Set H), u * x = x * u := fun u hu =>
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2)
      obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hCel hC4 hxx hcomm hxC
      exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))
  have hk2' : k = 2 := by omega
  have hcard : Nat.card A = 4 := by rw [hk, hk2']; norm_num
  refine ⟨hcard, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ u ∈ A, u * x = x * u := by
    intro u hu
    have := hcon u hu
    calc u * x = x * u * x⁻¹ * x := by rw [this]
      _ = x * u := by group
  by_cases hxA : x ∈ A
  · obtain ⟨E, hAE, hEel, hE8⟩ := h.exists_E8_above hAT
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hA hcard
    exact h.no_E8 hEel hE8 1 (by simpa using hAE hxA)
  · obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hA (by omega) hxx hcomm hxA
    exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))

end CFSG.GH74.Uniqueness.SU.K.R3
