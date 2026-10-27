module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Coord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Act
public import CFSG.Assembly.OddCoreSpan
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoStrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open
open scoped commutatorElement

@[expose] def colFold (w : ℕ → ℕ) (v : ℕ) : ℕ :=
  (List.range 6).foldl (fun r i => if v.testBit i then r ^^^ w i else r) 0

theorem colFold_two_pow : ∀ v < 64, colFold (2 ^ ·) v = v := by
  decide

theorem bitVec_foldl (w : ℕ → ℕ) (v : ℕ) : ∀ (l : List ℕ) (r : ℕ),
    bitVec (l.foldl (fun r i => if v.testBit i then r ^^^ w i else r) r) =
      l.foldl (fun r i => if v.testBit i then r + bitVec (w i) else r) (bitVec r)
  | [], _ => rfl
  | i :: l, r => by
    simp only [List.foldl_cons]
    rw [bitVec_foldl w v l]
    congr 1
    split_ifs
    · exact bitVec_xor r (w i)
    · rfl

theorem bitVec_colFold (w : ℕ → ℕ) (v : ℕ) :
    bitVec (colFold w v) =
      (List.range 6).foldl (fun r i => if v.testBit i then r + bitVec (w i) else r) 0 := by
  rw [colFold, bitVec_foldl, bitVec_zero]

theorem map_foldl {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (p : ℕ → Bool)
    (g : ℕ → V) (g' : ℕ → W) : ∀ l : List ℕ, (∀ i ∈ l, f (g i) = g' i) → ∀ r : V,
      f (l.foldl (fun r i => if p i then r + g i else r) r) =
        l.foldl (fun r i => if p i then r + g' i else r) (f r)
  | [], _, _ => rfl
  | i :: l, h, r => by
    simp only [List.foldl_cons]
    rw [map_foldl f p g g' l (fun j hj => h j (List.mem_cons_of_mem i hj))]
    congr 1
    split_ifs
    · rw [map_add, h i List.mem_cons_self]
    · rfl

theorem map_bitVec {f : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2)} {w : ℕ → ℕ}
    (hf : ∀ i < 6, f (bitVec (2 ^ i)) = bitVec (w i)) {v : ℕ} (hv : v < 64) :
    f (bitVec v) = bitVec (colFold w v) := by
  conv_lhs => rw [← colFold_two_pow v hv, bitVec_colFold]
  rw [map_foldl f _ _ (fun i => bitVec (w i)) _ (fun i hi => hf i (List.mem_range.mp hi)), map_zero,
    bitVec_colFold]

namespace Coord

variable {H : Type} [Group H] {t : H} {q : ℕ → H} (C : Coord t q)
include C

local notation "ψ" => psi (t := t) (q := q)

theorem psi_add' : ∀ a ∈ C.Q, ∀ b ∈ C.Q, ψ (a * b) = ψ a + ψ b :=
  fun _ ha _ hb => C.psi_mul ha hb

theorem psi_ker' : ∀ a ∈ C.Q, ψ a = 0 ↔ a ∈ zpowers t :=
  fun _ ha => C.psi_eq_zero_iff ha

theorem psi_q {v : ℕ} (hv : v < 64) : ψ (q v) = bitVec v := by
  rw [show q v = q v * t ^ 0 by rw [pow_zero, mul_one], C.psi_eq hv (by norm_num)]

variable {K : Subgroup H}
  (hK : K ≤ normalizer (C.Q : Set H) ⊓ centralizer ({t} : Set H))
include hK

theorem conj_mem_Q (c : K) {a : H} (ha : a ∈ C.Q) : (c : H) * a * (c : H)⁻¹ ∈ C.Q :=
  (mem_normalizer_iff.mp (hK c.2).1 a).mp ha

noncomputable def rhoEquiv (c : K) : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := Sec2.act C.psi_surj (c : H)
  invFun := Sec2.act C.psi_surj (c : H)⁻¹
  map_add' u w := by
    obtain ⟨a, ha, rfl⟩ := C.psi_surj u
    obtain ⟨b, hb, rfl⟩ := C.psi_surj w
    have hN := (hK c.2).1
    have hz := (hK c.2).2
    rw [← C.psi_mul ha hb,
      Sec2.act_psi C.psi_add' C.psi_surj C.psi_ker' hN hz (C.Q.mul_mem ha hb),
      Sec2.act_psi C.psi_add' C.psi_surj C.psi_ker' hN hz ha,
      Sec2.act_psi C.psi_add' C.psi_surj C.psi_ker' hN hz hb,
      show (c : H) * (a * b) * (c : H)⁻¹ = ((c : H) * a * (c : H)⁻¹) * ((c : H) * b * (c : H)⁻¹)
        by group]
    exact C.psi_mul (C.conj_mem_Q hK c ha) (C.conj_mem_Q hK c hb)
  map_smul' r u := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one r with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, ← Sec2.psi_one C.psi_add',
        Sec2.act_psi C.psi_add' C.psi_surj C.psi_ker' (hK c.2).1 (hK c.2).2 C.Q.one_mem, mul_one,
        mul_inv_cancel]
    · rw [one_smul, RingHom.id_apply, one_smul]
  left_inv u := by
    rw [← Sec2.act_mul C.psi_add' C.psi_surj C.psi_ker' (inv_mem (hK c.2).1) (inv_mem (hK c.2).2)
      (hK c.2).1 (hK c.2).2, inv_mul_cancel, Sec2.act_one C.psi_add' C.psi_surj C.psi_ker']
  right_inv u := by
    rw [← Sec2.act_mul C.psi_add' C.psi_surj C.psi_ker' (hK c.2).1 (hK c.2).2
      (inv_mem (hK c.2).1) (inv_mem (hK c.2).2), mul_inv_cancel,
      Sec2.act_one C.psi_add' C.psi_surj C.psi_ker']

noncomputable def rho : ↥K →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) where
  toFun := C.rhoEquiv hK
  map_one' := LinearEquiv.ext fun u => Sec2.act_one C.psi_add' C.psi_surj C.psi_ker' u
  map_mul' c d := LinearEquiv.ext fun u =>
    Sec2.act_mul C.psi_add' C.psi_surj C.psi_ker' (hK c.2).1 (hK c.2).2 (hK d.2).1 (hK d.2).2 u

theorem rho_psi (c : K) {a : H} (ha : a ∈ C.Q) :
    C.rho hK c (ψ a) = ψ ((c : H) * a * (c : H)⁻¹) :=
  Sec2.act_psi C.psi_add' C.psi_surj C.psi_ker' (hK c.2).1 (hK c.2).2 ha

theorem rho_mem_orthogonalGroup (c : K) :
    C.rho hK c ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  obtain ⟨a, ha, rfl⟩ := C.psi_surj u
  rw [C.rho_psi hK c ha, Sec2Omega.qMinusForm_apply, Sec2Omega.qMinusForm_apply]
  have hca := C.conj_mem_Q hK c ha
  have h3 : ((c : H) * a * (c : H)⁻¹) * ((c : H) * a * (c : H)⁻¹) = 1 ↔ a * a = 1 := by
    rw [show ((c : H) * a * (c : H)⁻¹) * ((c : H) * a * (c : H)⁻¹) =
      (c : H) * (a * a) * (c : H)⁻¹ by group]
    constructor
    · intro h
      rw [show a * a = (c : H)⁻¹ * ((c : H) * (a * a) * (c : H)⁻¹) * (c : H) by group, h]
      group
    · intro h
      rw [h]
      group
  have key := (C.mul_self_eq_one_iff hca).symm.trans (h3.trans (C.mul_self_eq_one_iff ha))
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus (ψ a)) with h | h <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (qMinus (ψ ((c : H) * a * (c : H)⁻¹))) with h' | h'
  · rw [h, h']
  · exact absurd (key.mpr h) (by rw [h']; exact one_ne_zero)
  · exact absurd (key.mp h') (by rw [h]; exact one_ne_zero)
  · rw [h, h']

theorem le_ker_rho : C.Q.subgroupOf K ≤ (C.rho hK).ker := by
  intro c hc
  rw [MonoidHom.mem_ker]
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨a, ha, rfl⟩ := C.psi_surj u
  rw [C.rho_psi hK c ha, LinearEquiv.coe_one, id,
    Sec2.psi_eq_iff C.psi_add' C.psi_ker' (C.conj_mem_Q hK c ha) ha]
  have := C.commutator_mem_zpowers (mem_subgroupOf.mp hc) ha
  rwa [commutatorElement_def] at this

theorem rho_bitVec (c : K) {w b : ℕ → ℕ} (hw : ∀ i < 6, w i < 64) (hb : ∀ i < 6, b i < 2)
    (hc : ∀ i < 6, (c : H) * q (2 ^ i) * (c : H)⁻¹ = q (w i) * t ^ b i) {v : ℕ} (hv : v < 64) :
    C.rho hK c (bitVec v) = bitVec (colFold w v) := by
  refine map_bitVec (f := (C.rho hK c).toLinearMap.toAddMonoidHom) (fun i hi => ?_) hv
  have hi64 : 2 ^ i < 64 := by
    calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
      _ = 64 := by norm_num
  change C.rho hK c (bitVec (2 ^ i)) = bitVec (w i)
  rw [← C.psi_q hi64, C.rho_psi hK c (C.q_mem hi64), hc i hi, C.psi_eq (hw i hi) (hb i hi)]

theorem commutator_eq_top (hQK : C.Q ≤ K) (hrange : (C.rho hK).range = timmesfeldOmega qMinus)
    (hker : (C.rho hK).ker = C.Q.subgroupOf K)
    (hperf : ⁅timmesfeldOmega qMinus, timmesfeldOmega qMinus⁆ = timmesfeldOmega qMinus)
    (hne : timmesfeldOmega qMinus ≠ ⊥) : commutator ↥K = ⊤ := by
  set D : Subgroup ↥K := commutator ↥K with hD
  set Q' : Subgroup ↥K := C.Q.subgroupOf K with hQ'
  have htD : (⟨t, hQK C.t_mem⟩ : ↥K) ∈ D := by
    have e := C.commutator_eq (v := 1) (w := 2) (by norm_num) (by norm_num) 0 0
    rw [show (gammaBit 1 2 + gammaBit 2 1) % 2 = 1 by decide, pow_one] at e
    simp only [pow_zero, mul_one] at e
    have : (⟨t, hQK C.t_mem⟩ : ↥K) =
        ⁅(⟨q 1, hQK (C.q_mem (by norm_num))⟩ : ↥K), ⟨q 2, hQK (C.q_mem (by norm_num))⟩⁆ :=
      Subtype.ext (by rw [commutatorElement_def]; exact e.symm)
    rw [this, hD, _root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  let W : Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
    { carrier := {v | ∃ a : ↥K, a ∈ Q' ∧ a ∈ D ∧ ψ (a : H) = v}
      add_mem' := by
        rintro _ _ ⟨a, haQ, haD, rfl⟩ ⟨b, hbQ, hbD, rfl⟩
        exact ⟨a * b, Q'.mul_mem haQ hbQ, D.mul_mem haD hbD, C.psi_mul haQ hbQ⟩
      zero_mem' := ⟨1, Q'.one_mem, D.one_mem, Sec2.psi_one C.psi_add'⟩
      smul_mem' := by
        rintro r _ ⟨a, haQ, haD, rfl⟩
        rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one r with rfl | rfl
        · exact ⟨1, Q'.one_mem, D.one_mem, by rw [zero_smul]; exact Sec2.psi_one C.psi_add'⟩
        · exact ⟨a, haQ, haD, (one_smul _ _).symm⟩ }
  have hDn : D.Normal := inferInstance
  have hW : ∀ γ ∈ timmesfeldOmega qMinus, ∀ w ∈ W, γ w ∈ W := by
    rintro γ hγ _ ⟨a, haQ, haD, rfl⟩
    rw [← hrange] at hγ
    obtain ⟨c, rfl⟩ := hγ
    exact ⟨c * a * c⁻¹, mem_subgroupOf.mpr (C.conj_mem_Q hK c (mem_subgroupOf.mp haQ)),
      hDn.conj_mem a haD c, (C.rho_psi hK c (mem_subgroupOf.mp haQ)).symm⟩
  have hWne : W ≠ ⊥ := by
    intro hW0
    obtain ⟨γ, hγ, hγ1⟩ : ∃ γ ∈ timmesfeldOmega qMinus, γ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_bot_iff.mpr fun γ hγ => (mem_bot).mpr (hcon γ hγ))
    rw [← hrange] at hγ
    obtain ⟨c, rfl⟩ := hγ
    obtain ⟨u, hu⟩ : ∃ u, C.rho hK c u ≠ u := by
      by_contra hcon
      push Not at hcon
      exact hγ1 (LinearEquiv.ext hcon)
    obtain ⟨a, ha, rfl⟩ := C.psi_surj u
    set a' : ↥K := ⟨a, hQK ha⟩ with ha'
    have hca := C.conj_mem_Q hK c ha
    have hcomm : ((⁅c, a'⁆ : ↥K) : H) = (c : H) * a * (c : H)⁻¹ * a⁻¹ := by
      rw [commutatorElement_def]
      rfl
    have hQc : ((⁅c, a'⁆ : ↥K) : H) ∈ C.Q := by
      rw [hcomm]
      exact C.Q.mul_mem hca (C.Q.inv_mem ha)
    have hDc : ⁅c, a'⁆ ∈ D := by
      rw [hD, _root_.commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have hmem : ψ ((⁅c, a'⁆ : ↥K) : H) ∈ W := ⟨⁅c, a'⁆, hQc, hDc, rfl⟩
    rw [hW0, Submodule.mem_bot, hcomm, Sec2.psi_mul_inv C.psi_add' hca ha, sub_eq_zero] at hmem
    exact hu (by rw [C.rho_psi hK c ha]; exact hmem)
  have hWtop : W = ⊤ := (Sec2Omega.eq_bot_or_eq_top_of_timmesfeldOmega hW).resolve_left hWne
  have hQD : Q' ≤ D := by
    intro a haQ
    have haW : ψ (a : H) ∈ W := hWtop ▸ Submodule.mem_top
    obtain ⟨b, hbQ, hbD, hba⟩ := haW
    have h1 := (Sec2.psi_eq_iff C.psi_add' C.psi_ker' (mem_subgroupOf.mp haQ)
      (mem_subgroupOf.mp hbQ)).mp hba.symm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have e : a = (⟨t, hQK C.t_mem⟩ : ↥K) ^ k * b := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      change (a : H) = t ^ k * (b : H)
      rw [hk, inv_mul_cancel_right]
    rw [e]
    exact D.mul_mem (zpow_mem htD k) hbD
  have hmap : D.map (C.rho hK) = (⊤ : Subgroup ↥K).map (C.rho hK) := by
    rw [hD, _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange,
      hperf]
  have hsup := Subgroup.map_eq_map_iff.mp hmap
  rw [top_sup_eq, hker, sup_eq_left.mpr hQD] at hsup
  exact hsup

end Coord

end CFSG.ComponentClassification.AS81.SuzB0
