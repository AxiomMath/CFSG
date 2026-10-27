module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3O
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUh
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsSingle
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3D
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3E
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLinear
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorAut
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 DiagU StabU UnitaryOut UnitaryConj HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem invStar_neg_one :
    invStar h (-1 : SpecialLinearGroup (Fin 2) K) = -1 := by
  apply Subtype.ext
  change starInvMat h (-1) = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starInvMat]

theorem pairSL_neg_one : pairSL h (-1 : SpecialLinearGroup (Fin 2) K) = negOne4 := by
  apply Subtype.ext
  rw [coe_pairSL, invStar_neg_one]
  change bd (-1) (-1) = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem u4_inner_aut (hp2 : p ≠ 2) {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {A : GL (Fin 4) K} (hA : IsCU h A φ) {l : K} (hl0 : l ≠ 0) {Q₀ : GL (Fin 4) K}
    (hQ : uStar h (Q₀ : Matrix (Fin 4) (Fin 4) K) * (Q₀ : Matrix (Fin 4) (Fin 4) K) = stdG)
    (hAQ : (A : Matrix (Fin 4) (Fin 4) K) * (Q₀ : Matrix (Fin 4) (Fin 4) K) =
      (Q₀ : Matrix (Fin 4) (Fin 4) K) * X1 l)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hJφ : ∀ x ∈ J', φ x = x)
    (hJp : ⁅J', J'⁆ = J') (hJc : Nat.card J' = Nat.card K * (Nat.card K ^ 2 - 1) / 2) :
    conjU h hA.1 (kappaU h hQ) = negOneU h * kappaU h hQ ∧
      thU p f K (kappaU h hQ) ∉ J' ∧
      center ↥(J' ⊔ zpowers (thU p f K (kappaU h hQ))) = ⊥ ∧
      ∃ A₈ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)),
        A₈ ≤ J' ⊔ zpowers (thU p f K (kappaU h hQ)) ∧ GrSLit.IsElemTwo A₈ ∧ Nat.card A₈ = 8 := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  have hKc := h.card_eq_sq
  set θ := thU p f K with hθ
  set π := θ.comp (pairU h hQ) with hπ
  set κ := kappaU h hQ with hκ
  have hAeq : A = Q₀ * X1GL hl0 * Q₀⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change (A : Matrix (Fin 4) (Fin 4) K) = (Q₀ : Matrix (Fin 4) (Fin 4) K) * X1 l *
      ((Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [← hAQ, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hX1c : ∀ a : SpecialLinearGroup (Fin 2) K,
      X1GL hl0 * SpecialLinearGroup.toGL (pairSL h a) =
        SpecialLinearGroup.toGL (pairSL h a) * X1GL hl0 :=
    fun a => Units.ext (pair_comm_X1 h a l).symm
  have hcomA : ∀ a, conjU h hA.1 (pairU h hQ a) = pairU h hQ a := by
    intro a
    apply Subtype.ext
    rw [coe_conjU, coe_pairU, hAeq]
    calc Q₀ * X1GL hl0 * Q₀⁻¹ * (Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹) *
          (Q₀ * X1GL hl0 * Q₀⁻¹)⁻¹ =
          Q₀ * (X1GL hl0 * SpecialLinearGroup.toGL (pairSL h a)) * (X1GL hl0)⁻¹ * Q₀⁻¹ := by
          group
      _ = Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹ := by rw [hX1c]; group
  set n : GL (Fin 4) K := ((negOneU h : unitarySU p f K 4) : GL (Fin 4) K) with hn
  have hk : X1GL hl0 * swapGL * (X1GL hl0)⁻¹ = n * swapGL := by
    apply Units.ext
    rw [X1_swap_X1, Units.val_mul, hn, coe_negOneU]
    change -blk 0 1 1 0 = -1 * blk 0 1 1 0
    rw [neg_one_mul]
  have hnc : n * Q₀ = Q₀ * n := GeneralLinearGroup.scalar_commute _ Q₀
  have hAκ : conjU h hA.1 κ = negOneU h * κ := by
    apply Subtype.ext
    rw [coe_conjU, hAeq, Subgroup.coe_mul]
    change Q₀ * X1GL hl0 * Q₀⁻¹ * (Q₀ * swapGL * Q₀⁻¹) * (Q₀ * X1GL hl0 * Q₀⁻¹)⁻¹ =
      n * (Q₀ * swapGL * Q₀⁻¹)
    calc Q₀ * X1GL hl0 * Q₀⁻¹ * (Q₀ * swapGL * Q₀⁻¹) * (Q₀ * X1GL hl0 * Q₀⁻¹)⁻¹ =
          Q₀ * (X1GL hl0 * swapGL * (X1GL hl0)⁻¹) * Q₀⁻¹ := by group
      _ = Q₀ * n * swapGL * Q₀⁻¹ := by rw [hk]; group
      _ = n * (Q₀ * swapGL * Q₀⁻¹) := by rw [← hnc]; group
  have hθneg : θ (negOneU h) = 1 := thU_negOneU h
  have hcc : θ κ * θ κ = 1 := by rw [← map_mul, hκ, kappaU_sq, hθneg]
  have hcσ : ∀ a, θ κ * π a * θ κ = π (SpecialLinearGroup.map h.bar a) := by
    intro a
    have h1 : κ * pairU h hQ a * κ = pairU h hQ (SpecialLinearGroup.map h.bar a) * negOneU h := by
      rw [← kappaU_conj_pairU h hQ a, ← hκ, ← kappaU_sq h hQ, ← hκ]
      group
    change θ κ * θ (pairU h hQ a) * θ κ = θ (pairU h hQ (SpecialLinearGroup.map h.bar a))
    rw [← map_mul, ← map_mul, h1, map_mul, hθneg, mul_one]
  have hscal : ∀ s : unitarySU p f K 4, θ s = 1 → ∃ c : Kˣ,
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (c : K) • 1 := fun s hs =>
    val_of_mem_scal ((QuotientGroup.eq_one_iff s).mp hs)
  have hconjback : ∀ (D : GL (Fin 4) K) (c : K),
      ((Q₀ * D * Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • 1 →
        (D : Matrix (Fin 4) (Fin 4) K) = c • 1 := by
    intro D c hD
    have h1 : (D : Matrix (Fin 4) (Fin 4) K) =
        ((Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((Q₀ * D * Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (Q₀ : Matrix (Fin 4) (Fin 4) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [h1, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hker : ∀ a, π a = 1 ↔ a = 1 ∨ a = -1 := by
    intro a
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := hscal _ ha
      rw [coe_pairU] at hc
      have hD := hconjback _ _ hc
      change ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _ at hD
      have hsc : (c : K) • (1 : Matrix (Fin 4) (Fin 4) K) = bd ((c : K) • 1) ((c : K) • 1) := by
        rw [← scalar_eq_bd, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      rw [coe_pairSL, hsc] at hD
      obtain ⟨ha1, -⟩ := bd_inj hD
      have hdet := a.2
      rw [ha1, det_smul, det_one, mul_one, Fintype.card_fin, pow_two] at hdet
      rcases mul_self_eq_one_iff.mp hdet with hc1 | hc1
      · left
        apply Subtype.ext
        rw [ha1, hc1, one_smul]
        rfl
      · right
        apply Subtype.ext
        rw [ha1, hc1, neg_one_smul]
        rfl
    · rintro (rfl | rfl)
      · exact map_one π
      · change θ (pairU h hQ (-1)) = 1
        have h1 : pairU h hQ (-1 : SpecialLinearGroup (Fin 2) K) = negOneU h := by
          apply Subtype.ext
          apply Units.ext
          rw [coe_pairU, pairSL_neg_one, coe_negOneU]
          change (Q₀ : Matrix (Fin 4) (Fin 4) K) * (-1) *
            ((Q₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1
          rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel,
            Units.val_one]
        rw [h1, hθneg]
  have hcπ : θ κ ∉ π.range := by
    rintro ⟨a, ha⟩
    change θ (pairU h hQ a) = θ κ at ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at ha
    obtain ⟨c, hc⟩ := val_of_mem_scal ha
    have h1 : ((pairU h hQ a)⁻¹ * κ : unitarySU p f K 4) = ⟨Q₀ * ((SpecialLinearGroup.toGL
        (pairSL h a))⁻¹ * swapGL) * Q₀⁻¹, by
          rw [show Q₀ * ((SpecialLinearGroup.toGL (pairSL h a))⁻¹ * swapGL) * Q₀⁻¹ =
            (Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹)⁻¹ * (Q₀ * swapGL * Q₀⁻¹) by group]
          exact mul_mem (inv_mem (pairU h hQ a).2) κ.2⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_pairU]
      change (Q₀ * SpecialLinearGroup.toGL (pairSL h a) * Q₀⁻¹)⁻¹ * (Q₀ * swapGL * Q₀⁻¹) = _
      group
    rw [h1] at hc
    have hD := hconjback _ _ hc
    rw [Units.val_mul] at hD
    have hD' : ((swapGL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (c : K) •
        ((SpecialLinearGroup.toGL (pairSL h a) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have h2 := congrArg (fun M => ((SpecialLinearGroup.toGL (pairSL h a) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * M) hD
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one] at h2
      exact h2
    have e := congrFun (congrFun hD' 0) 3
    change blk (0 : K) 1 1 0 0 3 = (c : K) * ((pairSL h a : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) 0 3 at e
    rw [coe_pairSL] at e
    simp [blk, bd] at e
  set C := (Subgroup.centralizer {A}).comap (unitarySU p f K 4).subtype with hC
  have hq9 : 9 ≤ Nat.card K := by
    rw [hKc]
    have h3 : 3 ≤ p ^ f := by
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    nlinarith
  have hcard : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J' := by
    have heven : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      rcases Nat.even_or_odd (Nat.card K) with he | ho
      · exact (even_iff_two_dvd.mp he).mul_right _
      · exact (even_iff_two_dvd.mp (Nat.Odd.sub_odd ho.pow odd_one)).mul_left _
    have h4 : (p ^ f) ^ 4 = Nat.card K ^ 2 := by rw [hKc]; ring
    rw [hJc, h4, ← hKc]
    have := Nat.mul_div_cancel' heven
    omega
  have hJ'eq := CSU.eq_map_commutator h hp2 Q₀ hQ hl0 hA hAQ hJφ hJp hcard C hC
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
    apply LinearGroups.special_linear_dimension_two_perfect
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have hrangeC : (pairU h hQ).range ≤ C := by
    rintro _ ⟨a, rfl⟩
    rw [hC, Subgroup.mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (hcomA a)
    rw [coe_conjU] at h1
    calc (pairU h hQ a : GL (Fin 4) K) * A = A * (pairU h hQ a : GL (Fin 4) K) * A⁻¹ * A := by
          rw [h1]
      _ = A * (pairU h hQ a : GL (Fin 4) K) := by group
  have hrangep : ⁅(pairU h hQ).range, (pairU h hQ).range⁆ = (pairU h hQ).range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hle : π.range ≤ J' := by
    rw [hJ'eq]
    rintro _ ⟨a, rfl⟩
    refine ⟨pairU h hQ a, ?_, rfl⟩
    have hmem : pairU h hQ a ∈ ⁅(pairU h hQ).range, (pairU h hQ).range⁆ := by
      rw [hrangep]
      exact ⟨a, rfl⟩
    exact Subgroup.commutator_mono hrangeC hrangeC hmem
  have hkercard : Nat.card π.ker ≤ 2 := by
    let g : π.ker → Bool := fun a => decide ((a : SpecialLinearGroup (Fin 2) K) = 1)
    have hg : Function.Injective g := by
      intro a b hab
      have ha := (hker a).mp a.2
      have hb := (hker b).mp b.2
      apply Subtype.ext
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]
      · exfalso
        simp only [g, ha, hb, decide_true] at hab
        have h1 : (-1 : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
          intro h1
          have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
          simp at this
          apply h2K
          linear_combination -this
        exact h1 (of_decide_eq_true hab.symm)
      · exfalso
        simp only [g, ha, hb, decide_true] at hab
        have h1 : (-1 : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
          intro h1
          have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
          simp at this
          apply h2K
          linear_combination -this
        exact h1 (of_decide_eq_true hab)
      · rw [ha, hb]
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have hrangecard : Nat.card J' ≤ Nat.card π.range := by
    have h1 := Subgroup.card_mul_index π.ker
    rw [Subgroup.index_ker, SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
    rw [hJc]
    have hpos : 0 < Nat.card π.ker := Nat.card_pos
    calc Nat.card K * (Nat.card K ^ 2 - 1) / 2 ≤
        Nat.card π.ker * Nat.card π.range / 2 := by rw [h1]
      _ ≤ 2 * Nat.card π.range / 2 := Nat.div_le_div_right (Nat.mul_le_mul_right _ hkercard)
      _ = Nat.card π.range := by omega
  have hJ : π.range = J' := Subgroup.eq_of_le_of_card_ge hle hrangecard
  obtain ⟨t₀, ht₀⟩ := h.exists_bar_ne
  have : Finite h.fixedField := Subtype.finite
  have hk₀odd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  obtain ⟨a₀, b₀, hab₀⟩ := OddClassSelector.exists_sq_add_sq hk₀odd (-1)
  have hab : (a₀ : K) ^ 2 + (b₀ : K) ^ 2 = -1 := by
    have := congrArg (h.fixedField.subtype) hab₀
    simpa using this
  have hσa : h.bar (a₀ : K) = a₀ := (h.mem_fixedField).mp a₀.2
  have hσb : h.bar (b₀ : K) = b₀ := (h.mem_fixedField).mp b₀.2
  have : Finite (StatedProj (StatedSU 4 (p ^ f) K)) := inferInstance
  refine ⟨hAκ, hJ ▸ hcπ, ?_, ?_⟩
  · rw [← hJ]
    exact center_sup_eq_bot π h2K hker hcc hcσ hcπ ht₀
  · rw [← hJ]
    exact exists_eight_le_sup π h2K hker hcc hcσ hcπ hab hσa hσb

end CFSG.ComponentClassification.HarrisLit.C3
