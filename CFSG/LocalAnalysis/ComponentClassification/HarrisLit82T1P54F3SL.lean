module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Spin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SL
public import CFSG.LieType.Steinberg.CentralExt.SLThree
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL blockSL_injective)
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open Matrix
open scoped MatrixGroups

theorem range_inf_center_eq_bot_of_sl2 {K : Type*} [Field K] {G : Type*} [Group G]
    {ρ : SL(2, K) →* G} (hρ : Function.Injective ρ) (hZ : ρ (-1) ∉ center G) :
    ρ.range ⊓ center G = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [mem_inf] at ha
  obtain ⟨⟨A, rfl⟩, haZ⟩ := ha
  have hA : A ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro B
    apply hρ
    rw [map_mul, map_mul]
    exact mem_center_iff.mp haZ _
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff A).mp hA with rfl | rfl
  · rw [map_one]
    exact one_mem _
  · exact absurd haZ hZ

namespace SL

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem blockSL_two_inf_center {n : ℕ} (hn : 2 ≤ n) (hj : 2 + (n - 2) ≤ n) :
    (blockSL K n (n - 2) 2 hj).range ⊓ center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_inf] at hx
  obtain ⟨⟨A, rfl⟩, hxZ⟩ := hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxZ
  have h1 := congrFun (congrFun hr ⟨0, by omega⟩) ⟨0, by omega⟩
  rw [coe_blockSL, blockMat_apply, dite_eq_right (by simp), Matrix.one_apply_eq,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  refine (mem_bot).mpr (Subtype.ext ?_)
  rw [← hr, h1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem rawF3_sl (hK3 : Nat.card K = 3) {n : ℕ} (hn4 : 4 ≤ n)
    (hn2 : Even n) {a : SpecialLinearGroup (Fin n) K}
    (ham : (a : Matrix (Fin n) (Fin n) K) = -1) : RawF3 (SpecialLinearGroup (Fin n) K) a := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hn : 2 ≤ n := by omega
  have haZ : a ∈ center (SpecialLinearGroup (Fin n) K) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ham,
      Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  set u := rootInv K hn with hu
  have hcl := isClassicalSL2_rootSL2 h2 hn
  have huZ : u ∉ center (SpecialLinearGroup (Fin n) K) := by
    intro h
    obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have hum : (u : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) s := hs.symm
    rw [hu, coe_rootInv, negBlock_eq_diagonal] at hum
    have e0 := congrFun (congrFun hum ⟨0, by omega⟩) ⟨0, by omega⟩
    have e2 := congrFun (congrFun hum ⟨2, by omega⟩) ⟨2, by omega⟩
    simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e0 e2
    rw [ite_eq_left (by simp)] at e0
    rw [ite_eq_right (by simp)] at e2
    exact h2 (by linear_combination e2 - e0)
  obtain ⟨eK⟩ := nonempty_sl2_equiv_zmod_three hK3
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hJ₁Z : rootSL2 K hn ⊓ center (SpecialLinearGroup (Fin n) K) = ⊥ :=
    range_inf_center_eq_bot_of_sl2 (blockSL_injective _) huZ
  have hJ₁n := (isLongRootSL2_standard hn).normal_subgroupOf_centralizer h2
  have hj : 2 + (n - 2) ≤ n := by omega
  set J₂ := (blockSL K n (n - 2) 2 hj).range with hJ₂
  have hJ₂' : J₂ = longRootGroup (-negBlock K n 0) := by
    rw [hJ₂, SL.range_blockSL_eq_longRootGroupK h2 hj, SL.negBlockK_two_eq_neg n hn]
  let eJ : SpecialLinearGroup (Fin (n - 2)) K ≃* J₂ := MonoidHom.ofInjective (blockSL_injective hj)
  have hcomm : ∀ {c : SpecialLinearGroup (Fin n) K}, c ∈ centralizer {u} →
      (c : Matrix (Fin n) (Fin n) K) * -negBlock K n 0 = -negBlock K n 0 * c := by
    intro c hc
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (mem_centralizer_singleton_iff.mp hc)
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, coe_rootInv] at h1
    rw [Matrix.mul_neg, Matrix.neg_mul, h1]
  have hJle : J₂ ≤ centralizer {u} := by
    intro x hx
    rw [hJ₂'] at hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := hx.1
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, coe_rootInv]
    exact h1
  have hJn : (J₂.subgroupOf (centralizer {u})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJle]
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    rw [hJ₂']
    constructor
    · exact fun hx => conj_mem_longRootGroup_of_commute (hcomm hc) hx
    · intro hx
      have := conj_mem_longRootGroup_of_commute (hcomm (inv_mem hc)) hx
      rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  have hneg : (-1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K).det = 1 := by
    rw [det_neg, det_one, mul_one, Fintype.card_fin]
    exact (Even.neg_one_pow (by obtain ⟨m, hm⟩ := hn2; exact ⟨m - 1, by omega⟩))
  have hau : a * u = blockSL K n (n - 2) 2 hj (⟨-1, hneg⟩ : SL(n - 2, K)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ham, hu, coe_rootInv]
    change -1 * negBlock K n 0 = SL.negBlockK K n 2 (n - 2)
    rw [SL.negBlockK_two_eq_neg n hn, neg_one_mul]
  have hauJ : a * u ∈ J₂ := by
    rw [hau, hJ₂]
    exact ⟨_, rfl⟩
  have hJ₂Z : J₂ ⊓ center (SpecialLinearGroup (Fin n) K) = ⊥ := blockSL_two_inf_center hn hj
  refine ⟨u, hcl.orderOf_eq_two, huZ, rootSL2 K hn, J₂, hcl.le_centralizer,
    hJ₁n.isSubnormal, hcl.mem, hJ₁Z, ⟨eL.trans eK⟩, ?_, .inr hauJ⟩
  rcases Nat.lt_or_ge n 6 with hn6 | hn6
  ·
    obtain rfl : n = 4 := by
      obtain ⟨k, hk⟩ := hn2
      omega
    exact .inr ⟨hJle, hJn.isSubnormal, hJ₂Z, ⟨eJ.symm.trans eK⟩⟩
  ·
    have hqS := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
      (n - 2) K (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    have hqJ : IsQuasisimple J₂ := LocalCores.isQuasisimple_of_mulEquiv eJ hqS
    have h2J : 2 ∣ Nat.card J₂ := by
      have hau2 : orderOf (a * u) = 2 := by
        have hcomm' : a * u = u * a := (mem_center_iff.mp haZ u).symm
        have huu : u * u = 1 := by rw [← sq, ← hcl.orderOf_eq_two, pow_orderOf_eq_one]
        have ha2 : a * a = 1 := Subtype.ext (by
          rw [Matrix.SpecialLinearGroup.coe_mul, ham, Matrix.SpecialLinearGroup.coe_one]
          simp)
        refine orderOf_eq_prime ?_ fun h => huZ ?_
        · rw [sq]
          calc a * u * (a * u) = a * (u * a) * u := by group
            _ = a * (a * u) * u := by rw [← hcomm']
            _ = a * a * (u * u) := by group
            _ = 1 := by rw [ha2, huu, one_mul]
        · have : u = a⁻¹ := eq_inv_of_mul_eq_one_right h
          rw [this]
          exact inv_mem haZ
      have h1 := orderOf_dvd_natCard (⟨a * u, hauJ⟩ : J₂)
      rwa [Subgroup.orderOf_mk, hau2] at h1
    have hadm : StatedLieAdmissible .PSL (n - 2) 3 1 := by
      refine ⟨Nat.prime_three, le_rfl, by omega, ?_, ?_⟩ <;>
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
    have hlie : Blueprint.LieModel (↥J₂ ⧸ center ↥J₂) .PSL (n - 2) 3 1 :=
      Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, by rw [hK3, pow_one],
        ⟨(QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).symm.trans
          (projectiveSpecialLinearGroupEquivStatedProj (n - 2) K)⟩⟩⟩
    exact .inl ⟨⟨hJle, hJn.isSubnormal, SL.isTwoQuasisimple_of_isQuasisimple hqJ h2J⟩, hqJ,
      ⟨.PSL, n - 2, hlie⟩⟩

end SL

theorem rowSLThree : RowSLThree := by
  intro Y _ _ hq hZ τ n ⟨hτ, hn2⟩ hlie hc t ht htZ
  subst hτ
  rcases hlie with ⟨-, ⟨-, -, hn, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hn4 : 4 ≤ n := by
    obtain ⟨k, hk⟩ := hn2
    have h3 : n ≠ 2 := fun h => h23 (by rw [h]; norm_num)
    omega
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let e' : Y ⧸ center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj (m + 1) K).symm
  obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover
    (β := QuotientGroup.mk' (center (SpecialLinearGroup (Fin (m + 1)) K)))
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen _ => LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_card_three
      (by omega) hK3 hπ hcen) hq hZ e'
  rw [QuotientGroup.ker_mk'] at hαZ hαk
  obtain ⟨a, haZ, rfl⟩ := (show t ∈ (center (SpecialLinearGroup (Fin (m + 1)) K)).map α from
    hαZ ▸ htZ)
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp haZ
  have ha1 : a ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hr1 : r ≠ 1 := fun h =>
    ha1 (Subtype.ext (by rw [← hr, h, map_one, Matrix.SpecialLinearGroup.coe_one]))
  have hrm : r = -1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := Fintype.ofFinite K
    have hsq : r * r = 1 := by
      have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK3]
      have h0 : r ≠ 0 := fun h0 => by
        rw [h0, zero_pow (by simp)] at hr3
        exact zero_ne_one hr3
      have := FiniteField.pow_card_sub_one_eq_one r h0
      rw [hcard] at this
      simpa [sq] using this
    exact (mul_self_eq_one_iff.mp hsq).resolve_left hr1
  have ham : (a : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = -1 := by
    rw [← hr, hrm, map_neg, map_one]
  exact (SL.rawF3_sl hK3 hn4 hn2 ham).concl3
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple (m + 1) K
      (by omega) (Or.inl (by omega)) (Or.inl (by omega))) hαs hαk ht haZ

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
