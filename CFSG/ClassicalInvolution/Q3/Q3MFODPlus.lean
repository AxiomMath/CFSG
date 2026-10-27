module

public import CFSG.ClassicalInvolution.Q3.Q3MFODData
public import CFSG.ClassicalInvolution.Q3.Q3MFODOrb
public import CFSG.ClassicalInvolution.Q3.Q3MFODStd
public import CFSG.ClassicalInvolution.Q3.Q3MFODSimAt
public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import CFSG.ClassicalInvolution.AschTight.S19KUniFL
public import CFSG.ClassicalInvolution.Q3.Q3MFODHyp
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3OFModelU
public import CFSG.ClassicalInvolution.Q3.Q3OFProd
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTri
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3PPInv
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3MFOD CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.G2D4Models.Twin
  CFSG.ClassicalInvolution.Q3.Q3T
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame)
open CFSG.ClassicalInvolution.Models.Transfer (centerScalar_quadPlus)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Generic

theorem mul_self_eq_one_of_lift {K : Type} [Group K] [Group.IsPerfect K] (α : MulAut K)
    (ρ : MulAut (K ⧸ Subgroup.center K)) (hρ2 : ρ * ρ = 1)
    (hα : ∀ x, (QuotientGroup.mk (α x) : K ⧸ Subgroup.center K) = ρ (QuotientGroup.mk x)) :
    α * α = 1 := by
  have hc : ∀ s ∈ (⊤ : Subgroup K), s⁻¹ * (α * α) s ∈ Subgroup.center K := by
    intro s _
    have h1 : (QuotientGroup.mk (α (α s)) : K ⧸ Subgroup.center K) = QuotientGroup.mk s := by
      rw [hα, hα]
      have := congrArg (fun m : MulAut (K ⧸ Subgroup.center K) => m (QuotientGroup.mk s)) hρ2
      simpa using this
    exact QuotientGroup.eq.mp h1.symm
  have hfix := ModelFacts.Orth15.alpha_fixes_commutators (α * α) hc
  have hP : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = (⊤ : Subgroup K) := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  refine MulEquiv.ext fun s => ?_
  exact hfix s (by rw [hP]; exact Subgroup.mem_top s)

theorem oddCoreIn_fixed_of_conj_transfer {X : Type} [Group X] (σ α : MulAut X)
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient X (σ * α * σ⁻¹))) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient X α)) = ⊥ := by
  have hmul : autToCentralQuotient X (σ * α * σ⁻¹) =
      autToCentralQuotient X σ * autToCentralQuotient X α * (autToCentralQuotient X σ)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have h' := Q3NM.oddCoreIn_fixed_conj_eq_bot (autToCentralQuotient X σ)⁻¹ _ h
  rw [hmul] at h'
  have e : (autToCentralQuotient X σ)⁻¹ * (autToCentralQuotient X σ * autToCentralQuotient X α *
      (autToCentralQuotient X σ)⁻¹) * ((autToCentralQuotient X σ)⁻¹)⁻¹ =
      autToCentralQuotient X α := by group
  rwa [e] at h'

end Generic


section Plus4

theorem oddCoreIn_fixed_of_pres_plus4 [Finite (spinGroup Q₄)]
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q₄))) {R' : Subgroup (spinGroup Q₄)}
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (α' : MulAut (spinGroup Q₄)) (hα'2 : α' * α' = 1) (hpres : Pres α')
    (hfix : ∀ r ∈ R', α' r = r) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q₄) α')) = ⊥ := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hrange := range_spinAction_quadPlus (K := 𝔽₃) hn3
  have hEq := (commutator_orthogonalGroup_quadPlus (K := 𝔽₃) hn3).symm
  have cq := Q3TY.centralQuot3_plus (m := 4) le_rfl
  have hadmL : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hSL : CFSG.Open.IsQuasisimple SL(4, 𝔽₃) :=
    (ModelFacts.modelClauseZero .PSL 4 3 1 Nat.prime_three trivial hadmL).1
  have hSLZ : IsPGroup 2 (Subgroup.center SL(4, 𝔽₃)) :=
    (modelFiniteCenterTwoGroup3 .PSL 4 Nat.prime_three trivial hadmL).2
  have hdim : 6 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  obtain ⟨a, μ, hμ, hsim, hαa⟩ := exists_sim_of_mat3 hF3 α'
    (spin_plus4_sim_of_family α' (descAut α') (descAut_apply α') hpres)
  obtain ⟨i, fr, hfr, -⟩ := cq.map_mem _ hR'
  have hLa : ∀ B : SL(2, 𝔽₃), a * fr.La B = fr.La B * a := by
    intro B
    have hmem : fr.La B ∈ R'.map (spinAction Q₄) := by
      rw [hfr]
      exact ⟨B, rfl⟩
    obtain ⟨r, hr, hrB⟩ := hmem
    have h1 := hαa r
    rw [hfix r hr, hrB] at h1
    calc a * fr.La B = (a * fr.La B * a⁻¹) * a := by group
      _ = fr.La B * a := by rw [← h1]
  exact oddCoreIn_fixed_of_sim_data hF3 hQ hdim hrange hEq
    (ModelFacts.open_isQuasisimple (isQuasisimple_spinGroup_quadPlus hn3)) hZ2 α' fr hμ hsim
    hαa hα'2 hLa
    (fun haa hμ' hg' => oddCoreIn_fixed_conjES_of_sim_involution hF3 hSL hSLZ hQ hEq haa hg')

theorem oddCoreIn_fixed_of_lift_plus4 [Finite (spinGroup Q₄)]
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q₄))) {R : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (α : MulAut (spinGroup Q₄)) (hα2 : α * α = 1) (hαR : ∀ r ∈ R, α r = r) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q₄) α)) = ⊥ := by
  classical
  obtain ⟨σ, hσ, hpres⟩ := exists_pres_conj α hα2
  have hα'2 : σ * α * σ⁻¹ * (σ * α * σ⁻¹) = 1 := by
    calc σ * α * σ⁻¹ * (σ * α * σ⁻¹) = σ * (α * α) * σ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have hfix : ∀ r' ∈ R.map σ.toMonoidHom, (σ * α * σ⁻¹) r' = r' := by
    rintro _ ⟨r, hr, rfl⟩
    show (σ * α * σ⁻¹) (σ r) = σ r
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hαR r hr]
  exact oddCoreIn_fixed_of_conj_transfer σ α
    (oddCoreIn_fixed_of_pres_plus4 hZ2 (hσ R hR) (σ * α * σ⁻¹) hα'2 hpres hfix)

theorem exists_lift_plus4 [Finite (spinGroup Q₄)]
    (ρ : MulAut (spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄))) :
    ∃ α : MulAut (spinGroup Q₄), ∀ x, (QuotientGroup.mk (α x) :
      spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄)) = ρ (QuotientGroup.mk x) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  obtain ⟨-, hcomap, hZc⟩ := spinToStatedProj_quadPlus (K := 𝔽₃) hn3
  have hψk : (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))).ker ≤
      Subgroup.center (spinGroup Q₄) := by
    rw [QuotientGroup.ker_mk']
  have hC : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))).ker := fun hd =>
    not_dvd_card_center_spin (quadPlus 4 𝔽₃) (range_spinMatrix_quadPlus hn3) hZc hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) (p := 3)
      (by norm_num) (hd.trans (Subgroup.card_dvd_of_le hψk))
  obtain ⟨α, hα⟩ := (centralPSection_spinPlus (p := 3) (F := 𝔽₃) hn3).exists_mulEquiv_lift
    (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))) (QuotientGroup.mk'_surjective _) hψk hC ρ
  exact ⟨α, hα⟩

theorem fixes_of_lift_plus4 [Finite (spinGroup Q₄)] {R : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (α : MulAut (spinGroup Q₄)) (ρ : MulAut (spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄)))
    (hα : ∀ x, (QuotientGroup.mk (α x) : spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄)) =
      ρ (QuotientGroup.mk x))
    (hρR : ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r) : ∀ r ∈ R, α r = r := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have : Nontrivial (Fin 4 ⊕ Fin 4 → 𝔽₃) :=
    Module.nontrivial_of_finrank_pos (R := 𝔽₃) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      norm_num)
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q₄), ¬ 3 ∣ orderOf c :=
    Q3OT.center_no_three hF3 (range_spinAction_quadPlus (K := 𝔽₃) hn3)
      (centerScalar_quadPlus (K := 𝔽₃) hn3) (ModelFacts.OrthAut.plus_hker2 (F := 𝔽₃) 4)
  have hψk : (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))).ker ≤
      Subgroup.center (spinGroup Q₄) := by
    rw [QuotientGroup.ker_mk']
  exact Q3TY.eq_of_fixed_of_pow3 (QuotientGroup.mk' (Subgroup.center (spinGroup Q₄))) hψk
    (fun z hz => hZ3 z (hψk hz)) α ρ hα ((Q3TY.centralQuot3_plus (m := 4) le_rfl).pow3 R hR) hρR

theorem fixedOddFree_aux_plus4 [Finite (spinGroup Q₄)]
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q₄)))
    (ρ : MulAut (spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄))) (hρ2 : ρ * ρ = 1)
    (hfix : ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)),
      ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus (by norm_num)
  obtain ⟨R, hR, hρR⟩ := hfix
  obtain ⟨α, hα⟩ := exists_lift_plus4 ρ
  have hρeq : ρ = autToCentralQuotient (spinGroup Q₄) α := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    rw [autToCentralQuotient_mk, hα]
  rw [hρeq]
  exact oddCoreIn_fixed_of_lift_plus4 hZ2 hR α (mul_self_eq_one_of_lift α ρ hρ2 hα)
    (fixes_of_lift_plus4 hR α ρ hα hρR)

theorem fixedOddFreeFund_spin_plus4 (hfin : Finite (spinGroup Q₄))
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q₄))) :
    FixedOddFreeFund (⟨spinGroup Q₄, fundamentalSubgroups .POmegaPlus
      (plusDatum 4 𝔽₃ (by norm_num))⟩ : CompData) := by
  have : Finite (spinGroup Q₄) := hfin
  exact fun ρ hρ2 hfix => fixedOddFree_aux_plus4 hZ2 ρ hρ2 hfix

end Plus4

theorem fixedOddFreeFund_plus4 : FixedOddFreeFund (CompData.model .POmegaPlus 4) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨hp, le_rfl, le_rfl⟩
  have hfz := modelFiniteCenterTwoGroup3 .POmegaPlus 4 hp trivial hadm
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ hn3⟩ →
      Finite M.K ∧ IsPGroup 2 (Subgroup.center M.K) →
      FixedOddFreeFund (⟨M.K, fundamentalSubgroups .POmegaPlus M.D⟩ : CompData) := by
    intro M hM hMf
    subst hM
    exact fixedOddFreeFund_spin_plus4 hMf.1 hMf.2
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num)) hfz

theorem mfComp_plus4 : MFComp (CompData.model .POmegaPlus 4) := Or.inr fixedOddFreeFund_plus4

end CFSG.ClassicalInvolution.Q3.Q3PP
