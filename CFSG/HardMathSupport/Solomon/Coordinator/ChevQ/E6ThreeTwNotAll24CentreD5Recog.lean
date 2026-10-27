module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChainE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.WeakCT.SU4
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal.Unitary CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.SU4Even
  CFSG.ClassicalInvolution.WeakCT CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDChain
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDChainE
  CFSG.LieType.Chevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem center_spinGroup_quadMinus_pow_four {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 4 ≤ n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (x : spinGroup (quadMinus n F b c)) (hx : x ∈ Subgroup.center (spinGroup (quadMinus n F b c))) :
    x ^ 4 = 1 := by
  rw [← (spinToStatedProj_quadMinus hn hirr).2.2, (spinToStatedProj_quadMinus hn hirr).2.1,
    Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨d, hd⟩ := mem_scalars.mp hx
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_hypPair _
    (minusPair F b c (⟨0, by omega⟩ : Fin (n - 1)))
  have hd2 : d * d = 1 := by
    have h := map_spinAction (quadMinus n F b c) x v₀
    rw [hd, map_smul_eq_sq] at h
    have h' : (d ^ 2 - 1) * (quadMinus n F b c) v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
    linear_combination (mul_eq_zero.mp h').resolve_right hv₀
  have := isCentral_cliffordAlgebra_quadMinus n b c hirr
  have hxx : x * x ∈ (spinAction (quadMinus n F b c)).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul, LinearEquiv.mul_apply, hd, hd, smul_smul, hd2, one_smul]
    rfl
  have h1 := CFSG.ClassicalInvolution.ModelFacts.OrthAut.minus_hker2 hirr (x * x) hxx
  calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h1

@[expose] def DStrongModel {G : Type} [Group G] (C : Subgroup G) (m r e : ℕ) : Prop :=
  LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaMinus m r e ∧ CFSG.IsQuasisimple ↥C ∧
    ∀ z ∈ Subgroup.center ↥C, z ^ 4 = 1

section Main


theorem strongModel_of_chain {k : Type} [Field k] {G : Type} [Group G] {n p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hp2 : p ≠ 2)
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {σ₀ : K ≃+* K} {b c : F} (D : KleinData F K σ₀ b c)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ι : K →+* k) (ρ : ℕ → SL(2, k) →* G) (hρ : ∀ i, i < n → Function.Injective (ρ i))
    (hcomm : ∀ i j : ℕ, i < n → j < n → i ≠ j → ¬ dEdge n i j → ¬ dEdge n j i →
      ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A)
    (hfr : ∀ i : ℕ, i + 3 < n → ∃ θ : SL(3, k) →* G,
      θ.comp (blockSL k 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL k 3 2 1 (by omega)) = ρ (i + 1))
    (Φ : SL(4, k) →* G) (hΦ0 : Φ.comp (blockSL2 k 3 0) = ρ (n - 2))
    (hΦ1 : Φ.comp (blockSL2 k 3 1) = ρ (n - 3)) (hΦ2 : Φ.comp (blockSL2 k 3 2) = ρ (n - 1))
    (C : Subgroup G)
    (hC : (⨆ i : Fin (n - 1),
      if i.val + 2 < n then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap F K)))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range) = C) :
    DStrongModel C n p f := by
  classical
  have hn4 : 4 ≤ n := hadm.2.2
  have h2F : (2 : F) ≠ 0 := by
    have hp := hadm.1
    have hf := hadm.2.1
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  set ιF : F →+* k := ι.comp (algebraMap F K) with hιF
  set Vg : Subgroup G := ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
    (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range with hVg
  set nodeG : Fin (n - 1) → Subgroup G := fun i =>
    if i.val + 2 < n then ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).range else Vg
    with hnodeG
  have hCeq : (⨆ i, nodeG i) = C := hC
  have hN : ∀ i, nodeG i ≤ C := fun i => hCeq ▸ le_iSup nodeG i
  set U : Fin (n - 1) → Subgroup ↥C := fun i => (nodeG i).subgroupOf C with hU
  have hgen : ⨆ i, U i = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    have : ∀ i, (U i).map C.subtype = nodeG i := fun i => by
      rw [hU, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 (hN i)
    simp only [this]
    exact hCeq
  have hlongVg : ∀ i : ℕ, i + 4 ≤ n → ∀ (A : SL(2, k)) (B : SL(2, K)),
      ρ i A * Φ (Matrix.SpecialLinearGroup.map ι (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D) B)) =
        Φ (Matrix.SpecialLinearGroup.map ι (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D) B)) *
          ρ i A := by
    intro i hi A B
    rw [phi_usbSL ι _ Φ hΦ0 hΦ2]
    exact mul_comm_of_mul
      (hcomm i (n - 2) (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _)
      (hcomm i (n - 1) (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _)
  have hcommU : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j,
      u * v = v * u := by
    intro i j hij u hu v hv
    have hi2 : i.val + 2 < n := by have := j.isLt; omega
    refine Subtype.ext ?_
    simp only [hU, hnodeG, if_pos hi2, Subgroup.mem_subgroupOf] at hu
    obtain ⟨A, hA⟩ := hu
    by_cases hj2 : j.val + 2 < n
    · simp only [hU, hnodeG, if_pos hj2, Subgroup.mem_subgroupOf] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hcomm i.val j.val (by omega) (by omega) (by omega) (by simp only [dEdge]; omega)
        (by simp only [dEdge]; omega) _ _
    · simp only [hU, hnodeG, if_neg hj2, Subgroup.mem_subgroupOf, hVg] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hlongVg i.val (by have := j.isLt; omega) _ _
  have hpairU : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hj
    have hi2 : i.val + 2 < n := by omega
    obtain ⟨θk, h0, h1⟩ := hfr i.val (by omega)
    have hnt := exists_ne_one_of_injective_comp θk (blockSL k 3 2 0 (by omega))
      (by rw [h0]; exact hρ _ (by omega))
    have hjv : j.val = i.val + 1 := hij.symm
    have hi' : ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).range ≤ C := by
      have := hN i
      simpa only [hnodeG, if_pos hi2] using this
    have hj' : ((ρ (i.val + 1)).comp (Matrix.SpecialLinearGroup.map ιF)).range ≤ C := by
      have := hN j
      simpa only [hnodeG, if_pos hj, hjv] using this
    obtain ⟨W, hW⟩ := linearPair_of_frame ιF h0 h1 hnt C hi' hj'
    refine ⟨W, ?_⟩
    have hj3 : i.val + 1 + 2 < n := by omega
    simp only [hU, hnodeG, if_pos hi2, hjv, if_pos hj3]
    exact hW
  have htwU : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockPair hirr W (U i) (U j) := by
    intro i j hi hj
    have hiv : i.val = n - 3 := by omega
    have hi2 : i.val + 2 < n := by omega
    have hj2 : ¬ j.val + 2 < n := by omega
    have hni : nodeG i = ((ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF)).range := by
      simp only [hnodeG, if_pos hi2, hiv]
    have hnj : nodeG j = Vg := by simp only [hnodeG, if_neg hj2]
    have hΦinj : Function.Injective
        ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp (blockSL2 K 3 1)) := by
      have e : (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp (blockSL2 K 3 1) =
          (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ι) := by
        ext A : 1
        simp only [MonoidHom.comp_apply, map_blockSL2]
        rw [← hΦ1]
        rfl
      rw [e]
      exact (hρ _ (by omega)).comp (map_injective_sl ι 2)
    have eU : (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K))) =
        (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF) := by
      ext A : 1
      simp only [MonoidHom.comp_apply, map_blockSL2, map_map_sl]
      rw [← hΦ1]
      rfl
    have hUC : ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K)))).range ≤ C := by
      rw [eU]
      have := hN i
      rwa [hni] at this
    have hVC : ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        (usbSL σ₀.toRingHom (CompsPTwoDPair.σσ' D))).range ≤ C := by
      have := hN j
      rwa [hnj] at this
    obtain ⟨W, hW⟩ := CompsPTwoDPair.twistedB2BlockPair_of_sl4 D hirr h2F
      (Φ.comp (Matrix.SpecialLinearGroup.map ι)) hΦinj C hUC hVC
    refine ⟨W, ?_⟩
    rw [eU] at hW
    simp only [hU, hni, hnj, hVg]
    exact hW
  obtain ⟨Ψ, -, -, hq', hcen, hlie, -⟩ := weakCT_spinMinus_of_pair hadm hp2 hF hq hirr U hgen
    hcommU hpairU htwU
  refine ⟨hlie, hq', fun z hz => ?_⟩
  rw [hcen] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [← map_pow, center_spinGroup_quadMinus_pow_four hn4 hirr x hx, map_one]


theorem strongModel_of_chain_even {k : Type} [Field k] {G : Type} [Group G] {n f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f) {σ₀ : K ≃+* K} {b c : F} (D : KleinDataEven F K σ₀ b c)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ι : K →+* k) (ρ : ℕ → SL(2, k) →* G) (hρ : ∀ i, i < n → Function.Injective (ρ i))
    (hcomm : ∀ i j : ℕ, i < n → j < n → i ≠ j → ¬ CompsPTwoDChain.dEdge n i j →
      ¬ CompsPTwoDChain.dEdge n j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A)
    (hfr : ∀ i : ℕ, i + 3 < n → ∃ θ : SL(3, k) →* G,
      θ.comp (blockSL k 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL k 3 2 1 (by omega)) = ρ (i + 1))
    (Φ : SL(4, k) →* G) (hΦ0 : Φ.comp (blockSL2 k 3 0) = ρ (n - 2))
    (hΦ1 : Φ.comp (blockSL2 k 3 1) = ρ (n - 3)) (hΦ2 : Φ.comp (blockSL2 k 3 2) = ρ (n - 1))
    (C : Subgroup G)
    (hC : (⨆ i : Fin (n - 1),
      if i.val + 2 < n then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap F K)))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        (usbSL σ₀.toRingHom (CompsPTwoDPairE.σσ' D))).range) = C) :
    DStrongModel C n 2 f := by
  classical
  have hn4 : 4 ≤ n := hadm.2.2
  haveI : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) := fact_shortField hirr
  set ιF : F →+* k := ι.comp (algebraMap F K) with hιF
  set Vg : Subgroup G := ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
    (usbSL σ₀.toRingHom (CompsPTwoDPairE.σσ' D))).range with hVg
  set nodeG : Fin (n - 1) → Subgroup G := fun i =>
    if i.val + 2 < n then ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).range else Vg
    with hnodeG
  have hCeq : (⨆ i, nodeG i) = C := hC
  have hN : ∀ i, nodeG i ≤ C := fun i => hCeq ▸ le_iSup nodeG i
  set U : Fin (n - 1) → Subgroup ↥C := fun i => (nodeG i).subgroupOf C with hU
  have hgen : ⨆ i, U i = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    have : ∀ i, (U i).map C.subtype = nodeG i := fun i => by
      rw [hU, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 (hN i)
    simp only [this]
    exact hCeq
  have hlongVg : ∀ i : ℕ, i + 4 ≤ n → ∀ (A : SL(2, k)) (B : SL(2, K)),
      ρ i A * Φ (Matrix.SpecialLinearGroup.map ι
          (usbSL σ₀.toRingHom (CompsPTwoDPairE.σσ' D) B)) =
        Φ (Matrix.SpecialLinearGroup.map ι
          (usbSL σ₀.toRingHom (CompsPTwoDPairE.σσ' D) B)) * ρ i A := by
    intro i hi A B
    rw [CompsPTwoDChain.phi_usbSL ι _ Φ hΦ0 hΦ2]
    exact CompsPTwoDChain.mul_comm_of_mul
      (hcomm i (n - 2) (by omega) (by omega) (by omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega) _ _)
      (hcomm i (n - 1) (by omega) (by omega) (by omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega) _ _)
  have hcommU : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j,
      u * v = v * u := by
    intro i j hij u hu v hv
    have hi2 : i.val + 2 < n := by have := j.isLt; omega
    refine Subtype.ext ?_
    simp only [hU, hnodeG, if_pos hi2, Subgroup.mem_subgroupOf] at hu
    obtain ⟨A, hA⟩ := hu
    by_cases hj2 : j.val + 2 < n
    · simp only [hU, hnodeG, if_pos hj2, Subgroup.mem_subgroupOf] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hcomm i.val j.val (by omega) (by omega) (by omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega)
        (by simp only [CompsPTwoDChain.dEdge]; omega) _ _
    · simp only [hU, hnodeG, if_neg hj2, Subgroup.mem_subgroupOf, hVg] at hv
      obtain ⟨B, hB⟩ := hv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB]
      exact hlongVg i.val (by have := j.isLt; omega) _ _
  have hρC : ∀ i : ℕ, i + 2 < n → ∀ A : SL(2, F),
      ((ρ i).comp (Matrix.SpecialLinearGroup.map ιF)) A ∈ C := by
    intro i hi A
    have hi' : (⟨i, by omega⟩ : Fin (n - 1)).val + 2 < n := hi
    have hle : nodeG ⟨i, by omega⟩ ≤ C := hN _
    have h1 : ((ρ i).comp (Matrix.SpecialLinearGroup.map ιF)).range ≤ C := by
      simpa only [hnodeG, if_pos hi'] using hle
    exact h1 ⟨A, rfl⟩
  let ρ' : Fin (n - 2) → (SL(2, F) →* ↥C) := fun i =>
    ((ρ i.val).comp (Matrix.SpecialLinearGroup.map ιF)).codRestrict C
      (hρC i.val (by have := i.2; omega))
  have hρ'U : ∀ i : Fin (n - 2),
      Function.Injective (ρ' i) ∧ (ρ' i).range = U ⟨i.val, by omega⟩ := by
    intro i
    have hi2 : (⟨i.val, by omega⟩ : Fin (n - 1)).val + 2 < n := by
      have := i.2
      show i.val + 2 < n
      omega
    refine ⟨?_, ?_⟩
    · intro A B h
      have h' : ρ i.val (Matrix.SpecialLinearGroup.map ιF A) =
          ρ i.val (Matrix.SpecialLinearGroup.map ιF B) := congrArg Subtype.val h
      exact CompsPTwoDChain.map_injective_sl ιF 2 (hρ i.val (by have := i.2; omega) h')
    · ext x
      simp only [hU, hnodeG, if_pos hi2, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      constructor
      · rintro ⟨A, rfl⟩
        exact ⟨A, rfl⟩
      · rintro ⟨A, hA⟩
        exact ⟨A, Subtype.ext hA⟩
  have hρ'ψ : ∀ i j : Fin (n - 2), i.val + 1 = j.val →
      ∃ ψ : SL(3, F) →* ↥C, ψ.comp (blk F 0) = ρ' i ∧ ψ.comp (blk F 1) = ρ' j := by
    rintro i ⟨j, hj⟩ hij
    simp only at hij
    subst hij
    obtain ⟨θk, h0, h1⟩ := hfr i.val (by have := i.2; omega)
    exact exists_frame_codRestrict ιF h0 h1 C (hρC i.val (by have := i.2; omega))
      (hρC (i.val + 1) (by have := i.2; omega))
  let θ0 : spinGroup (quadMinus 3 F b c) →* G :=
    (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp (CompsPTwoDPairE.theta D hirr)
  have eU : (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
      ((blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K))) =
      (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF) := by
    ext A : 1
    simp only [MonoidHom.comp_apply, CompsPTwoDChain.map_blockSL2, CompsPTwoDChain.map_map_sl]
    rw [← hΦ1]
    rfl
  have hθlb : θ0.comp (minusLongBlock b c) =
      (ρ (n - 3)).comp (Matrix.SpecialLinearGroup.map ιF) := by
    have e : θ0.comp (minusLongBlock b c) = (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((CompsPTwoDPairE.theta D hirr).comp (minusLongBlock b c)) := rfl
    rw [e, CompsPTwoDPairE.theta_comp_lb, eU]
  have hθsb : ((θ0.comp (shortBlock hirr 3 finOne)).range) = Vg := by
    have e : θ0.comp (shortBlock hirr 3 finOne) = (Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
        ((CompsPTwoDPairE.theta D hirr).comp (shortBlock hirr 3 finOne)) := rfl
    rw [e, MonoidHom.range_comp, CompsPTwoDPairE.range_theta_sb, hVg, MonoidHom.range_comp]
  have hθC : ∀ s, θ0 s ∈ C := by
    intro s
    have htop := spinMinus6_blocks_sup_eq_top_even hirr
    have hs : s ∈ (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range := by
      rw [htop]
      trivial
    have hle : (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range ≤ C.comap θ0 := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        show θ0 (minusLongBlock b c A) ∈ C
        have := congrArg (fun φ => φ A) hθlb
        simp only [MonoidHom.comp_apply] at this
        rw [this]
        exact hρC (n - 3) (by omega) A
      · rintro _ ⟨B, rfl⟩
        show θ0 (shortBlock hirr 3 finOne B) ∈ C
        have h1 : θ0 (shortBlock hirr 3 finOne B) ∈ Vg := by
          rw [← hθsb]
          exact ⟨B, rfl⟩
        have h2 : Vg ≤ C := by
          have hnV : ¬ (⟨n - 2, by omega⟩ : Fin (n - 1)).val + 2 < n := by
            show ¬ n - 2 + 2 < n
            omega
          have := hN ⟨n - 2, by omega⟩
          simpa only [hnodeG, if_neg hnV] using this
        exact h2 h1
    exact hle hs
  let θ' : spinGroup (quadMinus 3 F b c) →* ↥C := θ0.codRestrict C hθC
  have hθV : (shortBlock hirr 3 finOne).range.map θ' = U ⟨n - 2, by omega⟩ := by
    have hnV : ¬ (⟨n - 2, by omega⟩ : Fin (n - 1)).val + 2 < n := by
      show ¬ n - 2 + 2 < n
      omega
    rw [CompsPTwoDChain.map_codRestrict_eq_subgroupOf']
    simp only [hU, hnodeG, if_neg hnV]
    congr 1
    rw [← MonoidHom.range_comp]
    exact hθsb
  have hρ'₀ : ρ' ⟨n - 2 - 1, by omega⟩ = θ'.comp (minusLongBlock b c) := by
    have h3 : n - 2 - 1 = n - 3 := by omega
    ext A : 1
    refine Subtype.ext ?_
    have := congrArg (fun φ => φ A) hθlb
    simp only [MonoidHom.comp_apply] at this
    show ρ (n - 2 - 1) (Matrix.SpecialLinearGroup.map ιF A) = θ0 (minusLongBlock b c A)
    rw [this, h3]
  obtain ⟨Ψ, -, -, hq', hcen, hlie, -⟩ := CompsPTwoDFrameE.weakCT_spinMinus_even_of_frame hadm
    hn4 hF hirr U hgen hcommU θ' hθV ρ' hρ'₀ hρ'U hρ'ψ
  refine ⟨hlie, hq', fun z hz => ?_⟩
  rw [hcen] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [← map_pow, center_spinGroup_quadMinus_pow_four hn4 hirr x hx, map_one]


end Main

section Recog

variable (r : ℕ) [Fact r.Prime] (L : Type) [Field L] [CharP L r] [IsAlgClosed L]

@[expose] def TwoDChainRecogS (e m : ℕ) : Prop :=
  ∀ {G : Type} [Group G] (ρ : ℕ → SL(2, L) →* G) (Φ : SL(4, L) →* G) (C : Subgroup G),
    (∀ i, i < m → Function.Injective (ρ i)) →
    (∀ i j : ℕ, i < m → j < m → i ≠ j → ¬ CompsPTwoDChain.dEdge m i j →
      ¬ CompsPTwoDChain.dEdge m j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A) →
    (∀ i : ℕ, i + 3 < m → ∃ θ : SL(3, L) →* G,
      θ.comp (blockSL L 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = ρ (i + 1)) →
    Φ.comp (blockSL2 L 3 0) = ρ (m - 2) → Φ.comp (blockSL2 L 3 1) = ρ (m - 3) →
    Φ.comp (blockSL2 L 3 2) = ρ (m - 1) →
    (⨆ i : Fin (m - 1), if i.val + 2 < m then
        ((ρ i.val).comp (Matrix.SpecialLinearGroup.map
          ((frobeniusFixedField L r (e * 2)).subtype.comp (algebraMap
            ↥(frobeniusFixedField L r e) ↥(frobeniusFixedField L r (e * 2)))))).range
      else ((Φ.comp (Matrix.SpecialLinearGroup.map (frobeniusFixedField L r (e * 2)).subtype)).comp
        (usbSL (CompsPTwoDKlein.frobInvol (k := L) (p := r) e).toRingHom
          (fun x => CompsPTwoDKlein.frobHom_frobHom e x))).range) = C →
    DStrongModel C m r e


end Recog

section Instances


theorem twoDChainRecogS_odd {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r]
    [IsAlgClosed L] {e m : ℕ} (hr2 : r ≠ 2) (he : 0 < e) (hm4 : 4 ≤ m) (hq5 : 5 ≤ r ^ e) :
    TwoDChainRecogS r L e m := by
  classical
  intro G _ ρ Φ C hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC
  obtain ⟨bb, cc, hirr, ⟨KD⟩⟩ := CompsPTwoDKlein.exists_kleinData_frob (k := L) (p := r) he hr2
  haveI hFfin : Finite ↥(frobeniusFixedField L r e) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_frobeniusFixedField he]
      exact (pow_pos (Fact.out : r.Prime).pos _).ne')
  have hFcard : Nat.card ↥(frobeniusFixedField L r e) = r ^ e := card_frobeniusFixedField he
  have hq4 : 4 ≤ Nat.card ↥(frobeniusFixedField L r e) := by
    rw [hFcard]
    omega
  have hadm : StatedLieAdmissible .POmegaMinus m r e := ⟨Fact.out, he, hm4⟩
  exact strongModel_of_chain (k := L) (G := G) (n := m) (p := r) (f := e) hadm hr2 hFcard hq4 KD
    hirr (frobeniusFixedField L r (e * 2)).subtype ρ hρinj hcomm hfr Φ hΦ0 hΦ1 hΦ2 C hC

theorem twoDChainRecogS_even {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {e m : ℕ}
    (he : 0 < e) (hm4 : 4 ≤ m) : TwoDChainRecogS 2 L e m := by
  classical
  intro G _ ρ Φ C hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC
  obtain ⟨bb, cc, hirr, ⟨KD⟩⟩ :=
    CompsPTwoDKleinE.exists_kleinDataEven_frob (k := L) (p := 2) he
  haveI hFfin : Finite ↥(frobeniusFixedField L 2 e) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_frobeniusFixedField he]
      exact (pow_pos Nat.prime_two.pos _).ne')
  have hFcard : Nat.card ↥(frobeniusFixedField L 2 e) = 2 ^ e := card_frobeniusFixedField he
  have hadm : StatedLieAdmissible .POmegaMinus m 2 e := ⟨Nat.prime_two, he, hm4⟩
  exact strongModel_of_chain_even (k := L) (G := G) (n := m) (f := e) hadm hFcard KD
    hirr (frobeniusFixedField L 2 (e * 2)).subtype ρ hρinj hcomm hfr Φ hΦ0 hΦ1 hΦ2 C hC

@[expose] def TwoDChainRecogSAll (L : Type) [Field L] [IsAlgClosed L] (Q : ℕ → ℕ → Prop) : Prop :=
  ∀ (r : ℕ) [Fact r.Prime] [CharP L r] (e m : ℕ), 0 < e → 5 ≤ m → Q r (r ^ e) →
    TwoDChainRecogS r L e m

theorem twoDChainRecogSAll_even_or_five (L : Type) [Field L] [IsAlgClosed L] :
    TwoDChainRecogSAll L (fun r q => r = 2 ∨ 5 ≤ q) := by
  intro r hr hch e m he hm5 hq
  by_cases hr2 : r = 2
  · subst hr2
    exact twoDChainRecogS_even he (by omega)
  · exact twoDChainRecogS_odd hr2 he (by omega) (hq.resolve_left hr2)

end Instances

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
