module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieS6b
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieS6a
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndB

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.CatLeafProof.EndOddCore CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.CatFactsSp4 (diagSL coe_diagSL T2 mem_centralizer_T2_iff
  exists_conj_T2 kron_mul kron_neg_one_one)
open CFSG.LinearGroups (elementarySet special_linear_elementary_generation)
open scoped MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem transvection_pow_char {ℓ : ℕ} [CharP K ℓ] {m : ℕ} {i j : Fin m} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ^ ℓ = 1 := by
  have h : ∀ k : ℕ, SpecialLinearGroup.transvection hij c ^ k =
      SpecialLinearGroup.transvection hij (k • c) := by
    intro k
    induction k with
    | zero => rw [pow_zero, zero_smul, SpecialLinearGroup.transvection_coeff_zero]
    | succ k ih => rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
  rw [h, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem coe_neg_one_SL2 : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := rfl

variable (n : ℕ)

@[expose] def slBlkMat (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin (2 + n)) (Fin (2 + n)) K :=
  (fromBlocks g 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem slBlkMat_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    slBlkMat n g * slBlkMat n h = slBlkMat n (g * h) := by
  rw [slBlkMat, slBlkMat, slBlkMat, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem slBlkMat_one : slBlkMat n (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [slBlkMat, fromBlocks_one, submatrix_one_equiv]

theorem det_slBlkMat (g : Matrix (Fin 2) (Fin 2) K) : (slBlkMat n g).det = g.det := by
  rw [slBlkMat, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem slBlkMat_castAdd (g : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    slBlkMat n g (Fin.castAdd n i) (Fin.castAdd n j) = g i j := by
  simp [slBlkMat]

theorem slBlkMat_natAdd (g : Matrix (Fin 2) (Fin 2) K) (i : Fin n) :
    slBlkMat n g (Fin.natAdd 2 i) (Fin.natAdd 2 i) = 1 := by
  simp [slBlkMat]

@[expose] def slBlk : SL(2, K) →* SL(2 + n, K) where
  toFun g := ⟨slBlkMat n (g : Matrix (Fin 2) (Fin 2) K), by rw [det_slBlkMat, g.2]⟩
  map_one' := Subtype.ext (slBlkMat_one n)
  map_mul' g h := Subtype.ext (slBlkMat_mul n (g : Matrix (Fin 2) (Fin 2) K) h).symm

theorem coe_slBlk (g : SL(2, K)) :
    ((slBlk n g : SL(2 + n, K)) : Matrix (Fin (2 + n)) (Fin (2 + n)) K) =
      slBlkMat n (g : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] def sl2Blk (g₀ : StatedSp 2 K) : SL(2, K) →* StatedSp (2 + n) K :=
  (spBlk n).comp ((MulAut.conj g₀).toMonoidHom.comp (diagSL K))

theorem sl2Blk_apply (g₀ : StatedSp 2 K) (g : SL(2, K)) :
    sl2Blk n g₀ g = spBlk n (g₀ * diagSL K g * g₀⁻¹) := rfl

variable {n}

theorem false_of_config_sl2 [Finite K] (hK : ringChar K ≠ 2) {A : StatedSp r K}
    {F : Subgroup (StatedSp r K)} (hFT : F ≤ centralizer ({A} : Set (StatedSp r K)))
    (hFn : ∀ c ∈ centralizer ({A} : Set (StatedSp r K)), ∀ f ∈ F, c * f * c⁻¹ ∈ F)
    (hq : IsQuasisimple F) (φ : SL(2, K) →* StatedSp r K) (hφF : ∀ g, φ g ∈ F)
    (hφ : ∀ c : K, (((φ (-1) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ≠ c • 1)
    {L D : Subgroup (StatedProj (StatedSp r K))}
    (h : Config (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) A) L D) : False := by
  set Z := (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) with hZdef
  have hZ : Z ≤ center (StatedSp r K) := scalars_subgroupOf_le_center
  have hφZ : φ (-1) ∉ Z := by
    intro hm
    rw [hZdef, mem_subgroupOf] at hm
    obtain ⟨c, hc⟩ := hm
    apply hφ (c : K)
    rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  let ψ : SL(2, K) →* F.map (QuotientGroup.mk' Z) :=
    ((QuotientGroup.mk' Z).comp φ).codRestrict (F.map (QuotientGroup.mk' Z))
      (fun g => mem_map_of_mem _ (hφF g))
  have hψ1 : ψ (-1) ≠ 1 := by
    intro h1
    apply hφZ
    have h2 : QuotientGroup.mk' Z (φ (-1)) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨H, ⟨eH⟩⟩ := UnbalancedGS.SymplecticExclusion.exists_quaternion_of_sl2_hom hK ψ hψ1
  have hqF : IsQuasisimple (F.map (QuotientGroup.mk' Z)) := by
    have hr : ((QuotientGroup.mk' Z).comp F.subtype).range = F.map (QuotientGroup.mk' Z) := by
      rw [MonoidHom.range_comp, range_subtype]
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq
        ((QuotientGroup.mk' Z).comp F.subtype) with h0 | h0
    · exfalso
      apply hφZ
      have hm : QuotientGroup.mk' Z (φ (-1)) ∈ ((QuotientGroup.mk' Z).comp F.subtype).range :=
        ⟨⟨φ (-1), hφF _⟩, rfl⟩
      rw [h0, mem_bot] at hm
      exact (QuotientGroup.eq_one_iff _).1 hm
    · rwa [hr] at h0
  have heven : Even (Nat.card (F.map (QuotientGroup.mk' Z))) := by
    have h8 : Nat.card H = 8 := by
      rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hdvd : Nat.card H ∣ Nat.card (F.map (QuotientGroup.mk' Z)) :=
      Subgroup.card_subgroup_dvd_card H
    rw [h8] at hdvd
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) hdvd)
  have hcomp := isTwoComponentAt_map_mk hZ h.twoComp.1 hFT hFn hqF heven
  have hL := h.unique _ hcomp
  subst hL
  exact h.false_of_quat H eH

theorem false_of_config_skewSplit [Finite K] (hK : ringChar K ≠ 2) (hr : 3 ≤ r) {l : K}
    (hl0 : l ≠ 0) {A : StatedSp r K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      l • stdSkew r K)
    {L D : Subgroup (StatedProj (StatedSp r K))}
    (h : Config (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) A) L D) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨n, rfl⟩ : ∃ n, r = 2 + n := ⟨r - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  have hcent : centralizer ({A} : Set (StatedSp (2 + n) K)) =
      spCent (2 + n) K (stdSkewGsp (2 + n) K) := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent, coe_stdSkewGsp]
    constructor
    · intro hg
      have := congrArg (fun u : StatedSp (2 + n) K => ((u : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
        Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K)) hg
      simp only [Subgroup.coe_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.smul_mul] at this
      exact (smul_right_injective _ hl0 this).symm
    · intro hg
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul, hA, Matrix.mul_smul, Matrix.smul_mul, hg]
  refine false_of_config_sl2 hK (F := (leviSL (2 + n) K).range) ?_ ?_
    (isQuasisimple_leviSL_range (by omega) (Or.inl (by omega)))
    ((leviSL (2 + n) K).comp (slBlk n)) (fun g => ⟨slBlk n g, rfl⟩) ?_ h
  · rintro _ ⟨g, rfl⟩
    rw [hcent]
    exact leviSL_mem_spCent g
  · intro c hc f hf
    rw [hcent] at hc
    exact conj_mem_leviSL_range h2 hc hf
  · intro c hc
    have e1 := congrFun (congrFun hc (Sum.inl (Fin.castAdd n 0))) (Sum.inl (Fin.castAdd n 0))
    have e2 := congrFun (congrFun hc (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩)))
      (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩))
    rw [MonoidHom.comp_apply, coe_leviSL, fromBlocks_apply₁₁, coe_slBlk] at e1 e2
    rw [slBlkMat_castAdd, coe_neg_one_SL2] at e1
    rw [slBlkMat_natAdd] at e2
    simp only [Matrix.neg_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
      mul_one] at e1 e2
    exact h2 (by linear_combination e2 - e1)

theorem false_of_config_skewNs [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) (hd : ∀ l : K, l ^ 2 ≠ -1) {A : StatedSp r K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      skewNs r K (-1))
    {L D : Subgroup (StatedProj (StatedSp r K))}
    (h : Config (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedSp r K)) A) L D) : False := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd0 : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨n, rfl⟩ : ∃ n, r = 2 + n := ⟨r - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  set Ag : gsp (2 + n) K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  have hAgm : ((Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
      Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) =
      skewNs (2 + n) K (-1) := hA
  have hAns : ∀ c : Kˣ, (Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) ≠
      GeneralLinearGroup.scalar (Fin (2 + n) ⊕ Fin (2 + n)) c := by
    intro c hc
    apply skewNsGsp_ne_scalar (r := 2 + n) (by omega) hd0 c
    rw [← hc]
    exact Units.ext (by rw [coe_skewNsGsp, hAgm])
  have hAA : ((Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
      Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) *
      ((Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
        Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) = (-1 : K) • 1 := by
    rw [hAgm, skewNs_mul_self]
  have hJ : ((Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
      Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K)ᵀ * formJ (2 + n) K *
      ((Ag : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
        Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K) =
      (-(-1 : K)) • formJ (2 + n) K := by
    rw [hAgm, skewNs_similitude]
  have hcent : centralizer ({A} : Set (StatedSp (2 + n) K)) = spCent (2 + n) K Ag := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_spCent]
    constructor
    · intro hg
      have := congrArg (fun u : StatedSp (2 + n) K => ((u : GL (Fin (2 + n) ⊕ Fin (2 + n)) K) :
        Matrix (Fin (2 + n) ⊕ Fin (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) K)) hg
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      exact this.symm
    · intro hg
      apply statedSp_ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      exact hg.symm
  obtain ⟨L', hL'C, hL'n, hL'q, hL'ℓ⟩ := exists_unitary_component hℓ hℓ2 hf hKc (by omega)
    (Or.inl (by omega)) hAns hd hAA hJ
  set T : StatedSp 2 K := ⟨(skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K), mem_statedSp_iff.2 (by
    rw [coe_skewNsGsp, skewNs_similitude, neg_neg, one_smul])⟩ with hT
  have hTm : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      skewNs 2 K (-1) := rfl
  obtain ⟨g₀, hg₀⟩ := exists_conj_T2 h2 T (by rw [hTm, skewNs_mul_self, neg_one_smul])
  have key : ∀ x : StatedSp 2 K, x * T = T * x → spBlk n x ∈ spCent (2 + n) K Ag := by
    intro x hx
    have hm := congrArg (fun u : StatedSp 2 K =>
      ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hx
    simp only [Subgroup.coe_mul, Units.val_mul] at hm
    rw [hTm] at hm
    rw [mem_spCent, hAgm, skewNs_eq_blk]
    exact (spBlk_commute hm _).symm
  have hφC : ∀ g, sl2Blk n g₀ g ∈ spCent (2 + n) K Ag := by
    intro g
    rw [sl2Blk_apply]
    apply key
    have hTc : T = g₀ * T2 K * g₀⁻¹ := by rw [← hg₀]; group
    have hdT : diagSL K g * T2 K = T2 K * diagSL K g :=
      mem_centralizer_singleton_iff.1 (mem_centralizer_T2_iff.2 (by
        simp only [coe_diagSL, kron_mul, Matrix.mul_one, Matrix.one_mul]))
    rw [hTc]
    calc g₀ * diagSL K g * g₀⁻¹ * (g₀ * T2 K * g₀⁻¹) = g₀ * (diagSL K g * T2 K) * g₀⁻¹ := by
          group
      _ = g₀ * (T2 K * diagSL K g) * g₀⁻¹ := by rw [hdT]
      _ = g₀ * T2 K * g₀⁻¹ * (g₀ * diagSL K g * g₀⁻¹) := by group
  have hφL : ∀ g, sl2Blk n g₀ g ∈ L' := by
    have hle : Subgroup.closure (elementarySet 2 K) ≤ L'.comap (sl2Blk n g₀) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      exact hL'ℓ _ (hφC _) (by rw [← map_pow, transvection_pow_char hij c, map_one])
    intro g
    exact hle (by rw [special_linear_elementary_generation]; exact mem_top g)
  have hneg : (((g₀ * diagSL K (-1) * g₀⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
    have hd1 : (((diagSL K (-1) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
      rw [coe_diagSL, coe_neg_one_SL2, kron_neg_one_one]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd1, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one]
  refine false_of_config_sl2 hK (F := L') (by rw [hcent]; exact hL'C) (by rw [hcent]; exact hL'n)
    hL'q (sl2Blk n g₀) hφL (fun c => ?_) h
  rw [sl2Blk_apply, coe_spBlk, hneg]
  exact blk_neg_one_ne_smul h2 hn c

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
