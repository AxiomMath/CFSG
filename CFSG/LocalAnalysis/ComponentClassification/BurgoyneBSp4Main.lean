module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.PSL (eq_bot_of_oddCoreIn conj_embedding
  conj_range_normal)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem stdSkew_twin_hyps (hK : ringChar K ≠ 2) (h4 : 4 ≤ Nat.card K)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B) :
    (∀ i : Fin 2, BlockDiag (lrPair i) ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
    (∀ i : Fin 2, ¬ PairScalar i ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
    ∀ y ∈ oddCoreIn B (conjAut 2 K (stdSkewGsp 2 K)), ∃ D : gsp 2 K, y = conjAut 2 K D ∧
      (∀ i : Fin 2, BlockDiag (lrPair i)
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
      ∀ i : Fin 2, PairScalar i
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
        conjAut 2 K D = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine ⟨fun i => by rw [coe_stdSkewGsp]; exact blockDiag_diagonal _ _, fun i h => ?_,
    fun y hy => ?_⟩
  · obtain ⟨-, -, h3⟩ := h
    simp only [coe_stdSkewGsp, stdSkew, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at h3
    exact h2 (by linear_combination h3)
  · obtain ⟨D, a, b, rfl, hD⟩ := skewSplit_oddCore hK le_rfl (Or.inr h4) hinj hB hy
    refine ⟨D, rfl, fun i => by rw [hD]; exact blockDiag_diagonal _ _, fun i hs => ?_⟩
    obtain ⟨-, -, h3⟩ := hs
    simp only [hD, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at h3
    subst h3
    refine conjAut_eq_one_of_eq_smul (by omega) (p := a) ?_
    rw [hD, Matrix.smul_one_eq_diagonal]
    congr 1
    ext x
    cases x <;> rfl

theorem skewNs_twin_hyps {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (h5 : 5 ≤ ℓ ^ f)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) :
    (∀ i : Fin 2, BlockDiag (lrPair i) ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
    (∀ i : Fin 2, ¬ PairScalar i ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
    ∀ y ∈ oddCoreIn B (conjAut 2 K (skewNsGsp 2 K hd0)), ∃ D : gsp 2 K, y = conjAut 2 K D ∧
      (∀ i : Fin 2, BlockDiag (lrPair i)
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
      ∀ i : Fin 2, PairScalar i
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
        conjAut 2 K D = 1 := by
  have hA₁ : ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (0 : K) • 1 + (1 : K) • skewNs 2 K d := by
    rw [coe_skewNsGsp, zero_smul, one_smul, zero_add]
  refine ⟨fun i => by rw [hA₁]; exact blockDiag_add_smul_skewNs _ _ _ _, fun i h => ?_,
    fun y hy => ?_⟩
  · obtain ⟨-, h10, -⟩ := h
    rw [coe_skewNsGsp, skewNs_apply_inr_inl] at h10
    exact one_ne_zero h10
  · obtain ⟨D, p, s, rfl, hD⟩ := skewNs_oddCore hℓ hℓ2 hf hKc le_rfl (Or.inr h5) hinj hB hd hd0 hy
    refine ⟨D, rfl, fun i => by rw [hD]; exact blockDiag_add_smul_skewNs _ _ _ _, fun i hs => ?_⟩
    obtain ⟨-, h10, -⟩ := hs
    have hs0 : s = 0 := by
      rw [hD] at h10
      simpa [skewNs, one_apply] using h10
    refine conjAut_eq_one_of_eq_smul (by omega) (p := p) ?_
    rw [hD, hs0, zero_smul, add_zero]

theorem exists_conj_transfer' {r : ℕ} (hr : 1 ≤ r) {X : Type} [Group X]
    {ψ : X →* MulAut (StatedProj (StatedSp r K))} (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} {A A' : gsp r K} (htA : ψ t = conjAut r K A) (H : StatedSp r K) {c : K} (hc : c ≠ 0)
    (hH : ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        c • ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    ∃ ψ' : X →* MulAut (StatedProj (StatedSp r K)), Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
        ψ'.range ∧ ψ' t = conjAut r K A' ∧
      ∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
          MulAut (StatedProj (StatedSp r K))).range ↔
        ψ x ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
          MulAut (StatedProj (StatedSp r K))).range := by
  set Hg : gsp r K := ⟨H, statedSp_le_gsp H.2⟩ with hHg
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut r K Hg⁻¹)
  have hN : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range.Normal := conj_range_normal
  refine ⟨_, hinj', hInn', ?_, fun x => ?_⟩
  · change conjAut r K Hg⁻¹ * ψ t * (conjAut r K Hg⁻¹)⁻¹ = _
    rw [htA, ← map_inv, inv_inv, ← map_mul, ← map_mul]
    refine conjAut_eq_of_eq_smul hr hc ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hH
  · change conjAut r K Hg⁻¹ * ψ x * (conjAut r K Hg⁻¹)⁻¹ ∈ _ ↔ _
    constructor
    · intro h
      have := hN.conj_mem _ h (conjAut r K Hg⁻¹)⁻¹
      rwa [inv_inv, show (conjAut r K Hg⁻¹)⁻¹ * (conjAut r K Hg⁻¹ * ψ x * (conjAut r K Hg⁻¹)⁻¹) *
        conjAut r K Hg⁻¹ = ψ x by group] at this
    · intro h
      exact hN.conj_mem _ h _

theorem sp4_twin_X {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp 2 K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) :
    5 ≤ Nat.card K ∧ ∃ ψ' : X →* MulAut (StatedProj (StatedSp 2 K)), Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
        ψ'.range ∧
      (∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
          MulAut (StatedProj (StatedSp 2 K))).range ↔
        ψ x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
          MulAut (StatedProj (StatedSp 2 K))).range) ∧
      ∀ i : Fin 2, ActsProperly (ψ' t) (Y.map ψ') (slice (longRoot K i)) ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero (2 : ℕ) := ⟨by omega⟩
  have : Nontrivial (Fin 2 ⊕ Fin 2 → K) := by
    have : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
    infer_instance
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq5 : ℓ ^ f ≠ 3 → 5 ≤ ℓ ^ f := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hgood : ∀ {A' : gsp 2 K} (ψ' : X →* MulAut (StatedProj (StatedSp 2 K))),
      Function.Injective ψ' →
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
        ψ'.range → ψ' t = conjAut 2 K A' →
      (∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
          MulAut (StatedProj (StatedSp 2 K))).range ↔
        ψ x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range)
      → 5 ≤ ℓ ^ f →
      (∀ {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))},
        (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
          B →
        (∀ i : Fin 2, BlockDiag (lrPair i) ((A' : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
        (∀ i : Fin 2, ¬ PairScalar i ((A' : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
        ∀ y ∈ oddCoreIn B (conjAut 2 K A'), ∃ D : gsp 2 K, y = conjAut 2 K D ∧
          (∀ i : Fin 2, BlockDiag (lrPair i)
            ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
          ∀ i : Fin 2, PairScalar i
            ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
            conjAut 2 K D = 1) →
      5 ≤ Nat.card K ∧ ∃ ψ' : X →* MulAut (StatedProj (StatedSp 2 K)), Function.Injective ψ' ∧
        (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
          ψ'.range ∧
        (∀ x, ψ' x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
            MulAut (StatedProj (StatedSp 2 K))).range ↔
          ψ x ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
            MulAut (StatedProj (StatedSp 2 K))).range) ∧
        ∀ i : Fin 2, ActsProperly (ψ' t) (Y.map ψ') (slice (longRoot K i)) ⊥ := by
    intro A' ψ' hinj' hInn' hψ't hpre h5 hhyps
    obtain ⟨hAb, hAn, hcore⟩ := hhyps hInn'
    refine ⟨by rw [hKc]; exact h5, ψ', hinj', hInn', hpre, fun i => ?_⟩
    have hY' : Y.map ψ' ≠ ⊥ := fun h => hY ((map_eq_bot_iff_of_injective _ hinj').1 h)
    have hYO' : Y.map ψ' ≤ oddCoreIn ψ'.range (ψ' t) := by
      rw [← map_oddCentralizerCore_of_injective hinj']
      exact map_mono hYO
    rw [hψ't] at hYO' ⊢
    have hAt : orderOf (conjAut 2 K A') = 2 := by
      rw [← hψ't, orderOf_injective _ hinj']
      exact ht
    exact sp4_actsProperly hinj hAt hAb hAn hcore hY' hYO' i
  obtain ⟨A, τ, hα⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK le_rfl (ψ t)
  by_cases hτ : τ = 1
  swap
  · exact absurd (field_eq_bot hℓ hℓ2 hf hKc le_rfl hinj hψ hInn ht hτ hα hYO) hY
  subst hτ
  rw [map_one, mul_one] at hα
  set M := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin 2 ⊕ Fin 2) K) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    intro c hc
    have h1 : conjAut 2 K A = 1 := (conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩
    have ht1 : t = 1 := hψ (by rw [hα, h1, map_one])
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have htt : ψ t * ψ t = 1 := by
    rw [← map_mul, ← pow_two, ht2, map_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) (A * A)).1 (by rw [map_mul, ← hα, htt])
  set d : K := (c : K) with hd
  have hd0 : d ≠ 0 := c.ne_zero
  have hAA : M * M = d • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  set μ : K := (multiplier 2 K A : K) with hμ
  have hJμ : Mᵀ * formJ 2 K * M = μ • formJ 2 K := multiplier_spec A
  have hAμ : ∀ v w, pairedSympForm K 2 (((linA A : LinearMap.GeneralLinearGroup K
      (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
        Module.End K (Fin 2 ⊕ Fin 2 → K)) w) = μ * pairedSympForm K 2 v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJμ]
  have hratio := UnitaryHigher.multiplier_ratio SymplecticFlag.pairedSympForm_nondegenerate hd0
    (linA_mul_self hAA) hAμ
  have hμd : μ = d ∨ μ = -d := by
    rcases hratio with h | h
    · left
      field_simp at h
      exact h
    · right
      field_simp at h
      linear_combination h
  have hbot : oddCoreIn ψ.range (conjAut 2 K A) = ⊥ → False := fun h =>
    hY (eq_bot_of_oddCoreIn hψ (by rw [hα]; exact h) hYO)
  have hbot' : ∀ {ψ' : X →* MulAut (StatedProj (StatedSp 2 K))}, Function.Injective ψ' →
      oddCoreIn ψ'.range (ψ' t) = ⊥ → False := fun hinj' h =>
    hY (eq_bot_of_oddCoreIn hinj' h hYO)
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hd0 (by rw [← hl]; ring)
    have hAA' : M * M = (l ^ 2) • 1 := by rw [hl]; exact hAA
    rcases hμd with hμd | hμd
    ·
      exfalso
      have hJ' : Mᵀ * formJ 2 K * M = (l ^ 2) • formJ 2 K := by rw [hl, ← hμd]; exact hJμ
      by_cases hP : Module.finrank K (VPl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form (A := negGsp A) (l := l) hK
          (by omega) hl0 (by rw [coe_negGsp, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hAA')
          (by rw [coe_negGsp, transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg,
            neg_neg]; exact hJ')
          (by rw [VMl_negGsp A hl0]; exact hP.1)
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn hα H
          (neg_ne_zero.2 hl0) (A' := lrInvGsp 2 K ⟨0, by omega⟩)
          (by rw [neg_smul, ← hH, coe_negGsp, Matrix.mul_neg, Matrix.neg_mul, neg_neg])
        refine hbot' hinj' ?_
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hP.2 le_rfl hinj hInn' _
      by_cases hM2 : Module.finrank K (VMl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form hK (by omega) hl0 hAA' hJ' hM2.1
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn hα H hl0 hH
        refine hbot' hinj' ?_
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hM2.2 le_rfl hinj hInn' _
      refine hbot (splitSelf_oddCoreIn_eq_bot hK le_rfl hinj hInn hAns hl0 hAA' hJ' ?_ ?_)
      · by_contra h
        push Not at h
        exact hP h
      · by_contra h
        push Not at h
        exact hM2 h
    ·
      have hJ' : Mᵀ * formJ 2 K * M = (-(l ^ 2)) • formJ 2 K := by rw [hl, ← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA' hJ'
      obtain ⟨ψ', hinj', hInn', hψ't, hpre⟩ := exists_conj_transfer' (by omega) hψ hInn hα H hl0
        (A' := stdSkewGsp 2 K) hH
      by_cases h3 : Nat.card K = 3
      · exfalso
        refine hbot' hinj' ?_
        rw [hψ't]
        exact skewSplit_oddCoreIn_eq_bot_two_three h3 hInn'
      · have h5 : 5 ≤ ℓ ^ f := hq5 (by rwa [← hKc])
        exact hgood ψ' hinj' hInn' hψ't hpre h5 fun hB =>
          stdSkew_twin_hyps hK (by rw [hKc]; omega) hinj hB
  · push Not at hsq
    rcases hμd with hμd | hμd
    ·
      exfalso
      have hJ' : Mᵀ * formJ 2 K * M = d • formJ 2 K := by rw [← hμd]; exact hJμ
      exact hbot (nonsplitSelf_oddCoreIn_eq_bot hℓ hℓ2 hf hKc le_rfl hinj hInn hAns hsq hAA hJ')
    ·
      have hJ' : Mᵀ * formJ 2 K * M = (-d) • formJ 2 K := by rw [← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) hAns hsq hAA hJ'
      obtain ⟨ψ', hinj', hInn', hψ't, hpre⟩ := exists_conj_transfer' (by omega) hψ hInn hα H
        one_ne_zero (A' := skewNsGsp 2 K hd0) (by rw [one_smul, coe_skewNsGsp]; exact hH)
      by_cases h3 : Nat.card K = 3
      · exfalso
        refine hbot' hinj' ?_
        rw [hψ't]
        exact skewNs_oddCoreIn_eq_bot_two_three h3 hInn' hsq hd0
      · have h5 : 5 ≤ ℓ ^ f := hq5 (by rwa [← hKc])
        exact hgood ψ' hinj' hInn' hψ't hpre h5 fun hB =>
          skewNs_twin_hyps hℓ hℓ2 hf hKc h5 hinj hB hsq hd0

end CFSG.ComponentClassification.Burgoyne.B
