module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpInner
public import Mathlib.Algebra.QuadraticAlgebra.Basic
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.Sp

namespace Psp

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
@[expose] def diagGsp (u : Kˣ) : gsp r K :=
  ⟨⟨diagonal (Sum.elim (fun _ => (u : K)) fun _ => 1),
    diagonal (Sum.elim (fun _ => ((u⁻¹ : Kˣ) : K)) fun _ => 1),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      rcases x with x | x <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext x
      rcases x with x | x <;> simp⟩,
    ⟨u, by
      ext x y
      rcases x with i | i <;> rcases y with j | j <;>
        simp [formJ, diagonal_apply, Matrix.mul_apply, Matrix.fromBlocks, Matrix.one_apply]⟩⟩

theorem coe_diagGsp (u : Kˣ) :
    ((diagGsp r K u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      diagonal (Sum.elim (fun _ => (u : K)) fun _ => 1) := rfl

variable (r K) in
@[expose] def diagHom : Kˣ →* gsp r K where
  toFun := diagGsp r K
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_diagGsp]
    ext x y
    rcases x with i | i <;> rcases y with j | j <;> simp [diagonal_apply, one_apply]
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    change _ = (((diagGsp r K u : GL (Fin r ⊕ Fin r) K) * (diagGsp r K v : GL (Fin r ⊕ Fin r) K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    rw [Units.val_mul, coe_diagGsp, coe_diagGsp, coe_diagGsp, diagonal_mul_diagonal]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem diagHom_apply (u : Kˣ) : diagHom r K u = diagGsp r K u := rfl

theorem conjAut_mem_range_diagHom [Finite K] (hr : 1 ≤ r) {D : gsp r K} {a b : K}
    (hD : ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      diagonal (Sum.elim (fun _ => a) fun _ => b)) :
    conjAut r K D ∈ ((conjAut r K).comp (diagHom r K)).range := by
  have hne : ∀ x : Fin r ⊕ Fin r, Sum.elim (fun _ => a) (fun _ => b) x ≠ 0 := by
    intro x h0
    have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K)) x) x
    rw [hD, diagonal_mul, h0, zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  have ha : a ≠ 0 := hne (Sum.inl ⟨0, hr⟩)
  have hb : b ≠ 0 := hne (Sum.inr ⟨0, hr⟩)
  refine ⟨Units.mk0 (a / b) (div_ne_zero ha hb), ?_⟩
  rw [MonoidHom.comp_apply]
  refine conjAut_eq_of_eq_smul hr (inv_ne_zero hb) ?_
  rw [diagHom_apply, coe_diagGsp, hD, Units.val_mk0]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [diagonal_apply, hb, div_eq_inv_mul]

theorem skewNs_transpose_mul_formJ (d : K) :
    (skewNs r K d)ᵀ * formJ r K = -(formJ r K * skewNs r K d) := by
  rw [skewNs, fromBlocks_transpose, formJ, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, transpose_smul, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, fromBlocks_neg, neg_zero, neg_neg]

theorem add_smul_skewNs_similitude (d p s : K) :
    (p • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + s • skewNs r K d)ᵀ * formJ r K *
        (p • 1 + s • skewNs r K d) = (p * p - d * s * s) • formJ r K := by
  have h1 := skewNs_transpose_mul_formJ (r := r) d
  have h2 := skewNs_similitude (r := r) d
  have e : (p • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + s • skewNs r K d)ᵀ * formJ r K *
      (p • 1 + s • skewNs r K d) = (p * p) • formJ r K +
        (p * s) • ((skewNs r K d)ᵀ * formJ r K + formJ r K * skewNs r K d) +
        (s * s) • ((skewNs r K d)ᵀ * formJ r K * skewNs r K d) := by
    rw [transpose_add, transpose_smul, transpose_smul, transpose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul]
    module
  rw [e, h2, h1, neg_add_cancel, smul_zero, add_zero, smul_smul, ← add_smul]
  congr 1
  ring

variable (r) in
@[expose] def skewNsLift (d : K) :
    QuadraticAlgebra K d 0 →ₐ[K] Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  QuadraticAlgebra.lift ⟨skewNs r K d, by rw [skewNs_mul_self, zero_smul, add_zero]⟩

theorem skewNsLift_apply (d : K) (z : QuadraticAlgebra K d 0) :
    skewNsLift r d z = z.re • 1 + z.im • skewNs r K d := by
  simp [skewNsLift]

variable (r) in
@[expose] def skewNsHom (d : K) : (QuadraticAlgebra K d 0)ˣ →* gsp r K where
  toFun z := ⟨Units.map (skewNsLift r d : QuadraticAlgebra K d 0 →* _) z,
    ⟨(QuadraticAlgebra.isUnit_iff_norm_isUnit.1 z.isUnit).unit, by
      rw [IsUnit.unit_spec, QuadraticAlgebra.norm_def]
      change (skewNsLift r d (z : QuadraticAlgebra K d 0))ᵀ * formJ r K *
        (skewNsLift r d (z : QuadraticAlgebra K d 0)) = _
      rw [skewNsLift_apply, add_smul_skewNs_similitude]
      congr 1
      ring⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul _ z w

theorem coe_skewNsHom (d : K) (z : (QuadraticAlgebra K d 0)ˣ) :
    ((skewNsHom r d z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (z : QuadraticAlgebra K d 0).re • 1 + (z : QuadraticAlgebra K d 0).im • skewNs r K d :=
  skewNsLift_apply d _

theorem conjAut_mem_range_skewNsHom [Finite K] (hr : 1 ≤ r) {d : K} (hsq : ∀ l : K, l ^ 2 ≠ d)
    {D : gsp r K} {p s : K}
    (hD : ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      p • 1 + s • skewNs r K d) :
    conjAut r K D ∈ ((conjAut r K).comp (skewNsHom r d)).range := by
  have : Fact (∀ l : K, l ^ 2 ≠ d + 0 * l) := ⟨fun l h => hsq l (by simpa using h)⟩
  have hz : (⟨p, s⟩ : QuadraticAlgebra K d 0) ≠ 0 := by
    intro h0
    have hp : p = 0 := congrArg QuadraticAlgebra.re h0
    have hs : s = 0 := congrArg QuadraticAlgebra.im h0
    have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K))
      (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    rw [hD, hp, hs, zero_smul, zero_smul, add_zero, Matrix.zero_mul, one_apply_eq] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 _ hz, ?_⟩
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_skewNsHom, hD]
  rfl

theorem isCyclic_units_quadraticAlgebra [Finite K] {d : K} (hsq : ∀ l : K, l ^ 2 ≠ d) :
    IsCyclic (QuadraticAlgebra K d 0)ˣ := by
  have : Fact (∀ l : K, l ^ 2 ≠ d + 0 * l) := ⟨fun l h => hsq l (by simpa using h)⟩
  have : Finite (QuadraticAlgebra K d 0) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd d 0).symm
  infer_instance

theorem isCyclic_oddCentralizerCore_of_le_range {X G C : Type} [Group X] [Group G] [Group C]
    [Finite X] [IsCyclic C] {ψ : X →* G} (hψ : Function.Injective ψ) {t : X} (γ : C →* G)
    (h : oddCoreIn ψ.range (ψ t) ≤ γ.range) : IsCyclic ↥(oddCentralizerCore t) := by
  have h1 : (oddCentralizerCore t).map ψ = oddCoreIn ψ.range (ψ t) :=
    map_oddCentralizerCore_of_injective hψ t
  have h2 : IsCyclic ↥((oddCentralizerCore t).map ψ) := by
    rw [h1]
    exact isCyclic_of_le_range γ h
  exact isCyclic_of_surjective ((oddCentralizerCore t).equivMapOfInjective ψ hψ).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem isCyclic_oddCentralizerCore_of_eq_bot {X G : Type} [Group X] [Group G] [Finite X]
    {ψ : X →* G} (hψ : Function.Injective ψ) {t : X} (h : oddCoreIn ψ.range (ψ t) = ⊥) :
    IsCyclic ↥(oddCentralizerCore t) := by
  have : oddCentralizerCore t = ⊥ := eq_bot_of_oddCoreIn hψ h le_rfl
  rw [this]
  infer_instance

theorem isCyclic_oddCentralizerCore_inner [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp r K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : gsp r K} (htA : ψ t = conjAut r K A) :
    IsCyclic ↥(oddCentralizerCore t) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq5 : ℓ ^ f ≠ 3 → 5 ≤ ℓ ^ f := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    omega
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : conjAut r K A = 1 := (conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩
    have ht1 : t = 1 := hψ (by rw [htA, h1, map_one])
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htt : ψ t * ψ t = 1 := by
    rw [← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) (A * A)).1 (by rw [map_mul, ← htA, htt])
  set d : K := (c : K) with hd
  have hd0 : d ≠ 0 := c.ne_zero
  have hAA : M * M = d • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  set μ : K := (multiplier r K A : K) with hμ
  have hJμ : Mᵀ * formJ r K * M = μ • formJ r K := multiplier_spec A
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = μ * pairedSympForm K r v w := by
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
  have hbot : oddCoreIn ψ.range (conjAut r K A) = ⊥ → IsCyclic ↥(oddCentralizerCore t) :=
    fun h => isCyclic_oddCentralizerCore_of_eq_bot hψ (by rw [htA]; exact h)
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hd0 (by rw [← hl]; ring)
    have hAA' : M * M = (l ^ 2) • 1 := by rw [hl]; exact hAA
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = (l ^ 2) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      by_cases hP : Module.finrank K (VPl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form (A := negGsp A) (l := l) hK
          (by omega) hl0 (by rw [coe_negGsp, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hAA')
          (by rw [coe_negGsp, transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg,
            neg_neg]; exact hJ')
          (by rw [VMl_negGsp A hl0]; exact hP.1)
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H
          (neg_ne_zero.2 hl0) (A' := lrInvGsp r K ⟨0, by omega⟩)
          (by rw [neg_smul, ← hH, coe_negGsp, Matrix.mul_neg, Matrix.neg_mul, neg_neg])
        refine isCyclic_oddCentralizerCore_of_eq_bot hinj' ?_
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hP.2 hr hinj hInn' _
      by_cases hM2 : Module.finrank K (VMl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form hK (by omega) hl0 hAA' hJ' hM2.1
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H hl0 hH
        refine isCyclic_oddCentralizerCore_of_eq_bot hinj' ?_
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hM2.2 hr hinj hInn' _
      refine hbot (splitSelf_oddCoreIn_eq_bot hK hr hinj hInn hAns hl0 hAA' hJ' ?_ ?_)
      · by_contra h
        push Not at h
        exact hP h
      · by_contra h
        push Not at h
        exact hM2 h
    ·
      have hJ' : Mᵀ * formJ r K * M = (-(l ^ 2)) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA' hJ'
      obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H hl0
        (A' := stdSkewGsp r K) hH
      by_cases h3 : Nat.card K = 3
      · refine isCyclic_oddCentralizerCore_of_eq_bot hinj' ?_
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewSplit_oddCoreIn_eq_bot_two_three h3 hInn'
        · exact skewSplit_oddCoreIn_eq_bot_three h3 hr3 hinj hInn'
      · have h4 : 4 ≤ Nat.card K := by have := hq5 (by rwa [← hKc]); omega
        refine isCyclic_oddCentralizerCore_of_le_range hinj' ((conjAut r K).comp (diagHom r K)) ?_
        rw [hψ't]
        intro y hy
        obtain ⟨D, a, b, rfl, hD⟩ := skewSplit_oddCore hK hr (Or.inr h4) hinj hInn' hy
        exact conjAut_mem_range_diagHom (by omega) hD
  · push Not at hsq
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = d • formJ r K := by rw [← hμd]; exact hJμ
      exact hbot (nonsplitSelf_oddCoreIn_eq_bot hℓ hℓ2 hf hKc hr hinj hInn hAns hsq hAA hJ')
    ·
      have hJ' : Mᵀ * formJ r K * M = (-d) • formJ r K := by rw [← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) hAns hsq hAA hJ'
      obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H one_ne_zero
        (A' := skewNsGsp r K hd0) (by rw [one_smul, coe_skewNsGsp]; exact hH)
      by_cases h3 : Nat.card K = 3
      · refine isCyclic_oddCentralizerCore_of_eq_bot hinj' ?_
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewNs_oddCoreIn_eq_bot_two_three h3 hInn' hsq hd0
        · exact skewNs_oddCoreIn_eq_bot_three h3 hr3 hinj hInn' hsq hd0
      · have := isCyclic_units_quadraticAlgebra hsq
        refine isCyclic_oddCentralizerCore_of_le_range hinj'
          ((conjAut r K).comp (skewNsHom r d)) ?_
        rw [hψ't]
        intro y hy
        obtain ⟨D, p, s, rfl, hD⟩ := skewNs_oddCore hℓ hℓ2 hf hKc hr
          (Or.inr (hq5 (by rwa [← hKc]))) hinj hInn' hsq hd0 hy
        exact conjAut_mem_range_skewNsHom (by omega) hsq hD

theorem conj_injective_psp [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r) :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ Nat.card K := by
    have := hp.two_le
    have : 3 ≤ p := by omega
    rw [hKc]
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hcase : Nat.card K = 3 ∨ 4 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have : Fintype K := Fintype.ofFinite K
  have hsimple : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega)
      (by
        rcases hcase with h | h
        · exact Or.inr (Or.inl ⟨h, hr⟩)
        · exact Or.inl (Or.inr h))
  have hperf : Group.IsPerfect (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K (by
      rcases hcase with h | h
      · exact Or.inr (Or.inl ⟨h, hr⟩)
      · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
          (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
        exact Or.inl ⟨s, hs⟩)
  have hcenter : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp r K))) with h | h
    · exact h
    · exfalso
      have hcomm : ⁅(⊤ : Subgroup (StatedProj (StatedSp r K))), ⊤⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ y _ =>
          Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
      have htop : ⁅(⊤ : Subgroup (StatedProj (StatedSp r K))), ⊤⁆ = ⊤ :=
        hperf.commutator_eq_top
      obtain ⟨a, ha⟩ := exists_ne (1 : StatedProj (StatedSp r K))
      have hmem : a ∈ ⁅(⊤ : Subgroup (StatedProj (StatedSp r K))), ⊤⁆ := htop ▸ Subgroup.mem_top a
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact ha hmem
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcomm : ∀ y : StatedProj (StatedSp r K), x * y = y * x := by
    intro y
    have := congrArg (fun α : MulAut (StatedProj (StatedSp r K)) => α y) (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hz : x ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
    Subgroup.mem_center_iff.mpr fun y => (hcomm y).symm
  rw [hcenter, Subgroup.mem_bot] at hz
  exact hz

end Psp

open Psp

variable {r : ℕ} {K : Type} [Field K]

theorem isCyclic_oddCentralizerCore_psp [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp r K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) : IsCyclic ↥(oddCentralizerCore t) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨A, τ, hα⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard hK hr
      (ψ t)
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hα
    exact isCyclic_oddCentralizerCore_inner hp hp2 hf hKc hr hinj hψ hInn ht hα
  · have h := field_eq_bot hp hp2 hf hKc hr hinj hψ hInn ht hτ hα (le_refl (oddCentralizerCore t))
    rw [h]
    infer_instance

theorem oddCoreCyclic_psp {K : Type} [Field K] [Finite K] {p f r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hKc : Nat.card K = p ^ f) (hr : 2 ≤ r) :
    OddCoreCyclic (StatedProj (StatedSp r K)) := by
  intro B hB t htB ht
  have hinj := conj_injective_psp (r := r) hp hp2 hf hKc hr
  have hord : orderOf (⟨t, htB⟩ : ↥B) = 2 := by
    exact (orderOf_injective B.subtype Subtype.val_injective ⟨t, htB⟩).symm.trans ht
  have hcyc := isCyclic_oddCentralizerCore_psp hp hp2 hf hKc hr hinj (X := ↥B)
    (ψ := B.subtype) Subtype.val_injective (by rw [Subgroup.range_subtype]; exact hB) hord
  have h1 : (oddCentralizerCore (⟨t, htB⟩ : ↥B)).map B.subtype = oddCoreIn B t := by
    have := map_oddCentralizerCore_of_injective (f := B.subtype) Subtype.val_injective
      (⟨t, htB⟩ : ↥B)
    rwa [Subgroup.range_subtype] at this
  rw [← h1]
  exact isCyclic_of_surjective ((oddCentralizerCore (⟨t, htB⟩ : ↥B)).equivMapOfInjective
    B.subtype Subtype.val_injective).toMonoidHom (MulEquiv.surjective _)

open CFSG.Blueprint in
theorem no911_psp {Y : Type} [Group Y] [Finite Y] {r p f : ℕ} (hr : 2 ≤ r) (hp2 : p ≠ 2)
    (hL : LieModel Y .PSp r p f) : No911 Y := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    exact no911_of_mulEquiv θ (no911_of_oddCoreCyclic (oddCoreCyclic_psp hp hp2 hf hKc hr))
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
