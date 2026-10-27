module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpFour
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrth

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
abbrev skewNs (d : K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 (d • 1) 1 0

theorem skewNs_mul_self (d : K) : skewNs r K d * skewNs r K d = d • 1 := by
  rw [skewNs, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  simp

theorem skewNs_similitude (d : K) :
    (skewNs r K d)ᵀ * formJ r K * skewNs r K d = (-d) • formJ r K := by
  rw [skewNs, fromBlocks_transpose, formJ, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_smul]
  simp

variable (r K) in
@[expose] def skewNsGsp {d : K} (hd0 : d ≠ 0) : gsp r K :=
  ⟨⟨skewNs r K d, d⁻¹ • skewNs r K d,
    by rw [Matrix.mul_smul, skewNs_mul_self, smul_smul, inv_mul_cancel₀ hd0, one_smul],
    by rw [Matrix.smul_mul, skewNs_mul_self, smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩,
    ⟨Units.mk0 (-d) (neg_ne_zero.2 hd0), by rw [Units.val_mk0]; exact skewNs_similitude d⟩⟩

theorem coe_skewNsGsp {d : K} (hd0 : d ≠ 0) :
    ((skewNsGsp r K hd0 : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      skewNs r K d := rfl

theorem sum_skewNs_smul {V : Type} [AddCommGroup V] [Module K V] (d : K)
    (u : Fin r ⊕ Fin r → V) (c : Fin r ⊕ Fin r) :
    ∑ x, skewNs r K d x c • u x = Sum.elim (fun i => u (Sum.inr i)) (fun i => d • u (Sum.inl i))
      c := by
  rw [Fintype.sum_sum_type]
  rcases c with i | i
  · rw [Finset.sum_eq_zero (fun x _ => by simp), zero_add,
      Finset.sum_eq_single i (fun x _ hx => by simp [one_apply, hx]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i (fun x _ hx => by simp [one_apply, hx]) (by simp),
      Finset.sum_eq_zero (fun x _ => by simp), add_zero]
    simp

theorem exists_skew_nonsplit_normal_form [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 1 ≤ r) {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-d) • formJ r K) :
    ∃ H : StatedSp r K, ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        skewNs r K d := by
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hodd : Odd (Nat.card K) := by rw [hKc]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set T := ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) with hT
  have hTv : ∀ v, T v = M *ᵥ v := fun v => linA_apply A v
  have hAns' : ∀ c : K, T ≠ c • 1 := CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  have hAμ : ∀ v w, pairedSympForm K r (T v) (T w) = (-d) * pairedSympForm K r v w := by
    intro v w
    rw [hTv, hTv, form_similitude hJ]
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure hℓ
    hℓ2 hf hKc (V := Fin r ⊕ Fin r → K) (r := r) hr finrank_standard
    pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hAns' hd0
    (linA_mul_self hAA) hAμ
  obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, -, hneg⟩ := hnonsplit hd
  obtain ⟨hh, hhv, hsymm, hsep, -⟩ := hneg (by rw [neg_div, div_self hd0])
  let : Field (UnitaryHigher.scalarSquareField T) := hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField T)) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField T) (Fin r ⊕ Fin r → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
  let h' : (Fin r ⊕ Fin r → K) →ₛₗ[sigma.toRingHom] (Fin r ⊕ Fin r → K) →ₗ[
    UnitaryHigher.scalarSquareField T] UnitaryHigher.scalarSquareField T := hh
  have hnd : h'.Nondegenerate :=
    ⟨hsep, fun y hy => hsep y fun x => by
      rw [← hsymm.eq x y]
      exact (congrArg bar (hy x)).trans (map_zero bar)⟩
  have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
  have hne : sigma ≠ 1 := by
    intro heq
    let x : UnitaryHigher.scalarSquareField T := ⟨T, Algebra.self_mem_adjoin_singleton K _⟩
    have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x]; rfl)
    have hfix : bar x = x := DFunLike.congr_fun heq x
    rw [hfix] at hx
    simp only [zero_smul, zero_sub, one_smul, x] at hx
    have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    have hA2 : (2 : K) • T = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx]
      exact add_neg_cancel _
    apply hAns' 0
    rw [zero_smul]
    calc T = (2 : K)⁻¹ • ((2 : K) • T) := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hA2, smul_zero]
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h' hsymm hnd hsigma hne
  have hcoord : ∀ i j, pairedSympForm K r (b i) (T (b j)) = (if i = j then 1 else 0) ∧
      pairedSympForm K r (b i) (b j) = 0 := by
    intro i j
    have h1 := congrArg Subtype.val (hb i j)
    change (hh (b i) (b j) : Module.End K (Fin r ⊕ Fin r → K)) = _ at h1
    rw [hhv] at h1
    have e : ((if i = j then 1 else 0 : UnitaryHigher.scalarSquareField T) :
        Module.End K (Fin r ⊕ Fin r → K)) = (if i = j then (1 : K) else 0) • 1 + (0 : K) • T := by
      split_ifs <;> simp
    rw [e] at h1
    exact UnitaryHigher.smul_add_smul_inj hAns' h1
  set bb : Fin r → Fin r ⊕ Fin r → K := fun i => b (Fin.cast hfinrank.symm i) with hbb
  have hc1 : ∀ i j, pairedSympForm K r (bb i) (M *ᵥ bb j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbb, ← hTv, (hcoord _ _).1]
    simp only [Fin.cast_inj]
  have hc0 : ∀ i j, pairedSympForm K r (bb i) (bb j) = 0 := fun i j => (hcoord _ _).2
  set u : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K := Sum.elim bb (fun i => M *ᵥ bb i) with hu
  have hgram : ∀ p q, pairedSympForm K r (u p) (u q) = formJ r K p q := by
    rintro (i | i) (j | j)
    · simp only [hu, Sum.elim_inl, formJ, fromBlocks_apply₁₁, Matrix.zero_apply]
      exact hc0 i j
    · simp only [hu, Sum.elim_inl, Sum.elim_inr, formJ, fromBlocks_apply₁₂, one_apply]
      exact hc1 i j
    · simp only [hu, Sum.elim_inl, Sum.elim_inr, formJ, fromBlocks_apply₂₁, Matrix.neg_apply,
        one_apply]
      rw [← bJ_eq, bJ_swap, bJ_eq, hc1]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · simp only [hu, Sum.elim_inr, formJ, fromBlocks_apply₂₂, Matrix.zero_apply]
      rw [form_similitude hJ, hc0, mul_zero]
  obtain ⟨H, hH⟩ := exists_sp_of_gram hgram
  refine ⟨H, inv_mul_mul_eq_of_cols hH fun c => ?_⟩
  rw [sum_skewNs_smul]
  rcases c with i | i
  · rfl
  · simp only [hu, Sum.elim_inr, Sum.elim_inl]
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]

end CFSG.ComponentClassification.Burgoyne.Sp
