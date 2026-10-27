module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSplit

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

theorem eq_one_of_commute_leg [Finite K] (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    {A : gsp r K} {d : K} (hd : d ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))} {S : StatedSp r K} {e : K} (he : e ≠ 0)
    (hSS : ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1)
    (hcomm : ∀ D : gsp r K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ m : ℕ, conjAut r K (D ^ 2 ^ m) = 1)
    {x : MulAut (StatedProj (StatedSp r K))} (hx : x ∈ oddCoreIn B (conjAut r K A))
    (hxS : x * conjProjH (StatedSp r K) S = conjProjH (StatedSp r K) S * x) : x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hp3 : (Nat.card K).Prime := by rw [h3]; norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  have hodd := odd_orderOf_of_mem_oddCoreIn hx
  have hxt := commute_of_mem_oddCoreIn hx
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr x
  have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card hp3 τ
  subst hτ
  rw [map_one, mul_one] at hodd hxt hxS ⊢
  have hS' : conjAut r K ⟨S, statedSp_le_gsp S.2⟩ = conjProjH (StatedSp r K) S :=
    conjAut_statedSp S
  rw [← hS'] at hxS
  have h1 := pow_orderOf_succ_commute (by omega) hd hAA hxt hodd
  set SG : gsp r K := ⟨S, statedSp_le_gsp S.2⟩ with hSG
  have hSS' : ((SG : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((SG : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1 := hSS
  have h2' := pow_orderOf_succ_commute (by omega) he hSS' hxS hodd
  obtain ⟨m, hm⟩ := hcomm _ h1 h2'
  rw [map_pow, conjAut_pow_orderOf_succ] at hm
  exact UnbalancedCatalog.SpChain.eq_one_of_odd_orderOf hodd hm

theorem oddCoreIn_eq_bot_of_four [Finite K] (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {A : gsp r K} {d : K} (hd : d ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    {S₁ S₂ : StatedSp r K} {e₁ e₂ e₃ : K} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (he₃ : e₃ ≠ 0)
    (hS₁ : ((S₁ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((S₁ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e₁ • 1)
    (hS₂ : ((S₂ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((S₂ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e₂ • 1)
    (hS₃ : (((S₁ * S₂ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((S₁ * S₂ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e₃ • 1)
    (hA₁ : ((S₁ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S₁ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hA₂ : ((S₂ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S₂ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hc : ∀ S : StatedSp r K, (S = S₁ ∨ S = S₂ ∨ S = S₁ * S₂) → ∀ D : gsp r K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ m : ℕ, conjAut r K (D ^ 2 ^ m) = 1) :
    oddCoreIn B (conjAut r K A) = ⊥ := by
  have hcomA : ∀ S : StatedSp r K,
      ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      conjProjH (StatedSp r K) S ∈ B ⊓ centralizer ({conjAut r K A} : Set _) := by
    intro S hS
    refine Subgroup.mem_inf.2 ⟨hB ⟨_, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, ← conjAut_statedSp, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Units.ext (by simp only [Subgroup.coe_mul, Units.val_mul]; exact hS))
  have hsq : ∀ (S : StatedSp r K) (e : K), e ≠ 0 →
      ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1 →
      conjProjH (StatedSp r K) S * conjProjH (StatedSp r K) S = 1 := by
    intro S e he hS
    rw [← conjAut_statedSp, ← map_mul, conjAut_eq_one_iff (by omega)]
    refine ⟨Units.mk0 e he, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hS.trans (smul_one_eq_diagonal e)
  have hleg : ∀ S : StatedSp r K, (S = S₁ ∨ S = S₂ ∨ S = S₁ * S₂) → ∀ e : K, e ≠ 0 →
      ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((S : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = e • 1 →
      ∀ x ∈ oddCoreIn B (conjAut r K A),
        conjProjH (StatedSp r K) S * x = x * conjProjH (StatedSp r K) S → x = 1 :=
    fun S hS e he hSS x hx hxS => eq_one_of_commute_leg h3 hr hd hAA he hSS (hc S hS) hx hxS.symm
  refine eq_bot_of_four_group (s₁ := conjProjH (StatedSp r K) S₁)
    (s₂ := conjProjH (StatedSp r K) S₂) (hsq _ _ he₁ hS₁) (hsq _ _ he₂ hS₂)
    (fun x hx => PSL.conj_mem_oddCoreIn hx (hcomA _ hA₁))
    (fun x hx => PSL.conj_mem_oddCoreIn hx (hcomA _ hA₂)) (hleg _ (Or.inl rfl) _ he₁ hS₁)
    (hleg _ (Or.inr (Or.inl rfl)) _ he₂ hS₂) ?_
  rw [← map_mul]
  exact hleg _ (Or.inr (Or.inr rfl)) _ he₃ hS₃

abbrev fourMat (K : Type) [Field K] : Fin 3 → Matrix (Fin 2) (Fin 2) K :=
  ![!![1, 0; 0, -1], !![0, 1; 1, 0], !![0, 1; -1, 0]]

theorem zmod_three_pow_eight_of_commute : ∀ (k : Fin 3) (a b c d : ZMod 3),
    !![a, b; c, d] * fourMat (ZMod 3) k = fourMat (ZMod 3) k * !![a, b; c, d] →
    a * d - b * c ≠ 0 → !![a, b; c, d] ^ 8 = 1 := by
  decide

theorem pow_eight_of_commute_fourMat [Finite K] (h3 : Nat.card K = 3) (k : Fin 3)
    {P : Matrix (Fin 2) (Fin 2) K} (hP : P * fourMat K k = fourMat K k * P) (hdet : P.det ≠ 0) :
    P ^ 8 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set f : K →+* ZMod 3 := (FiniteField.ringEquivOfCardEq hc).toRingHom
  have hfinj : Function.Injective f := (FiniteField.ringEquivOfCardEq hc).injective
  have hinj : ∀ M N : Matrix (Fin 2) (Fin 2) K, M.map f = N.map f → M = N := fun M N h => by
    ext i j
    exact hfinj (congrFun (congrFun h i) j)
  have hg : (fourMat K k).map f = fourMat (ZMod 3) k := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> simp
    all_goals rw [map_neg, map_one]; decide
  have hP' := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M.map f) hP
  simp only [Matrix.map_mul, hg] at hP'
  have hdet' : (P.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 hdet
  apply hinj
  rw [Matrix.map_pow, Matrix.map_one f (map_zero f) (map_one f)]
  have hXe := eta_fin_two (P.map f)
  rw [hXe] at hP' hdet' ⊢
  rw [det_fin_two_of] at hdet'
  exact zmod_three_pow_eight_of_commute k _ _ _ _ hP' hdet'

omit [Field K] in
theorem fromBlocks_diag_pow {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n R) (m : ℕ) :
    fromBlocks P 0 0 Q ^ m = fromBlocks (P ^ m) 0 0 (Q ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, fromBlocks_one]
  | succ m ih =>
    rw [pow_succ, ih, fromBlocks_multiply, pow_succ, pow_succ]
    simp

theorem conjAut_pow_eight_of_commute_fourMat [Finite K] (h3 : Nat.card K = 3) (k : Fin 3)
    {D : gsp 2 K}
    (hDA : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      stdSkew 2 K = stdSkew 2 K * ((D : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hDS : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks (fourMat K k) 0 0 (fourMat K k) = fromBlocks (fourMat K k) 0 0 (fourMat K k) *
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K (D ^ 2 ^ 3) = 1 := by
  have h2 := two_ne_zero_of_three h3
  set M := ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hblk := fromBlocks_of_commute_stdSkew h2 hDA
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).1 (D : GL (Fin 2 ⊕ Fin 2) K).isUnit).ne_zero
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  rw [hblk, fromBlocks_multiply, fromBlocks_multiply] at hDS
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hDS
  obtain ⟨h11, -, -, h22⟩ := Matrix.fromBlocks_inj.1 hDS
  have hP8 := pow_eight_of_commute_fourMat h3 k h11 (left_ne_zero_of_mul hdet)
  have hR8 := pow_eight_of_commute_fourMat h3 k h22 (right_ne_zero_of_mul hdet)
  rw [conjAut_eq_one_iff (by norm_num)]
  refine ⟨1, Units.ext ?_⟩
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hM, hblk, show 2 ^ 3 = 8 by norm_num,
    fromBlocks_diag_pow, hP8, hR8, fromBlocks_one, map_one, Units.val_one]

@[expose] def orthLevi (g : Matrix (Fin r) (Fin r) K) (hg : gᵀ * g = 1) : StatedSp r K :=
  ⟨⟨fromBlocks g 0 0 g, fromBlocks gᵀ 0 0 gᵀ, by
      rw [fromBlocks_multiply, mul_eq_one_comm.1 hg]
      simp [fromBlocks_one], by
      rw [fromBlocks_multiply, hg]
      simp [fromBlocks_one]⟩,
    mem_statedSp_iff.2 (show (fromBlocks g 0 0 g)ᵀ * fromBlocks 0 1 (-1) 0 * fromBlocks g 0 0 g =
      fromBlocks 0 1 (-1) 0 by
        rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
        simp [hg])⟩

theorem coe_orthLevi (g : Matrix (Fin r) (Fin r) K) (hg : gᵀ * g = 1) :
    ((orthLevi g hg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks g 0 0 g := rfl

theorem fourMat_orth (k : Fin 3) : (fourMat K k)ᵀ * fourMat K k = 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem fourMat_mul : fourMat K 0 * fourMat K 1 = fourMat K 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem fourMat_sq (k : Fin 3) :
    fourMat K k * fourMat K k = (if k = 2 then (-1 : K) else 1) • 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem skewSplit_oddCoreIn_eq_bot_two_three [Finite K] (h3 : Nat.card K = 3)
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B) :
    oddCoreIn B (conjAut 2 K (stdSkewGsp 2 K)) = ⊥ := by
  set S₁ := orthLevi (fourMat K 0) (fourMat_orth 0) with hS₁
  set S₂ := orthLevi (fourMat K 1) (fourMat_orth 1) with hS₂
  have hmat : ∀ k : Fin 3, ∀ S : StatedSp 2 K,
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (fourMat K k) 0 0 (fourMat K k) →
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (if k = 2 then (-1 : K) else 1) • 1 := by
    intro k S hS
    rw [hS, fromBlocks_multiply, fourMat_sq]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
  have hcomA : ∀ k : Fin 3, ∀ S : StatedSp 2 K,
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (fourMat K k) 0 0 (fourMat K k) →
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro k S hS
    rw [hS, coe_stdSkewGsp, stdSkew_eq_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have h12 : ((S₁ * S₂ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      ((orthLevi (fourMat K 2) (fourMat_orth 2) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hS₁, hS₂, coe_orthLevi, coe_orthLevi, coe_orthLevi,
      fromBlocks_multiply, fourMat_mul]
    simp
  have hm₁ : ((S₁ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (fourMat K 0) 0 0 (fourMat K 0) := coe_orthLevi _ _
  have hm₂ : ((S₂ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (fourMat K 1) 0 0 (fourMat K 1) := coe_orthLevi _ _
  have hm₃ : (((S₁ * S₂ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (fourMat K 2) 0 0 (fourMat K 2) := by
    rw [h12, coe_orthLevi]
  have hAA : ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (1 : K) • 1 := by rw [coe_stdSkewGsp, stdSkew_mul_self, one_smul]
  have hS1sq := hmat 0 S₁ hm₁
  have hS2sq := hmat 1 S₂ hm₂
  have hS3sq := hmat 2 _ hm₃
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
    at hS1sq hS2sq hS3sq
  refine oddCoreIn_eq_bot_of_four h3 le_rfl hB one_ne_zero hAA one_ne_zero one_ne_zero
    (neg_ne_zero.2 one_ne_zero) hS1sq hS2sq hS3sq (hcomA 0 _ hm₁) (hcomA 1 _ hm₂) ?_
  rintro S hS D hDA hDS
  refine ⟨3, ?_⟩
  rw [coe_stdSkewGsp] at hDA
  rcases hS with rfl | rfl | rfl
  · rw [hm₁] at hDS
    exact conjAut_pow_eight_of_commute_fourMat h3 0 hDA hDS
  · rw [hm₂] at hDS
    exact conjAut_pow_eight_of_commute_fourMat h3 1 hDA hDS
  · rw [hm₃] at hDS
    exact conjAut_pow_eight_of_commute_fourMat h3 2 hDA hDS

end CFSG.ComponentClassification.Burgoyne.Sp
