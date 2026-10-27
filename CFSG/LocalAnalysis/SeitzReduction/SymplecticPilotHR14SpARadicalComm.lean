module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpARadical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerPerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open scoped commutatorElement

variable {K : Type} [Field K] {n j : ℕ}

section LeviCent

theorem leviEmbedGL_mem_centralizer_spARep {A : GL (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K) * spARepMat n j * (A : Matrix (Fin n) (Fin n) K)ᵀ =
      spARepMat n j) :
    leviEmbedGL K n A ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff]
  have h := leviEmbedGL_conj_upperUnipotentSp A (spARepMat_transpose (K := K) n j)
  have h2 : upperUnipotentSp n K (transpose_mul_mul_transpose (A : Matrix (Fin n) (Fin n) K)
      (spARepMat_transpose (K := K) n j)) = spARep n j := upperUnipotentSp_congr _ _ hA
  rw [h2] at h
  have h' : leviEmbedGL K n A * spARep n j * (leviEmbedGL K n A)⁻¹ = spARep n j := h
  calc leviEmbedGL K n A * spARep n j =
        leviEmbedGL K n A * spARep n j * (leviEmbedGL K n A)⁻¹ * leviEmbedGL K n A := by group
    _ = spARep n j * leviEmbedGL K n A := by rw [h']

theorem diagonal_mul_mul_transpose_apply (d : Fin n → K) (C : Matrix (Fin n) (Fin n) K)
    (k l : Fin n) : (diagonal d * C * (diagonal d)ᵀ) k l = d k * C k l * d l := by
  rw [diagonal_transpose, mul_diagonal, diagonal_mul]

theorem leviEmbedGL_diagGL_mem_centralizer {d : Fin n → Kˣ}
    (hd : ∀ k l : Fin n, spARepMat n j k l ≠ (0 : K) → (d k : K) * d l = 1) :
    leviEmbedGL K n (TauCeti.diagGL d) ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  refine leviEmbedGL_mem_centralizer_spARep ?_
  ext k l
  rw [TauCeti.diagGL_coe, diagonal_mul_mul_transpose_apply]
  by_cases h : spARepMat n j k l = (0 : K)
  · rw [h, mul_zero, zero_mul]
  · rw [show (d k : K) * spARepMat n j k l * d l = spARepMat n j k l * ((d k : K) * d l) by ring,
      hd k l h, mul_one]

end LeviCent

section MidTorus

variable (j) in
@[expose] def spAMidTorus (κ : Kˣ) : Fin n → Kˣ := fun k => if k.val < 2 * j then 1 else κ

theorem spAMidTorus_mem_centralizer (κ : Kˣ) :
    leviEmbedGL K n (TauCeti.diagGL (spAMidTorus (n := n) j κ)) ∈
      centralizer ({spARep n j} : Set (StatedSp n K)) := by
  refine leviEmbedGL_diagGL_mem_centralizer fun k l h => ?_
  rw [spARepMat, of_apply] at h
  have hc : k.val / 2 = l.val / 2 ∧ k ≠ l ∧ k.val < 2 * j ∧ l.val < 2 * j := by
    by_contra hc
    exact h (ite_eq_right hc)
  simp [spAMidTorus, hc.2.2.1, hc.2.2.2]

theorem commutatorElement_spAMidTorus_spAOffUnit (κ : Kˣ) {B : Matrix (Fin n) (Fin n) K}
    (hB : SpAOff j B) (hB' : SpAOff j ((((κ⁻¹ : Kˣ) : K) - 1) • B)) :
    ⁅TauCeti.diagGL (spAMidTorus (n := n) j κ), spAOffUnit hB⁆ = spAOffUnit hB' := by
  apply Units.ext
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, coe_spAOffUnit,
    coe_spAOffUnit, ← map_inv, TauCeti.diagGL_coe, TauCeti.diagGL_coe, coe_spAOffUnit_inv]
  have hD : diagonal (fun k => ((spAMidTorus j κ k : Kˣ) : K)) * (1 + B) *
      diagonal (fun k => (((spAMidTorus j κ)⁻¹ k : Kˣ) : K)) = 1 + ((κ⁻¹ : Kˣ) : K) • B := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, diagonal_mul_diagonal]
    congr 1
    · ext k l
      rw [diagonal_apply, Matrix.one_apply]
      split_ifs with h
      · subst h
        simp
      · rfl
    · ext k l
      rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
      by_cases h : B k l = 0
      · simp [h]
      · obtain ⟨hk, hl⟩ := hB k l h
        have hl' : ¬ l.val < 2 * j := by omega
        simp only [spAMidTorus, Pi.inv_apply, hk, hl', ↓reduceIte, Units.val_one, one_mul]
        ring
  rw [hD, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
    hB.mul_eq_zero hB, sub_zero, sub_smul, one_smul]
  abel

theorem commutatorElement_spAMidTorus_upperUnipotentSp (κ : Kˣ) {X : Matrix (Fin n) (Fin n) K}
    (hX : Xᵀ = X) (hXs : ∀ k l, X k l ≠ 0 → (k.val < 2 * j ↔ 2 * j ≤ l.val)) :
    ⁅leviEmbedGL K n (TauCeti.diagGL (spAMidTorus (n := n) j κ)), upperUnipotentSp n K hX⁆ =
      upperUnipotentSp n K (C := ((κ : K) - 1) • X) (by rw [transpose_smul, hX]) := by
  rw [commutatorElement_leviEmbedGL_upperUnipotentSp]
  refine upperUnipotentSp_congr _ _ ?_
  ext k l
  rw [Matrix.sub_apply, TauCeti.diagGL_coe, diagonal_mul_mul_transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : X k l = 0
  · simp [h]
  · have := hXs k l h
    by_cases hk : k.val < 2 * j
    · simp [spAMidTorus, hk, show ¬ l.val < 2 * j by omega]
      ring
    · simp [spAMidTorus, hk, show l.val < 2 * j by omega]
      ring

end MidTorus

section Members

theorem upperUnipotentSp_mem_centralizer_spARep {X : Matrix (Fin n) (Fin n) K} (hX : Xᵀ = X) :
    upperUnipotentSp n K hX ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff]
  exact upperUnipotentSp_commute hX (spARepMat_transpose n j)

theorem leviEmbedGL_spAOffUnit_mem_centralizer {B : Matrix (Fin n) (Fin n) K}
    (hB : SpAOff j B) :
    leviEmbedGL K n (spAOffUnit hB) ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  refine leviEmbedGL_mem_centralizer_spARep ?_
  rw [coe_spAOffUnit, Matrix.add_mul, Matrix.one_mul, hB.mul_spARepMat, add_zero, transpose_add,
    transpose_one, Matrix.mul_add, Matrix.mul_one, hB.spARepMat_mul_transpose, add_zero]

theorem SpAOff.smul {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) (c : K) :
    SpAOff j (c • B) := fun k l h =>
  hB k l (fun h' => h (by rw [Matrix.smul_apply, h', smul_zero]))

theorem leviEmbedGL_spAOffUnit_mem_commutator {κ : Kˣ} (hκ : (κ : K) ≠ 1)
    {B : Matrix (Fin n) (Fin n) K} (hB : SpAOff j B) :
    leviEmbedGL K n (spAOffUnit hB) ∈
      ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
        centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hκ' : ((κ⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
    rw [sub_ne_zero, Units.val_inv_eq_inv_val]
    exact fun h => hκ (inv_eq_one.1 h)
  set c : K := (((κ⁻¹ : Kˣ) : K) - 1)⁻¹
  have h1 : SpAOff j (c • B) := hB.smul c
  have h2 : SpAOff j ((((κ⁻¹ : Kˣ) : K) - 1) • (c • B)) := h1.smul _
  have e := commutatorElement_spAMidTorus_spAOffUnit κ h1 h2
  have e2 : leviEmbedGL K n (spAOffUnit h2) = leviEmbedGL K n (spAOffUnit hB) := by
    congr 1
    apply Units.ext
    rw [coe_spAOffUnit, coe_spAOffUnit, smul_smul, mul_inv_cancel₀ hκ', one_smul]
  rw [← e2, ← e, map_commutatorElement]
  exact commutator_mem_commutator (spAMidTorus_mem_centralizer κ)
    (leviEmbedGL_spAOffUnit_mem_centralizer h1)

theorem upperUnipotentSp_mem_commutator_of_off {κ : Kˣ} (hκ : (κ : K) ≠ 1)
    {X : Matrix (Fin n) (Fin n) K} (hX : Xᵀ = X)
    (hXs : ∀ k l, X k l ≠ 0 → (k.val < 2 * j ↔ 2 * j ≤ l.val)) :
    upperUnipotentSp n K hX ∈
      ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
        centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hκ' : (κ : K) - 1 ≠ 0 := sub_ne_zero.2 hκ
  set c : K := ((κ : K) - 1)⁻¹
  have hX' : (c • X)ᵀ = c • X := by rw [transpose_smul, hX]
  have hXs' : ∀ k l, (c • X) k l ≠ 0 → (k.val < 2 * j ↔ 2 * j ≤ l.val) := fun k l h =>
    hXs k l (fun h' => h (by rw [Matrix.smul_apply, h', smul_zero]))
  have e := commutatorElement_spAMidTorus_upperUnipotentSp (j := j) κ hX' hXs'
  have e2 : upperUnipotentSp n K (C := ((κ : K) - 1) • (c • X))
      (by rw [transpose_smul, hX']) = upperUnipotentSp n K hX :=
    upperUnipotentSp_congr _ _ (by rw [smul_smul, mul_inv_cancel₀ hκ', one_smul])
  rw [← e2, ← e]
  exact commutator_mem_commutator (spAMidTorus_mem_centralizer κ)
    (upperUnipotentSp_mem_centralizer_spARep hX')

theorem upperUnipotentSp_sum_mem {ι : Type*} (H : Subgroup (StatedSp n K)) (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (hf : ∀ i, (f i)ᵀ = f i)
    (h : ∀ i ∈ s, upperUnipotentSp n K (hf i) ∈ H)
    (hs : (∑ i ∈ s, f i)ᵀ = ∑ i ∈ s, f i) : upperUnipotentSp n K hs ∈ H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [upperUnipotentSp_congr hs transpose_zero Finset.sum_empty, upperUnipotentSp_zero]
    exact H.one_mem
  | insert a s ha ih =>
    have hsum : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := Finset.sum_insert ha
    have hs' : (∑ i ∈ s, f i)ᵀ = ∑ i ∈ s, f i := by
      rw [transpose_sum]
      exact Finset.sum_congr rfl fun i _ => hf i
    rw [upperUnipotentSp_congr hs (by rw [transpose_add, hf a, hs']) hsum,
      ← upperUnipotentSp_mul (hf a) hs']
    exact H.mul_mem (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hs')

end Members

section Pair

@[expose] def spAPairTorus (k : Fin n) (κ : Kˣ) : Fin n → Kˣ :=
  fun m => if m = k then κ else if m = spAPar k then κ⁻¹ else 1

variable (hjn : 2 * j ≤ n)
include hjn

theorem spAPar_ne {k : Fin n} (hk : k.val < 2 * j) : spAPar k ≠ k := by
  intro h
  have := spAPar_val hjn hk
  rw [h] at this
  split_ifs at this <;> omega

theorem spAPairTorus_mem_centralizer {k : Fin n} (hk : k.val < 2 * j) (κ : Kˣ) :
    leviEmbedGL K n (TauCeti.diagGL (spAPairTorus k κ)) ∈
      centralizer ({spARep n j} : Set (StatedSp n K)) := by
  refine leviEmbedGL_diagGL_mem_centralizer fun m l h => ?_
  rw [spARepMat_apply hjn] at h
  have hc : l.val < 2 * j ∧ m = spAPar l := by
    by_contra hc
    exact h (ite_eq_right hc)
  obtain ⟨hl, rfl⟩ := hc
  have hpk := spAPar_ne hjn hk
  by_cases h1 : l = k
  · subst h1
    simp [spAPairTorus, hpk]
  · by_cases h2 : l = spAPar k
    · subst h2
      rw [spAPar_spAPar hjn hk]
      simp [spAPairTorus, hpk]
    · have h3 : spAPar l ≠ k := fun h => h2 (by rw [← h, spAPar_spAPar hjn hl])
      have h4 : spAPar l ≠ spAPar k := fun h =>
        h1 (by rw [← spAPar_spAPar hjn hl, h, spAPar_spAPar hjn hk])
      simp [spAPairTorus, h1, h2, h3, h4]

theorem siegDiag_mem_commutator [CharP K 2] {κ : Kˣ} (hκ : (κ : K) ≠ 1) {k : Fin n}
    (hk : k.val < 2 * j) (c : K) :
    siegDiag K k c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hκ2 : (κ : K) ^ 2 - 1 ≠ 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have e : (κ : K) ^ 2 - 1 = ((κ : K) - 1) ^ 2 := by linear_combination ((κ : K) - 1) * h2
    rw [e]
    exact pow_ne_zero 2 (sub_ne_zero.2 hκ)
  have e : ⁅leviEmbedGL K n (TauCeti.diagGL (spAPairTorus k κ)),
      siegDiag K k (c / ((κ : K) ^ 2 - 1))⁆ = siegDiag K k c := by
    rw [siegDiag, commutatorElement_leviEmbedGL_upperUnipotentSp, siegDiag]
    refine upperUnipotentSp_congr _ _ ?_
    ext a b
    rw [Matrix.sub_apply, TauCeti.diagGL_coe, diagonal_mul_mul_transpose_apply]
    by_cases ha : a = k <;> by_cases hb : b = k
    · subst ha hb
      simp only [spAPairTorus, Matrix.single_apply, and_self, ↓reduceIte]
      field_simp
    · simp [Ne.symm hb]
    · simp [Ne.symm ha]
    · simp [Ne.symm ha]
  rw [← e]
  exact commutator_mem_commutator (spAPairTorus_mem_centralizer hjn hk κ)
    (upperUnipotentSp_mem_centralizer_spARep _)

theorem siegPair_mem_commutator {κ : Kˣ} (hκ : (κ : K) ≠ 1) {k l : Fin n}
    (hk : k.val < 2 * j) (hlk : l ≠ k) (hlp : l ≠ spAPar k) (c : K) :
    siegPair K k l c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hκ1 : (κ : K) - 1 ≠ 0 := sub_ne_zero.2 hκ
  have e : ⁅leviEmbedGL K n (TauCeti.diagGL (spAPairTorus k κ)),
      siegPair K k l (c / ((κ : K) - 1))⁆ = siegPair K k l c := by
    rw [siegPair, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair]
    refine upperUnipotentSp_congr _ _ ?_
    ext a b
    rw [Matrix.sub_apply, TauCeti.diagGL_coe, diagonal_mul_mul_transpose_apply]
    have hdl : ((spAPairTorus k κ l : Kˣ) : K) = 1 := by simp [spAPairTorus, hlk, hlp]
    have hdk : ((spAPairTorus k κ k : Kˣ) : K) = κ := by simp [spAPairTorus]
    by_cases hab : (a = k ∧ b = l) ∨ (a = l ∧ b = k)
    · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, and_self, hlk, Ne.symm hlk,
          ↓reduceIte, add_zero, hdl, hdk]
        field_simp
      · simp only [Matrix.add_apply, Matrix.single_apply, and_self, hlk, Ne.symm hlk,
          ↓reduceIte, zero_add, hdl, hdk]
        field_simp
    · have h1 : ¬ (k = a ∧ l = b) := fun h => hab (Or.inl ⟨h.1.symm, h.2.symm⟩)
      have h2 : ¬ (l = a ∧ k = b) := fun h => hab (Or.inr ⟨h.1.symm, h.2.symm⟩)
      simp [Matrix.add_apply, h1, h2]
  rw [← e]
  exact commutator_mem_commutator (spAPairTorus_mem_centralizer hjn hk κ)
    (upperUnipotentSp_mem_centralizer_spARep _)

theorem single_spAPar_mul_spARepMat {k : Fin n} (hk : k.val < 2 * j) :
    single k (spAPar k) (1 : K) * spARepMat n j = single k k 1 := by
  ext a b
  by_cases ha : a = k
  · subst ha
    rw [single_mul_apply_same, one_mul, spARepMat_apply hjn, Matrix.single_apply]
    by_cases hb : b = a
    · subst hb
      simp [hk]
    · rw [ite_eq_right (fun h => hb (by rw [← spAPar_spAPar hjn h.1, ← h.2, spAPar_spAPar hjn hk])),
        ite_eq_right (fun h => hb h.2.symm)]
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha, Matrix.single_apply,
      ite_eq_right (fun h => ha h.1.symm)]

theorem spARepMat_mul_single_spAPar {k : Fin n} (hk : k.val < 2 * j) :
    spARepMat n j * single (spAPar k) k (1 : K) = single k k 1 := by
  ext a b
  by_cases hb : b = k
  · subst hb
    rw [mul_single_apply_same, mul_one, spARepMat_apply hjn, Matrix.single_apply,
      spAPar_spAPar hjn hk]
    by_cases ha : a = b
    · subst ha
      simp [spAPar_lt hjn hk]
    · rw [ite_eq_right (fun h => ha h.2), ite_eq_right (fun h => ha h.1.symm)]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb, Matrix.single_apply,
      ite_eq_right (fun h => hb h.2.symm)]

theorem leviTv_spAPar_mem_centralizer [CharP K 2] {k : Fin n} (hk : k.val < 2 * j) :
    leviTv K (Ne.symm (spAPar_ne hjn hk)) (1 : K) ∈
      centralizer ({spARep n j} : Set (StatedSp n K)) := by
  refine leviEmbedGL_mem_centralizer_spARep ?_
  have h0 : single k k (1 : K) * single (spAPar k) k 1 = 0 :=
    Matrix.single_mul_single_of_ne (1 : K) k k (spAPar k) (Ne.symm (spAPar_ne hjn hk)) 1
  have h2 : single k k (1 : K) + single k k 1 = 0 := by
    rw [← Matrix.single_add, one_add_one_eq_two, CharTwo.two_eq_zero, Matrix.single_zero]
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, transpose_add, transpose_one,
    transpose_single, Matrix.add_mul, Matrix.one_mul, single_spAPar_mul_spARepMat hjn hk,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, spARepMat_mul_single_spAPar hjn hk,
    Matrix.mul_add, Matrix.mul_one, h0, add_zero, add_assoc, h2, add_zero]

theorem siegPair_spAPar_mem_commutator [CharP K 2] {κ : Kˣ} (hκ : (κ : K) ≠ 1) {k : Fin n}
    (hk : k.val < 2 * j) (c : K) :
    siegPair K k (spAPar k) c ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have hkp : k ≠ spAPar k := Ne.symm (spAPar_ne hjn hk)
  have e : ⁅leviTv K hkp (1 : K), siegDiag K (spAPar k) c⁆ =
      siegPair K k (spAPar k) c * siegDiag K k c := by
    rw [leviTv, siegDiag, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair, siegDiag,
      upperUnipotentSp_mul]
    refine upperUnipotentSp_congr _ _ ?_
    rw [TauCeti.coe_transvectionUnit, Matrix.transvection, transpose_add, transpose_one,
      transpose_single]
    simp only [Matrix.add_mul, Matrix.mul_add, single_mul_single_same, one_mul, mul_one]
    abel
  have hmem : siegPair K k (spAPar k) c =
      ⁅leviTv K hkp (1 : K), siegDiag K (spAPar k) c⁆ * (siegDiag K k c)⁻¹ := by
    rw [e, mul_inv_cancel_right]
  rw [hmem]
  exact mul_mem (commutator_mem_commutator (leviTv_spAPar_mem_centralizer hjn hk)
    (upperUnipotentSp_mem_centralizer_spARep _))
    (inv_mem (siegDiag_mem_commutator hjn hκ hk c))

end Pair

section Main

variable [CharP K 2] (hjn : 2 * j ≤ n) {κ : Kˣ} (hκ : (κ : K) ≠ 1)
include hjn hκ

theorem upperUnipotentSp_mem_commutator_of_inner {X : Matrix (Fin n) (Fin n) K} (hX : Xᵀ = X)
    (hXs : ∀ a b, X a b ≠ 0 → a.val < 2 * j ∧ b.val < 2 * j) :
    upperUnipotentSp n K hX ∈ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  set H := ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆
  set Xd : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => if a = b then X a b else 0 with hXd
  set Xu : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => if a < b then X a b else 0 with hXu
  have hd : ∀ a b, (single a b (Xd a b))ᵀ = single a b (Xd a b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact transpose_single a a _
    · rw [hXd, of_apply, ite_eq_right hab, Matrix.single_zero, transpose_zero]
  have hu : ∀ a b, (single a b (Xu a b) + single b a (Xu a b))ᵀ =
      single a b (Xu a b) + single b a (Xu a b) := fun a b => by
    rw [transpose_add, transpose_single, transpose_single, add_comm]
  have hone : ∀ {Y : Matrix (Fin n) (Fin n) K} (hY : Yᵀ = Y), Y = 0 →
      upperUnipotentSp n K hY ∈ H := by
    intro Y hY h0
    rw [upperUnipotentSp_congr hY transpose_zero h0, upperUnipotentSp_zero]
    exact H.one_mem
  have hdmem : ∀ a b, upperUnipotentSp n K (hd a b) ∈ H := by
    intro a b
    by_cases hab : a = b
    · subst hab
      by_cases h0 : X a a = 0
      · exact hone _ (by rw [hXd, of_apply, ite_eq_left rfl, h0, Matrix.single_zero])
      · rw [upperUnipotentSp_congr (hd a a) (transpose_single a a (X a a))
          (by rw [hXd, of_apply, ite_eq_left rfl])]
        exact siegDiag_mem_commutator hjn hκ (hXs a a h0).1 (X a a)
    · exact hone _ (by rw [hXd, of_apply, ite_eq_right hab, Matrix.single_zero])
  have humem : ∀ a b, upperUnipotentSp n K (hu a b) ∈ H := by
    intro a b
    by_cases hab : a < b
    · by_cases h0 : X a b = 0
      · exact hone _ (by rw [hXu, of_apply, ite_eq_left hab, h0, Matrix.single_zero,
          Matrix.single_zero, add_zero])
      · obtain ⟨ha, -⟩ := hXs a b h0
        rw [upperUnipotentSp_congr (hu a b)
          (C' := single a b (X a b) + single b a (X a b))
          (by rw [transpose_add, transpose_single, transpose_single, add_comm])
          (by rw [hXu, of_apply, ite_eq_left hab])]
        by_cases hbp : b = spAPar a
        · subst hbp
          exact siegPair_spAPar_mem_commutator hjn hκ ha (X a (spAPar a))
        · exact siegPair_mem_commutator hjn hκ ha hab.ne' hbp (X a b)
    · exact hone _ (by rw [hXu, of_apply, ite_eq_right hab, Matrix.single_zero,
        Matrix.single_zero, add_zero])
  have hsd : ∑ a, ∑ b, single a b (Xd a b) = Xd := (matrix_eq_sum_single Xd).symm
  have hsu : ∑ a, ∑ b, (single a b (Xu a b) + single b a (Xu a b)) = Xu + Xuᵀ := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
      ← matrix_eq_sum_single Xu]
    congr 1
    conv_rhs => rw [matrix_eq_sum_single Xu]
    rw [transpose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [transpose_sum]
    exact Finset.sum_congr rfl fun b _ => (transpose_single _ _ _).symm
  have hX3 : X = Xd + (Xu + Xuᵀ) := by
    ext a b
    rw [Matrix.add_apply, Matrix.add_apply, transpose_apply, hXd, hXu, of_apply, of_apply,
      of_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · rw [ite_eq_right h.ne, ite_eq_left h, ite_eq_right (not_lt.2 h.le), zero_add, add_zero]
    · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl a), add_zero, add_zero]
    · rw [ite_eq_right h.ne', ite_eq_right (not_lt.2 h.le), ite_eq_left h, zero_add, zero_add]
      exact (congrFun (congrFun hX a) b).symm
  have hXd' : Xdᵀ = Xd := by
    rw [← hsd, transpose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [transpose_sum]
    exact Finset.sum_congr rfl fun b _ => hd a b
  have hXu' : (Xu + Xuᵀ)ᵀ = Xu + Xuᵀ := by
    rw [transpose_add, transpose_transpose, add_comm]
  have hmd : upperUnipotentSp n K hXd' ∈ H := by
    have hin : ∀ a, (∑ b, single a b (Xd a b))ᵀ = ∑ b, single a b (Xd a b) := fun a => by
      rw [transpose_sum]
      exact Finset.sum_congr rfl fun b _ => hd a b
    rw [upperUnipotentSp_congr hXd' (by rw [hsd]; exact hXd') hsd.symm]
    exact upperUnipotentSp_sum_mem H _ _ hin (fun a _ =>
      upperUnipotentSp_sum_mem H _ _ (hd a) (fun b _ => hdmem a b) _) _
  have hmu : upperUnipotentSp n K hXu' ∈ H := by
    have hin : ∀ a, (∑ b, (single a b (Xu a b) + single b a (Xu a b)))ᵀ =
        ∑ b, (single a b (Xu a b) + single b a (Xu a b)) := fun a => by
      rw [transpose_sum]
      exact Finset.sum_congr rfl fun b _ => hu a b
    rw [upperUnipotentSp_congr hXu' (by rw [hsu]; exact hXu') hsu.symm]
    exact upperUnipotentSp_sum_mem H _ _ hin (fun a _ =>
      upperUnipotentSp_sum_mem H _ _ (hu a) (fun b _ => humem a b) _) _
  rw [upperUnipotentSp_congr hX (by rw [transpose_add, hXd', hXu']) hX3,
    ← upperUnipotentSp_mul hXd' hXu']
  exact H.mul_mem hmd hmu

theorem spARadical_le_commutator :
    spARadical K n j hjn ≤ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  intro x hx
  obtain ⟨B, hB, X, hX, hXi, rfl⟩ := exists_spARadElt_of_mem hjn hx
  set XI : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun a b => if a.val < 2 * j ∧ b.val < 2 * j then X a b else 0 with hXIdef
  have hXI : XIᵀ = XI := by
    ext a b
    rw [transpose_apply, hXIdef, of_apply, of_apply]
    by_cases h : a.val < 2 * j ∧ b.val < 2 * j
    · rw [ite_eq_left ⟨h.2, h.1⟩, ite_eq_left h]
      exact congrFun (congrFun hX a) b
    · rw [ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩), ite_eq_right h]
  have hXO : (X - XI)ᵀ = X - XI := by rw [transpose_sub, hX, hXI]
  have e : upperUnipotentSp n K hX = upperUnipotentSp n K hXI * upperUnipotentSp n K hXO := by
    rw [upperUnipotentSp_mul]
    exact upperUnipotentSp_congr _ _ (by rw [add_sub_cancel])
  rw [spARadElt, e, ← mul_assoc]
  refine mul_mem (mul_mem (leviEmbedGL_spAOffUnit_mem_commutator hκ hB) ?_) ?_
  · refine upperUnipotentSp_mem_commutator_of_inner hjn hκ hXI fun a b h => ?_
    by_contra h'
    exact h (by rw [hXIdef, of_apply, ite_eq_right h'])
  · refine upperUnipotentSp_mem_commutator_of_off hκ hXO fun a b h => ?_
    rw [Matrix.sub_apply, hXIdef, of_apply] at h
    by_cases ha : a.val < 2 * j <;> by_cases hb : b.val < 2 * j
    · exact absurd (by rw [ite_eq_left ⟨ha, hb⟩, sub_self]) h
    · exact ⟨fun _ => by omega, fun _ => ha⟩
    · exact ⟨fun h' => absurd h' ha, fun h' => absurd hb (by omega)⟩
    · exact absurd (by rw [ite_eq_right (fun h' => ha h'.1), hXi a b (by omega) (by omega),
        sub_zero]) h

end Main

end CFSG.SeitzReduction.SymplecticPilot
