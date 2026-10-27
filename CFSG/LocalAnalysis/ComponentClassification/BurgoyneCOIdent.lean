module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOInnerNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd
  commute_compInd_iff commute_signMat_iff det_signMat)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem signGL_empty : signGL K (∅ : Finset (Fin d)) = 1 := by
  apply Units.ext
  rw [coe_signGL, Units.val_one]
  ext i j
  simp [signMat, diagonal_apply, Matrix.one_apply]

theorem signMat_apply_self (J : Finset (Fin d)) (i : Fin d) :
    signMat K J i i = if i ∈ J then -1 else 1 := by
  rw [signMat, diagonal_apply_eq]

theorem det_eq_one_of_mem_commutator {n : ℕ} {H : Subgroup (GL (Fin n) K)} {g : GL (Fin n) K}
    (hg : g ∈ ⁅H, H⁆) : (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : ⁅H, H⁆ ≤ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    rw [commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      mul_comm]
  have h := congrArg Units.val (MonoidHom.mem_ker.1 (hle hg))
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h

theorem even_card_of_sign_mem_oBlock (hK : ringChar K ≠ 2) {I : Finset (Fin d)}
    (h : signGL K I ∈ oBlock K hw I) : Even I.card := by
  have hdet := det_eq_one_of_mem_commutator h
  rw [coe_signGL, det_signMat] at hdet
  have hne : (-1 : K) ≠ 1 := fun e => Ring.two_ne_zero hK (by linear_combination -e)
  exact (neg_one_pow_eq_one_iff_even hne).1 hdet

theorem ite_neg_one_eq_iff (hne : (-1 : K) ≠ 1) {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then (-1 : K) else 1) = if Q then -1 else 1) ↔ (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hne, hne.symm]

theorem ite_neg_one_eq_neg_iff (hne : (-1 : K) ≠ 1) {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then (-1 : K) else 1) = -(if Q then -1 else 1)) ↔ (P ↔ ¬ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hne, hne.symm]

theorem eq_or_eq_compl_of_sign_eq_mul (hK : ringChar K ≠ 2) {A B : Finset (Fin d)} {c : Kˣ}
    (h : signGL K B = signGL K A * GeneralLinearGroup.scalar (Fin d) c) : B = A ∨ B = Aᶜ := by
  have hne : (-1 : K) ≠ 1 := fun e => Ring.two_ne_zero hK (by linear_combination -e)
  have he : ∀ i, signMat K B i i = signMat K A i i * c := by
    intro i
    have := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) i i) h
    simp only [Units.val_mul, coe_signGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      mul_diagonal] at this
    exact this
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
  · left
    ext i
    exact isEmptyElim i
  have hc : (c : K) = 1 ∨ (c : K) = -1 := by
    have e := he i₀
    rw [signMat_apply_self, signMat_apply_self] at e
    split_ifs at e with h1 h2 h2
    · left; linear_combination e
    · right; linear_combination -e
    · right; linear_combination e
    · left; linear_combination -e
  rcases hc with hc | hc
  · left
    ext i
    have e := he i
    rw [signMat_apply_self, signMat_apply_self, hc, mul_one] at e
    exact (ite_neg_one_eq_iff hne).1 e
  · right
    ext i
    have e := he i
    rw [signMat_apply_self, signMat_apply_self, hc, mul_neg_one] at e
    rw [Finset.mem_compl]
    exact (ite_neg_one_eq_neg_iff hne).1 e

theorem eq_or_eq_compl_of_projH_sign_eq (hK : ringChar K ≠ 2) {A B : Finset (Fin d)}
    (hA : signGL K A ∈ matrixDerived (oQ (diagGL hw)))
    (hB : signGL K B ∈ matrixDerived (oQ (diagGL hw)))
    (h : projH _ (⟨signGL K A, hA⟩ : matrixDerived (oQ (diagGL hw))) = projH _ ⟨signGL K B, hB⟩) :
    B = A ∨ B = Aᶜ := by
  rw [projH_eq_projH_iff, mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  refine eq_or_eq_compl_of_sign_eq_mul hK (c := c) ?_
  have hA2 : signGL K A * signGL K A = 1 := Units.ext (by
    rw [Units.val_mul, coe_signGL, PSL.signMat_mul_self, Units.val_one])
  have hc' : GeneralLinearGroup.scalar (Fin d) c = (signGL K A)⁻¹ * signGL K B := hc
  rw [hc', ← mul_assoc, mul_inv_cancel, one_mul]

theorem orderOf_projH_sign (hK : ringChar K ≠ 2) {A : Finset (Fin d)}
    (hA : signGL K A ∈ matrixDerived (oQ (diagGL hw))) (hAne : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    orderOf (projH _ (⟨signGL K A, hA⟩ : matrixDerived (oQ (diagGL hw)))) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨signGL K A, hA⟩ : matrixDerived (oQ (diagGL hw))) ^ 2 = 1 := Subtype.ext (Units.ext (by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_signGL, pow_two, PSL.signMat_mul_self]
      rfl))
    rw [this, map_one]
  · intro h1
    have h0 : signGL K (∅ : Finset (Fin d)) ∈ matrixDerived (oQ (diagGL hw)) := by
      rw [signGL_empty]; exact one_mem _
    have h1' : projH _ (⟨signGL K (∅ : Finset (Fin d)), h0⟩ : matrixDerived (oQ (diagGL hw))) =
        projH _ ⟨signGL K A, hA⟩ := by
      rw [h1, ← map_one (projH (matrixDerived (oQ (diagGL hw))))]
      exact congrArg _ (Subtype.ext signGL_empty)
    rcases eq_or_eq_compl_of_projH_sign_eq hw hK h0 hA h1' with h | h
    · rw [h] at hAne
      exact Finset.not_nonempty_empty hAne
    · rw [h, compl_compl] at hAc
      exact Finset.not_nonempty_empty hAc

theorem sign_mem_oBlock_of_mem_blockP (J I : Finset (Fin d)) (hI : I = J ∨ I = Jᶜ)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hIc : Iᶜ.Nonempty)
    (hx : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ blockP K hw I) :
    signGL K I ∈ oBlock K hw I := by
  obtain ⟨g, hg, hgx⟩ := hx
  replace hg : (g : GL (Fin d) K) ∈ oBlock K hw I := hg
  rw [projH_eq_projH_iff, mem_subgroupOf] at hgx
  obtain ⟨c, hc⟩ := hgx
  have hc' : GeneralLinearGroup.scalar (Fin d) c = (g : GL (Fin d) K)⁻¹ * signGL K J := hc
  have e : signGL K J = (g : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc', mul_inv_cancel_left]
  obtain ⟨k, hk⟩ := hIc
  have hgk := ((mem_oIsoBlock_iff hw).1 (oBlock_le_oIsoBlock hw _ hg)).2
  have ekk := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K) k k) e
  simp only [Units.val_mul, coe_signGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    mul_diagonal, hgk k k (Or.inl (Finset.mem_compl.1 hk)), ite_true, one_mul,
    signMat_apply_self] at ekk
  rcases hI with rfl | rfl
  ·
    rw [ite_eq_right (Finset.mem_compl.1 hk)] at ekk
    have hc1 : c = 1 := Units.ext ekk.symm
    rw [hc1, map_one, mul_one] at e
    rw [e]
    exact hg
  ·
    rw [ite_eq_left (by simpa using hk)] at ekk
    have hc1 : c = -1 := Units.ext (by rw [← ekk]; rfl)
    have e2 : signGL K Jᶜ = (g : GL (Fin d) K) := by
      rw [signGL_eq_compl_mul, hc1] at e
      have hs : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) *
          GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) = 1 := by
        rw [← map_mul, neg_one_mul, neg_neg, map_one]
      calc signGL K Jᶜ = signGL K Jᶜ * GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) *
            GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by rw [mul_assoc, hs, mul_one]
        _ = (g : GL (Fin d) K) := by
            rw [e, mul_assoc, hs, mul_one]
    rw [e2]
    exact hg

theorem diag_of_commute_pairs (hK : ringChar K ≠ 2) {I I₀ : Finset (Fin d)}
    (h3 : 3 ≤ I₀.card) (hout : ∀ x ∈ I, ∀ y ∈ I, x ∉ I₀ → y ∉ I₀ → x = y)
    {M : GL (Fin d) K} (hM : M ∈ oIsoBlock K hw I)
    (hc : ∀ a ∈ I₀, ∀ b ∈ I₀, a ≠ b → M * signGL K {a, b} = signGL K {a, b} * M) :
    ∀ i j, i ≠ j → (M : Matrix (Fin d) (Fin d) K) i j = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsupp := ((mem_oIsoBlock_iff hw).1 hM).2
  have hpair : ∀ a ∈ I₀, ∀ b ∈ I₀, a ≠ b → ∀ x y, (x ∈ ({a, b} : Finset (Fin d)) ↔
      y ∉ ({a, b} : Finset (Fin d))) → (M : Matrix (Fin d) (Fin d) K) x y = 0 := by
    intro a ha b hb hab
    have e := congrArg Units.val (hc a ha b hb hab)
    rw [Units.val_mul, Units.val_mul, coe_signGL] at e
    exact (commute_compInd_iff _ _).1 ((commute_signMat_iff h2 _ _).1 e.symm)
  intro i j hij
  by_cases hiI : i ∈ I
  · by_cases hjI : j ∈ I
    ·
      have hex : (I₀ \ {i, j}).Nonempty := by
        rw [← Finset.card_pos]
        have h1 := Finset.le_card_sdiff {i, j} I₀
        have h2 : ({i, j} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨b, hb⟩ := hex
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      obtain ⟨hb, hbi, hbj⟩ := hb
      by_cases hi0 : i ∈ I₀
      · exact hpair i hi0 b hb (Ne.symm hbi) i j (by simp [Ne.symm hij, Ne.symm hbj])
      · have hj0 : j ∈ I₀ := by
          by_contra hj0
          exact hij (hout i hiI j hjI hi0 hj0)
        exact hpair j hj0 b hb (Ne.symm hbj) i j (by simp [hij, Ne.symm hbi])
    · rw [hsupp i j (Or.inr hjI), ite_eq_right hij]
  · rw [hsupp i j (Or.inl hiI), ite_eq_right hij]

theorem sq_eq_one_of_mem_center_blockP (hK : ringChar K ≠ 2) {I : Finset (Fin d)}
    (hIc : Iᶜ.Nonempty) (hNF : BlockNF w I) {z : blockP K hw I}
    (hz : z ∈ center (blockP K hw I)) : z ^ 2 = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨I₀, hI₀, h3, hI₀w, hout⟩ := hNF
  obtain ⟨_, ⟨M, hM, rfl⟩⟩ := z
  replace hM : (M : GL (Fin d) K) ∈ oBlock K hw I := hM
  have hcomm : ∀ g ∈ oBlock K hw I, (M : GL (Fin d) K) * g = g * M := by
    intro g hg
    have hgΩ := oBlock_le_matrixDerived hw h2 I hg
    have hz' := mem_center_iff.1 hz ⟨projH _ ⟨g, hgΩ⟩, ⟨⟨g, hgΩ⟩, hg, rfl⟩⟩
    have hz'' : projH _ (⟨g, hgΩ⟩ * M) = projH _ (M * ⟨g, hgΩ⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val hz'
    have hmem : (M * ⟨g, hgΩ⟩)⁻¹ * (⟨g, hgΩ⟩ * M) ∈
        (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) :=
      mul_mem (inv_mem (mul_mem hM hg)) (mul_mem hg hM)
    have h1 := projH_injOn_oBlock hw hIc hmem (by
      rw [map_mul, map_inv, hz'', inv_mul_cancel])
    have h1' := congrArg Subtype.val (inv_mul_eq_one.1 h1)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1'
    exact h1'
  have hpairs : ∀ a ∈ I₀, ∀ b ∈ I₀, a ≠ b →
      (M : GL (Fin d) K) * signGL K {a, b} = signGL K {a, b} * M := fun a ha b hb hab =>
    hcomm _ (signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb))
  have hdiag := diag_of_commute_pairs hw hK h3 hout (oBlock_le_oIsoBlock hw _ hM) hpairs
  have hiso := (oBlock_le_oIsoBlock hw _ hM).1
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL] at hiso
  have hsq : ∀ i, ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
      ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i
    have e := congrFun (congrFun hiso i) i
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, transpose_apply, diagonal_apply_eq] at e
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hdiag k i hk, zero_mul, zero_mul])
      (by simp)] at e
    have : w i * (((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i - 1) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (hw i))
  have hM2 : M ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two, Matrix.mul_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i (fun k _ hk => by rw [hdiag i k (Ne.symm hk), zero_mul])
        (by simp), hsq]
      simp
    · rw [Finset.sum_eq_zero fun k _ => by
        by_cases hk : k = i
        · rw [hk, hdiag i j hij, mul_zero]
        · rw [hdiag i k (Ne.symm hk), zero_mul]]
      simp [Matrix.one_apply_ne hij]
  apply Subtype.ext
  change projH _ M ^ 2 = 1
  rw [← map_pow, hM2, map_one]

end CFSG.ComponentClassification.Burgoyne.C
