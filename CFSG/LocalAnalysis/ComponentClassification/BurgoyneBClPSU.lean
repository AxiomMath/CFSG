module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLBlocks

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd commute_signMat_iff)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (two_ne_zero_of_unitary quatBlock_uBlock
  quatBlock_prSLHom)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (hu : UnitaryFieldData p f K) {n : ℕ}

theorem uConjAut_lift (hn1 : 1 ≤ n) (A : uU hu n) (g : StatedSU n (p ^ f) K) :
    uConjAut hu hn1 A (projH _ g) = projH _ (uLift hu A 1 g) := by
  have e := uLift_proj hu hn1 A 1 g
  rwa [map_one, mul_one] at e

theorem mem_fixOf_uLift_uSign (h2 : (2 : K) ≠ 0) {J : Finset (Fin n)}
    {g : StatedSU n (p ^ f) K} :
    g ∈ fixOf (uLift hu (uSign hu J) 1) ↔
      compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J := by
  change uLift hu (uSign hu J) 1 g = g ↔ _
  rw [uLift_one_eq_iff, coe_uSign, commute_signMat_iff h2 J]

variable [Finite K]

theorem noL2At_uSign (hp2 : p ≠ 2) (hn1 : 1 ≤ n) {J : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ J) (hb : b ∉ J) : NoL2At (uConjAut hu hn1 (uSign hu J)) := by
  have h2 := two_ne_zero_of_unitary hu hp2
  obtain ⟨F, _, _, hF, ⟨e₂⟩⟩ := C.exists_statedSU_two_equiv hu
  have hZ := scalars_subgroupOf_le_center (H := StatedSU n (p ^ f) K)
  have hle : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      uBlock p f K I ≤ fixOf (uLift hu (uSign hu J) 1) := fun hI g hg =>
    (mem_fixOf_uLift_uSign hu h2).2
      (commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg))
  have hnorm : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      ∀ B ∈ fixOf (uLift hu (uSign hu J) 1), ∀ g ∈ uBlock p f K I,
        B * g * B⁻¹ ∈ uBlock p f K I := by
    intro I hI B hB g hg
    have hBI : compInd K I * ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I :=
      commute_compInd_of_or hI ((mem_fixOf_uLift_uSign hu h2).1 hB)
    refine conj_mem_uBlock (D := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Di := (((B⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      ?_ ?_ hBI hg rfl
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have haJ : a ∉ Jᶜ := by simpa using ha
  refine noL2At_of_fix_blocks hZ (uConjAut_lift hu hn1 _) (hle (Or.inl rfl)) (hle (Or.inr rfl))
    (hnorm (Or.inl rfl)) (hnorm (Or.inr rfl)) ?_ (quatBlock_uBlock hu hp2 hF e₂ hb)
    (quatBlock_uBlock hu hp2 hF e₂ haJ)
  exact C.commutator_le_uBlock_sup hu J fun g hg => ((mem_fixOf_uLift_uSign hu h2).1 hg).symm

theorem noL2At_uPairA (hp2 : p ≠ 2) {m : ℕ} (hm : 3 ≤ m) (hn1 : 1 ≤ m + m) {l : K}
    (hl : l ≠ 0) (hN : hu.norm l = -1) :
    NoL2At (uConjAut hu hn1 (uPairA (m := m) hu (two_ne_zero_of_unitary hu hp2) hl hN)) := by
  have h2 := two_ne_zero_of_unitary hu hp2
  have hZ := scalars_subgroupOf_le_center (H := StatedSU (m + m) (p ^ f) K)
  set A := uPairA (m := m) hu h2 hl hN with hA
  set L₀ := (prSLHom (m := m) hu h2 hl hN).range with hL₀
  have hcent : ∀ g : StatedSU (m + m) (p ^ f) K, g ∈ fixOf (uLift hu A 1) ↔
      prA m l * ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        ((g : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) * prA m l := by
    intro g
    change uLift hu A 1 g = g ↔ _
    rw [uLift_one_eq_iff, hA, coe_uPairA]
  have hLF : L₀ ≤ fixOf (uLift hu A 1) := by
    rintro _ ⟨G, rfl⟩
    rw [hcent, coe_prSLHom]
    exact prPhi_commute_prA h2 hl _ _
  have hcomm : ⁅fixOf (uLift hu A 1), fixOf (uLift hu A 1)⁆ ≤ L₀ := by
    rw [commutator_le]
    intro g hg h hh
    have hgh : ⁅g, h⁆ ∈ fixOf (uLift hu A 1) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
    refine mem_range_prSLHom hu h2 hl hN ((hcent _).1 hgh) ?_
    have hblk : ∀ {u : StatedSU (m + m) (p ^ f) K}, u ∈ fixOf (uLift hu A 1) →
        ∃ G G' : Matrix (Fin m) (Fin m) K,
          prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
            fromBlocks G 0 0 G' := by
      intro u hu'
      obtain ⟨G, G', hG⟩ := exists_prPhi_of_commute h2 hl ((hcent u).1 hu').symm
      exact ⟨G, G', by rw [hG, prEv_prPhi h2 hl]⟩
    obtain ⟨G₁, G₁', e₁⟩ := hblk hg
    obtain ⟨G₂, G₂', e₂⟩ := hblk hh
    obtain ⟨G₃, G₃', e₃⟩ := hblk (inv_mem hg)
    obtain ⟨G₄, G₄', e₄⟩ := hblk (inv_mem hh)
    have hinv : ∀ {u : StatedSU (m + m) (p ^ f) K} {G G' H H' : Matrix (Fin m) (Fin m) K},
        prEv m l ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
          fromBlocks G 0 0 G' →
        prEv m l (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) = fromBlocks H 0 0 H' → G * H = 1 := by
      intro u G G' H H' eG eH
      have e1 : ((u : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) *
          (((u⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) :
            Matrix (Fin (m + m)) (Fin (m + m)) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one]
      have := congrArg (prEv m l) e1
      rw [prEv_mul h2 hl, eG, eH, prEv_one h2 hl, fromBlocks_multiply, ← fromBlocks_one] at this
      simpa using (fromBlocks_inj.1 this).1
    have h13 := hinv e₁ e₃
    have h24 := hinv e₂ e₄
    have hm4 : ((⁅g, h⁆ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) =
        (g : GL (Fin (m + m)) K) * (h : GL (Fin (m + m)) K) *
          ((g⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) *
          ((h⁻¹ : StatedSU (m + m) (p ^ f) K) : GL (Fin (m + m)) K) := by
      rw [commutatorElement_def]
      rfl
    rw [hm4, Units.val_mul, Units.val_mul, Units.val_mul, prEv_mul h2 hl, prEv_mul h2 hl,
      prEv_mul h2 hl, e₁, e₂, e₃, e₄]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      toBlocks_fromBlocks₁₁, det_mul]
    have d13 : G₁.det * G₃.det = 1 := by rw [← det_mul, h13, det_one]
    have d24 : G₂.det * G₄.det = 1 := by rw [← det_mul, h24, det_one]
    linear_combination G₂.det * G₄.det * d13 + d24
  exact noL2At_of_fix_layer hZ (uConjAut_lift hu hn1 A) hLF hcomm
    (quatBlock_prSLHom hu hp2 hl hN hm)

omit [Finite K] in
theorem noL2At_uConjAut (hp2 : p ≠ 2) (hn : 6 ≤ n) {A : uU hu n}
    (hA : orderOf (uConjAut hu (by omega) A) = 2) : NoL2At (uConjAut hu (by omega) A) := by
  have := hu.finite
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 := two_ne_zero_of_unitary hu hp2
  have hn1 : 1 ≤ n := by omega
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map hu.bar)ᵀ * Am = 1 := (mem_uU hu).1 A.2
  have hsq : uConjAut hu hn1 (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff hu (by omega) _).1 hsq
  have hAA : Am * Am = (c : K) • 1 := by
    have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at e
    rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hN : hu.norm (c : K) = 1 := by
    have e : ((Am * Am).map hu.bar)ᵀ * (Am * Am) = 1 := by
      rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
        Matrix.one_mul, hU]
    rw [hAA] at e
    have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp [Matrix.mul_apply, Matrix.one_apply] at e1
    rw [UnitaryFieldData.norm, mul_comm]
    simpa [Matrix.smul_apply, Matrix.one_apply] using e1
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one hu hp2 hN
  have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
  have hNl : hu.norm l * hu.norm l = 1 := by
    rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
    ring
  have hA'2 : (l⁻¹ • Am) * (l⁻¹ • Am) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  have hmap : (l⁻¹ • Am).map hu.bar = hu.bar l⁻¹ • Am.map hu.bar := by
    ext i j
    simp [map_mul]
  have he : Am = l • (l⁻¹ • Am) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have htr : ∀ (Hm : Matrix (Fin n) (Fin n) K) (hHU : (Hm.map hu.bar)ᵀ * Hm = 1)
      (A' : uU hu n) {c' : K}, c' ≠ 0 →
      (Hm.map hu.bar)ᵀ * Am * Hm = c' • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      NoL2At (uConjAut hu hn1 A') → NoL2At (uConjAut hu hn1 A) := by
    intro Hm hHU A' c' hc' hconj h'
    set H : uU hu n := ⟨uGL hu Hm hHU, uGL_mem hu _ _⟩ with hH
    refine NoL2At.of_conj (uConjAut hu hn1 H)⁻¹ ?_
    have e : (uConjAut hu hn1 H)⁻¹ * uConjAut hu hn1 A * (uConjAut hu hn1 H)⁻¹⁻¹ =
        uConjAut hu hn1 A' := by
      rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
      refine uConjAut_eq_of_eq_smul hu (by omega) hc' ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
      exact hconj
    rw [e]
    exact h'
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = 1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
    obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form hu h2 hU' hA'2
    have hconj : (Hm.map hu.bar)ᵀ * Am * Hm = l • signMat K J := by
      rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
        Matrix.one_mul]
    have hHH : Hm * (Hm.map hu.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
    have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
        by_cases hne : J.Nonempty
        · obtain ⟨a, ha⟩ := hne
          refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hcon a ha i]
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          refine ⟨1, one_ne_zero, ?_⟩
          ext i j
          simp [signMat, diagonal_apply, one_apply, hne]
      have e : Am = (l * s) • 1 := by
        calc Am = Hm * ((Hm.map hu.bar)ᵀ * Am * Hm) * (Hm.map hu.bar)ᵀ := by
              simp only [← Matrix.mul_assoc, hHH, Matrix.one_mul]
              rw [Matrix.mul_assoc, hHH, Matrix.mul_one]
          _ = (l * s) • 1 := by
              rw [hconj, hsJ, smul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
      have h1 : uConjAut hu hn1 A = 1 := by
        refine (uConjAut_eq_one_iff hu (by omega) A).2 ⟨Units.mk0 (l * s) (mul_ne_zero hl0 hs),
          Units.ext ?_⟩
        rw [GeneralLinearGroup.coe_scalar]
        change Am = _
        rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        rfl
      rw [h1, orderOf_one] at hA
      exact absurd hA (by norm_num)
    obtain ⟨a, ha, b, hb⟩ := hJ
    exact htr Hm hHU (uSign hu J) hl0 (by rw [hconj, coe_uSign]) (noL2At_uSign hu hp2 hn1 ha hb)
  ·
    have hNi : hu.bar l⁻¹ * l⁻¹ = -1 := by
      rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN1, inv_neg, inv_one]
    have hU' : ((l⁻¹ • Am).map hu.bar)ᵀ * (l⁻¹ • Am) = -1 := by
      rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi,
        neg_one_smul]
    obtain ⟨m', rfl⟩ := exists_half_of_antiunitary hu h2 hU' hA'2
    have hm : 3 ≤ m' := by omega
    obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form hu h2 hU' hA'2 hl0 hN1
    refine htr Hm hHU (uPairA (m := m') hu h2 hl0 hN1) one_ne_zero ?_
      (noL2At_uPairA hu hp2 hm hn1 hl0 hN1)
    rw [coe_uPairA, one_smul, he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA,
      ← Matrix.mul_assoc, hHU, Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]

end CFSG.ComponentClassification.Burgoyne.Cl
