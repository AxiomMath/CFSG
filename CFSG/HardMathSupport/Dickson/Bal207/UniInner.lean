module

public import CFSG.HardMathSupport.Dickson.Bal207.UniBlock
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealComp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealEigen
import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Type
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Polynomial Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_apply_not_mem)

section Matrix

variable {n : ℕ} {F : Type} [Field F] (I : Finset (Fin n))

theorem uni_blockOn_mulVec_of_zero (N : Matrix (Fin I.card) (Fin I.card) F) {v : Fin n → F}
    (hv : ∀ k ∈ I, v k = 0) : blockOn F I N *ᵥ v = v := by
  funext j
  show ∑ k, blockOn F I N j k * v k = v j
  rw [Finset.sum_eq_single j]
  · by_cases hj : j ∈ I
    · rw [hv j hj, mul_zero]
    · rw [blockOn_apply_not_mem I N (Or.inl hj), if_pos rfl, one_mul]
  · intro k _ hkj
    by_cases hk : k ∈ I
    · rw [hv k hk, mul_zero]
    · rw [blockOn_apply_not_mem I N (Or.inr hk), if_neg (Ne.symm hkj), zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem uni_diag_mulVec {D : Matrix (Fin n) (Fin n) F} (hD : D.IsDiag) (v : Fin n → F)
    (j : Fin n) : (D *ᵥ v) j = D j j * v j := by
  conv_lhs => rw [← hD.diagonal_diag]
  rw [mulVec_diagonal]
  rfl

end Matrix

section Eigen

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_toLin_apply (D : primeFormUnitary h (oneGram F n)) (v : Fin n → F) :
    ((t6psub_toLin D : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) v = ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := rfl

theorem uni_toLinSU_apply (g : gramSU h (oneGram F n)) (v : Fin n → F) :
    ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) v = ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := rfl

theorem uni_mem_V_iff (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (d : F) (v : Fin n → F) :
    v ∈ primaryComponent ((t6psub_toLin D : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) (X - C d) ↔
      ∀ j, ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j * v j = d * v j := by
  rw [u6r_mem_primaryComponent_iff, uni_toLin_apply, funext_iff]
  refine forall_congr' fun j => ?_
  rw [uni_diag_mulVec hD, Pi.smul_apply, smul_eq_mul]

theorem uni_single_mem_V (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (k : Fin n) :
    Pi.single k (1 : F) ∈ primaryComponent ((t6psub_toLin D :
        LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F))
      (X - C (((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k)) := by
  rw [uni_mem_V_iff D hD]
  intro j
  by_cases hjk : j = k
  · rw [hjk]
  · rw [Pi.single_eq_of_ne hjk, mul_zero, mul_zero]

theorem uni_single_ne_zero (k : Fin n) : (Pi.single k (1 : F) : Fin n → F) ≠ 0 :=
  fun h0 => one_ne_zero (Pi.single_eq_zero_iff.1 h0)

variable (h) in
theorem uni_idForm_single (j : Fin n) (v : Fin n → F) :
    idForm h n (Pi.single j 1) v = v j := by
  have e : (fun a => h.bar ((Pi.single j (1 : F) : Fin n → F) a)) = Pi.single j 1 := by
    funext a
    by_cases haj : a = j
    · subst haj
      rw [Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne haj, map_zero]
  show (fun a => h.bar ((Pi.single j (1 : F) : Fin n → F) a)) ⬝ᵥ
    (((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) = v j
  rw [e, Units.val_one, one_mulVec, single_dotProduct, one_mul]

theorem uni_conjHom_eq_one_of_const (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) {d : F}
    (hdj : ∀ j, ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d) :
    primeFormConjHom h (oneGram F n) D = 1 := by
  have hcomm : ∀ g : GL (Fin n) F, (D : GL (Fin n) F) * g = g * D := fun g => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hD.diagonal_diag]
    ext j k
    rw [diagonal_mul, mul_diagonal, diag_apply, diag_apply, hdj, hdj, mul_comm]
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change (D : GL (Fin n) F) * (g : GL (Fin n) F) * (D : GL (Fin n) F)⁻¹ = g
  rw [hcomm, mul_inv_cancel_right]

end Eigen

section Special

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_mem_specialBlock (hf : Odd f) (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag)
    (hD3 : (D : GL (Fin n) F) ^ 3 = 1) {d : F} (hd : d ^ 3 = 1)
    (hdD : X - C d ∈ primaryFactors ((t6psub_toLin D :
      LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)))
    {I : Finset (Fin n)} (hI : ∀ j, j ∈ I ↔ ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d)
    (M : primeFormUnitary h (oneGram F I.card)) (g : gramSU h (oneGram F n))
    (hg : (g : GL (Fin n) F) = uniBlk h I M) :
    t6psuh_toLinSU h n g ∈ specialBlock (idForm h n) (t6psub_toLin D) (X - C d) := by
  have H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin D) :=
    t6psuh_primaryData_toLin' h D.2 Nat.prime_three (by norm_num) (c := 1)
      (by rw [hD3, map_one])
  have hgM : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      blockOn F I ((M : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F) := by
    rw [hg, coe_uniBlk]
  have hcGL : (g : GL (Fin n) F) * (D : GL (Fin n) F) = (D : GL (Fin n) F) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hgM, ← hD.diagonal_diag]
    refine (uni_diagonal_commute_blockOn I (fun j hj k hk => ?_) _).symm
    rw [diag_apply, diag_apply, (hI j).1 hj, (hI k).1 hk]
  have hcomm : Commute ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) ((t6psub_toLin D : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) := by
    have e : t6psuh_toLinSU h n g * t6psub_toLin D = t6psub_toLin D * t6psuh_toLinSU h n g := by
      rw [t6psuh_toLinSU_apply, t6psub_toLin, ← map_mul, ← map_mul, hcGL]
    exact (commute_iff_eq _ _).2 (congrArg Units.val e)
  have hid : ∀ v : Fin n → F, (∀ w ∈ primaryComponent ((t6psub_toLin D :
      LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) (X - C d),
        idForm h n w v = 0) →
      ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) v = v := by
    intro v hv
    have hvI : ∀ k ∈ I, v k = 0 := fun k hk => by
      have hmem := uni_single_mem_V D hD k
      rw [(hI k).1 hk] at hmem
      rw [← uni_idForm_single h k v]
      exact hv _ hmem
    rw [uni_toLinSU_apply, hgM]
    exact uni_blockOn_mulVec_of_zero I _ hvI
  have hdet : LinearMap.det ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) = 1 := by
    have e : ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) =
          Matrix.toLin' ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      (Matrix.toLin'_apply' _).symm
    rw [e, LinearMap.det_toLin']
    exact g.2.2
  exact KCUnitaryBlock.mem_specialBlock_of_degree_one H (u6r_bar_mul_self h hf hd) hdD
    (sesqSpecialUnitaryGroup_le _ (t6psuh_toLinSU_mem_sesqSpecialUnitaryGroup g)) hcomm hid hdet

theorem uni_exists_uniBlk_of_mem (hf : Odd f) (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) {d : F} (hd : d ^ 3 = 1)
    {I : Finset (Fin n)} (hI : ∀ j, j ∈ I ↔ ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d)
    {g : gramSU h (oneGram F n)}
    (hg : t6psuh_toLinSU h n g ∈ specialBlock (idForm h n) (t6psub_toLin D) (X - C d)) :
    ∃ M : primeFormUnitary h (oneGram F I.card), M ∈ blockSU h I.card ∧
      ((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) = g := by
  have hsup := (specialBlock_le_orbitFactor hg).2
  rw [u6r_dualPoly h hf hd] at hsup
  have hcomm : Commute ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) ((t6psub_toLin D : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) :=
    mem_gl_centralizer.mp (specialBlock_le_orbitFactor hg).1.2
  have hent : ∀ j k, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j k =
      ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) (Pi.single k 1) j := by
    intro j k
    rw [uni_toLinSU_apply, mulVec_single_one]
    rfl
  have hoff : ∀ j k, (j ∉ I ∨ k ∉ I) →
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j k = if j = k then 1 else 0 := by
    intro j k hjk
    by_cases hk : k ∈ I
    ·
      have hj : j ∉ I := hjk.resolve_right (not_not.2 hk)
      have hj' : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j ≠ d := fun h' =>
        hj ((hI j).2 h')
      have hmem := uni_single_mem_V D hD k
      rw [(hI k).1 hk] at hmem
      have hw := (uni_mem_V_iff D hD d _).1 (apply_mem_primaryComponent hcomm hmem) j
      have hjk' : j ≠ k := fun h' => hj (h' ▸ hk)
      rw [hent, if_neg hjk']
      have h2 : (((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j - d) *
          ((t6psuh_toLinSU h n g : LinearMap.GeneralLinearGroup F (Fin n → F)) :
            Module.End F (Fin n → F)) (Pi.single k 1) j = 0 := by
        rw [sub_mul, hw, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hj')
    ·
      have hk' : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k ≠ d := fun h' =>
        hk ((hI k).2 h')
      have hmem := uni_single_mem_V D hD k
      have hfix := hsup _ (u6r_mem_primaryFactors D hmem (uni_single_ne_zero k)) (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self]
        exact fun h' => hk' (C_injective (sub_right_injective h'))) _ hmem
      rw [hent, hfix, Pi.single_apply]
  obtain ⟨M, hM⟩ := uni_exists_uniBlk h I g.2.1 hoff
  refine ⟨M, Subgroup.mem_subgroupOf.2 ⟨M.2, ?_⟩, hM⟩
  rw [← det_uniBlk h I M, hM]
  exact g.2.2

end Special

section Comp

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_block_isComponent (D : primeFormUnitary h (oneGram F n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin D)) (i : t6psub_Idx h n D) :
    CFSG.Open.IsComponentOf ((t6psub_block D i).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)))
      (fixSubgroup (primeFormConjHom h (oneGram F n) D)) := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) F) :=
    Finite.of_injective (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) Units.val_injective
  have hq := isQuasisimple_open (u6r_block_quasisimple D H i)
  have hn : (((t6psub_block D i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n))).subgroupOf
        ((fixSubgroup (t6psub_actSU h n D)).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (u6r_block_le D i)]
    exact fun x c hx hc => u6r_block_normal D i c hc x hx
  exact ⟨(u6r_block_le D i).trans (u6r_map_fix_le D),
    CFSG.Open.IsSubnormal.step (u6r_block_le D i) hn
      (CFSG.Open.IsSubnormal.step (u6r_map_fix_le D) (u6r_map_fix_normal D)
        (CFSG.Open.IsSubnormal.refl _)), hq⟩

theorem uni_perfect_le_blocks (D : primeFormUnitary h (oneGram F n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin D))
    (P : Subgroup (primeFormP h (oneGram F n)))
    (hPC : P ≤ fixSubgroup (primeFormConjHom h (oneGram F n) D)) (hP : ⁅P, P⁆ = P) :
    P ≤ ⨆ i : t6psub_Idx h n D, (t6psub_block D i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)) := by
  have hPX : P ≤ (fixSubgroup (t6psub_actSU h n D)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)) :=
    le_map_fixSubgroup_of_perfect _ u6r_ker_le_center (t6psub_actSU h n D)
      (primeFormConjHom h (oneGram F n) D) (fun x => t6psub_hact D x)
      (QuotientGroup.mk'_surjective _) hPC hP
  exact excU62_perfect_le_of_derived hPX hP (u6r_block_derived D H)

theorem uni_map_block_eq (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag)
    (hD3 : (D : GL (Fin n) F) ^ 3 = 1) (i : t6psub_Idx h n D) {d : F} (hd : d ^ 3 = 1)
    (hid : (i.1 : F[X]) = X - C d) {I : Finset (Fin n)}
    (hI : ∀ j, j ∈ I ↔ ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d) :
    (t6psub_block D i).map (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)) =
      (blockSU h I.card).map ((uniTheta h hf hn h3).comp (uniBlk h I)) := by
  have hfo : Odd f := by rcases hf with rfl | rfl <;> decide
  have hdD : X - C d ∈ primaryFactors ((t6psub_toLin D :
      LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) := hid ▸ i.1.2
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : t6psuh_toLinSU h n g ∈ specialBlock (idForm h n) (t6psub_toLin D) (X - C d) := by
      rw [← hid]
      exact Subgroup.mem_comap.mp hg
    obtain ⟨M, hM, hMg⟩ := uni_exists_uniBlk_of_mem hfo D hD hd hI hg'
    refine ⟨M, hM, ?_⟩
    rw [MonoidHom.comp_apply,
      show uniBlk h I M = ⟨(g : GL (Fin n) F), g.2.1⟩ from Subtype.ext hMg]
    exact uniTheta_gramSU h hf hn h3 g
  · rintro ⟨M, hM, rfl⟩
    have hdet : (((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [det_uniBlk]
      exact (Subgroup.mem_subgroupOf.1 hM).2
    let g : gramSU h (oneGram F n) := ⟨(uniBlk h I M : GL (Fin n) F), (uniBlk h I M).2, hdet⟩
    refine ⟨g, ?_, ?_⟩
    · show t6psuh_toLinSU h n g ∈ specialBlock (idForm h n) (t6psub_toLin D) (i.1 : F[X])
      rw [hid]
      exact uni_mem_specialBlock hfo D hD hD3 hd hdD hI M g rfl
    · have e : (uniTheta h hf hn h3).comp (uniBlk h I) M = (g : primeFormP h (oneGram F n)) := by
        rw [MonoidHom.comp_apply, show uniBlk h I M = ⟨(g : GL (Fin n) F), g.2.1⟩ from rfl]
        exact uniTheta_gramSU h hf hn h3 g
      exact e.symm

theorem uni_theta_uniBlk_injective (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    {I : Finset (Fin n)} {j₀ : Fin n} (hj₀ : j₀ ∉ I) :
    Function.Injective ((uniTheta h hf hn h3).comp (uniBlk h I)) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have hM' : uniTheta h hf hn h3 (uniBlk h I M) = 1 := hM
  have h1 : primeFormConjHom h (oneGram F n) (uniBlk h I M) = 1 := by
    rw [← conj_uniTheta h hf hn h3, hM', map_one]
  have h2 : primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl (uniBlk h I M) : UniGamma h n) = 1 := by
    rw [uni_psi_inl, h1]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h uni_isPrimeFormGram_one hn _).1 h2
  have hU0 : ((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := hc
  have hc1 : c = 1 := by
    have e : (((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) j₀ j₀ =
          ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) :
            Matrix (Fin n) (Fin n) F) j₀ j₀ := by rw [hU0]
    rw [uniBlk_apply_off h I M (Or.inl hj₀), if_pos rfl, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, diagonal_apply_eq] at e
    exact Units.val_eq_one.mp e.symm
  apply uniBlk_injective h I
  rw [map_one]
  apply Subtype.ext
  rw [hU0, hc1, map_one, Subgroup.coe_one]

theorem uni_inner_component (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    (hD1 : primeFormConjHom h (oneGram F n) D ≠ 1) {L : Subgroup (primeFormP h (oneGram F n))}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup (primeFormConjHom h (oneGram F n) D))) :
    ∃ I : Finset (Fin n), (∃ j, j ∉ I) ∧ (∃ j, j ∈ I) ∧
      L = (blockSU h I.card).map ((uniTheta h hf hn h3).comp (uniBlk h I)) := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin n) F) :=
    Finite.of_injective (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) Units.val_injective
  have hD3' : (D : GL (Fin n) F) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hD3, Subgroup.coe_one]
  have H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin D) :=
    t6psuh_primaryData_toLin' h D.2 Nat.prime_three (by norm_num) (c := 1)
      (by rw [hD3', map_one])
  obtain ⟨i, hi⟩ := LieComp.component_mem_named_factors
    (fun i : t6psub_Idx h n D => (t6psub_block D i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (oneGram F n)) n)))
    (fun i => uni_block_isComponent D H i)
    (fun P hPC hP => uni_perfect_le_blocks D H P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hL
  obtain ⟨d, hd, hid⟩ := u6r_primaryFactor_eq D hD3' i.1.2
  set I : Finset (Fin n) := Finset.univ.filter
    fun j => ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d with hIdef
  have hI : ∀ j, j ∈ I ↔ ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = d := fun j => by
    rw [hIdef, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ j)
  refine ⟨I, ?_, ?_, hi.trans (uni_map_block_eq hf hn h3 D hD hD3' i hd hid hI)⟩
  · by_contra hall
    push Not at hall
    exact hD1 (uni_conjHom_eq_one_of_const D hD fun j => (hI j).1 (hall j))
  · have hdD : X - C d ∈ primaryFactors ((t6psub_toLin D :
        LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F)) := hid ▸ i.1.2
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot (u6r_squarefree D hD3') hdD)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    have hj' : v j ≠ 0 := hj
    exact ⟨j, (hI j).2 (mul_right_cancel₀ hj' ((uni_mem_V_iff D hD d v).1 hv j))⟩

end Comp

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
