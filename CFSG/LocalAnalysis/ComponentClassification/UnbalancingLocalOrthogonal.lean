module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace OrthogonalExclusion

open OrthogonalBlocks OrthogonalBlocks.HypForm LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {r : ℕ} {M : Type} [Fintype M] [DecidableEq M]

theorem commutator_mem_omega (F : HypForm r M K) {g h : GL (Fin r ⊕ M) K}
    (hg : ∀ v, F.Q ((g : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ v) = F.Q v)
    (hh : ∀ v, F.Q ((h : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ v) = F.Q v) :
    ⁅g, h⁆ ∈ StatedOmega F.Q :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure hg) (Subgroup.subset_closure hh)

section Odd

@[expose] def diagSign : GL (Fin 2) K :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

theorem diagSign_conj_upper (a : K) :
    diagSign * SpecialLinearGroup.toGL (sl2Upper K a) * diagSign⁻¹ =
      SpecialLinearGroup.toGL (sl2Upper K (-a)) := by
  apply Units.ext
  simp only [Units.val_mul, diagSign, Units.inv_mk, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_sl2Upper]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem diagSign_conj_lower (a : K) :
    diagSign * SpecialLinearGroup.toGL (sl2Lower K a) * diagSign⁻¹ =
      SpecialLinearGroup.toGL (sl2Lower K (-a)) := by
  apply Units.ext
  simp only [Units.val_mul, diagSign, Units.inv_mk, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_sl2Lower]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

theorem commutator_diagSign_upper (h2 : (2 : K) ≠ 0) (c : K) :
    ⁅(diagSign : GL (Fin 2) K), SpecialLinearGroup.toGL (sl2Upper K (-(c / 2)))⁆ =
      SpecialLinearGroup.toGL (sl2Upper K c) := by
  have : NeZero (2 : K) := ⟨h2⟩
  rw [commutatorElement_def, diagSign_conj_upper, ← map_inv, ← map_mul, ← sl2Upper_neg,
    ← sl2Upper_add, neg_neg, add_halves]

theorem commutator_diagSign_lower (h2 : (2 : K) ≠ 0) (c : K) :
    ⁅(diagSign : GL (Fin 2) K), SpecialLinearGroup.toGL (sl2Lower K (-(c / 2)))⁆ =
      SpecialLinearGroup.toGL (sl2Lower K c) := by
  have : NeZero (2 : K) := ⟨h2⟩
  rw [commutatorElement_def, diagSign_conj_lower, ← map_inv, ← map_mul, ← sl2Lower_neg,
    ← sl2Lower_add, neg_neg, add_halves]

@[expose] def embEquiv (hr : 2 ≤ r) : Fin 2 ⊕ Fin (r - 2) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

@[expose] def embGL (hr : 2 ≤ r) : GL (Fin 2) K →* GL (Fin r) K :=
  (Units.map (reindexAlgEquiv K K (embEquiv hr)).toRingEquiv.toMonoidHom).comp
    (blockDiagHom (MonoidHom.id _) 1)

theorem embGL_apply (hr : 2 ≤ r) (g : GL (Fin 2) K) (a b : Fin 2 ⊕ Fin (r - 2)) :
    (embGL hr g : Matrix (Fin r) (Fin r) K) (embEquiv hr a) (embEquiv hr b) =
      fromBlocks (g : Matrix (Fin 2) (Fin 2) K) 0 0 1 a b := by
  simp [embGL, reindex_apply, coe_blockDiagHom]

variable (F : HypForm r M K)

@[expose] def sl2Hom (hr : 2 ≤ r) : SL(2, K) →* GL (Fin r ⊕ M) K :=
  (F.rho.comp (embGL hr)).comp SpecialLinearGroup.toGL

theorem sl2Hom_mem_omega (hr : 2 ≤ r) (h2 : (2 : K) ≠ 0) (s : SL(2, K)) :
    sl2Hom F hr s ∈ StatedOmega F.Q := by
  have hs : s ∈ Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) := by
    rw [sl2_closure_upper_lower]
    exact Subgroup.mem_top s
  have hiso : ∀ g : GL (Fin 2) K, ∀ v,
      F.Q (((F.rho.comp (embGL hr)) g : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) *ᵥ v) = F.Q v :=
    fun g => F.rho_isometry _
  have hle : Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)) ≤
      (StatedOmega F.Q).comap (sl2Hom F hr) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change (F.rho.comp (embGL hr)) (SpecialLinearGroup.toGL (sl2Upper K c)) ∈ StatedOmega F.Q
      rw [← commutator_diagSign_upper h2 c, map_commutatorElement]
      exact commutator_mem_omega F (hiso _) (hiso _)
    · change (F.rho.comp (embGL hr)) (SpecialLinearGroup.toGL (sl2Lower K c)) ∈ StatedOmega F.Q
      rw [← commutator_diagSign_lower h2 c, map_commutatorElement]
      exact commutator_mem_omega F (hiso _) (hiso _)
  exact hle hs

theorem exists_sl2_hom_omega (hr : 3 ≤ r) (hK : ringChar K ≠ 2) :
    ∃ φ : SL(2, K) →* StatedProj (StatedOmega F.Q), φ (-1) ≠ 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hr2 : 2 ≤ r := by omega
  refine ⟨(QuotientGroup.mk' _).comp ((sl2Hom F hr2).codRestrict _
    (sl2Hom_mem_omega F hr2 h2)), fun h => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hc' : (sl2Hom F hr2 (-1) : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) = scalar _ (c : K) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  have hentry : ∀ a : Fin 2 ⊕ Fin (r - 2),
      (sl2Hom F hr2 (-1) : Matrix (Fin r ⊕ M) (Fin r ⊕ M) K) (Sum.inl (embEquiv hr2 a))
        (Sum.inl (embEquiv hr2 a)) =
      fromBlocks ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 1 a a := by
    intro a
    simp only [sl2Hom, MonoidHom.comp_apply, coe_rho, fromBlocks_apply₁₁, embGL_apply,
      SpecialLinearGroup.coe_GL_coe_matrix]
  have hneg : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := rfl
  have h0 := hentry (Sum.inl 0)
  have h1 := hentry (Sum.inr ⟨0, by omega⟩)
  rw [hc', hneg] at h0 h1
  simp only [scalar_apply, diagonal_apply_eq, fromBlocks_apply₁₁, fromBlocks_apply₂₂,
    Matrix.neg_apply, one_apply_eq] at h0 h1
  apply h2
  linear_combination h0 - h1

end Odd

section Two

@[expose] def symMat (i j : Fin r) : Matrix (Fin r) (Fin r) K :=
  single i j 1 + single j i 1

@[expose] def transvGL {i h : Fin r} (hih : i ≠ h) : GL (Fin r) K :=
  ⟨1 + single i h 1, 1 - single i h 1,
    by rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      single_mul_single_of_ne _ _ _ _ hih.symm]; abel,
    by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      single_mul_single_of_ne _ _ _ _ hih.symm]; abel⟩

theorem transvGL_symMat {i j h : Fin r} (hih : i ≠ h) (hjh : j ≠ h) (u : K) :
    ((transvGL hih : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (u • symMat h j) *
        ((transvGL hih : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ - u • symMat h j =
      u • symMat i j := by
  have e1 : single i h (1 : K) * single h j 1 = single i j 1 := by
    rw [single_mul_single_same, mul_one]
  have e2 : single i h (1 : K) * single j h 1 = 0 := single_mul_single_of_ne _ _ _ _ hjh.symm _
  have e3 : single h j (1 : K) * single h i 1 = 0 := single_mul_single_of_ne _ _ _ _ hjh _
  have e4 : single j h (1 : K) * single h i 1 = single j i 1 := by
    rw [single_mul_single_same, mul_one]
  have e5 : single i j (1 : K) * single h i 1 = 0 := single_mul_single_of_ne _ _ _ _ hjh _
  simp only [transvGL, symMat, Units.val_mk, transpose_add, transpose_one, transpose_single,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, e1, e2, e3, e4, e5, add_zero]
  module

theorem symMat_mulVec_dotProduct (h2 : (2 : K) = 0) (i j : Fin r) (u : K) (z : Fin r → K) :
    ((u • symMat i j) *ᵥ z) ⬝ᵥ z = 0 := by
  simp only [symMat, smul_add, Matrix.add_mulVec, add_dotProduct, Matrix.smul_mulVec,
    single_mulVec, smul_dotProduct]
  simp only [dotProduct, Function.update_apply, Pi.zero_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_mul]
  linear_combination u * z i * z j * h2

variable (F : HypForm r M K)

theorem tau_symMat_mem_omega (h2 : (2 : K) = 0) {i j h : Fin r} (hih : i ≠ h) (hjh : j ≠ h)
    (u : K) : F.tau (u • symMat i j) ∈ StatedOmega F.Q := by
  rw [← transvGL_symMat hih hjh u, ← F.commutator_rho_tau]
  exact commutator_mem_omega F (F.rho_isometry _)
    (F.tau_isometry (symMat_mulVec_dotProduct h2 h j u))

@[expose] def bMat (hr : 3 ≤ r) (c : Fin 3 → K) : Matrix (Fin r) (Fin r) K :=
  c 0 • symMat ⟨0, by omega⟩ ⟨1, by omega⟩ + c 1 • symMat ⟨0, by omega⟩ ⟨2, by omega⟩ +
    c 2 • symMat ⟨1, by omega⟩ ⟨2, by omega⟩

theorem bMat_zero (hr : 3 ≤ r) : bMat (K := K) hr 0 = 0 := by
  simp [bMat]

theorem bMat_add (hr : 3 ≤ r) (c d : Fin 3 → K) : bMat hr (c + d) = bMat hr c + bMat hr d := by
  simp only [bMat, Pi.add_apply, add_smul]
  abel

theorem bMat_injective (hr : 3 ≤ r) : Function.Injective (bMat (K := K) hr) := by
  intro c d h
  have e : ∀ (a b : ℕ) (ha : a < r) (hb : b < r),
      bMat hr c ⟨a, ha⟩ ⟨b, hb⟩ = bMat hr d ⟨a, ha⟩ ⟨b, hb⟩ := fun a b ha hb => by rw [h]
  have h01 := e 0 1 (by omega) (by omega)
  have h02 := e 0 2 (by omega) (by omega)
  have h12 := e 1 2 (by omega) (by omega)
  simp [bMat, symMat, Fin.ext_iff] at h01 h02 h12
  funext k
  fin_cases k
  · exact h01
  · exact h02
  · exact h12

@[expose] def bHom (hr : 3 ≤ r) : Multiplicative (Fin 3 → K) →* GL (Fin r ⊕ M) K :=
  SectionRank.ClassicalOdd.glOfAdd (fun c => (F.tau (bMat hr c) : Matrix _ _ K))
    (by rw [bMat_zero, tau_zero, Units.val_one])
    (fun c d => by rw [bMat_add, ← tau_mul, Units.val_mul])

theorem bHom_apply (hr : 3 ≤ r) (c : Multiplicative (Fin 3 → K)) :
    bHom F hr c = F.tau (bMat hr c.toAdd) :=
  Units.ext rfl

theorem bHom_injective (hr : 3 ≤ r) : Function.Injective (bHom F hr) :=
  SectionRank.ClassicalOdd.glOfAdd_injective fun _ _ h =>
    bMat_injective hr (F.tau_injective (Units.ext h))

theorem bHom_mem_omega (hr : 3 ≤ r) (h2 : (2 : K) = 0) (c : Multiplicative (Fin 3 → K)) :
    bHom F hr c ∈ StatedOmega F.Q := by
  rw [bHom_apply, bMat, ← tau_mul, ← tau_mul]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact tau_symMat_mem_omega F h2 (h := ⟨2, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) _
  · exact tau_symMat_mem_omega F h2 (h := ⟨1, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) _
  · exact tau_symMat_mem_omega F h2 (h := ⟨0, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) _

theorem three_mul_le_pRank_omega [Finite K] [CharP K 2] (hr : 3 ≤ r) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    f * 3 ≤ Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedOmega F.Q))) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine SectionRank.ClassicalOdd.le_pRank_statedProj one_lt_two
    SectionRank.ClassicalOdd.multiplicative_comm
    (SectionRank.ClassicalOdd.pow_char_eq_one (K := K)) ?_ (bHom F hr) (bHom_injective F hr)
    (bHom_mem_omega F hr h2) (v := Sum.elim (Pi.single ⟨0, by omega⟩ 1) 0) ?_ ?_
  · rw [SectionRank.ClassicalOdd.card_multiplicative_fun hK, Fintype.card_fin]
  · intro hv
    have := congrFun hv (Sum.inl ⟨0, by omega⟩)
    simp at this
  · intro c
    rw [bHom_apply]
    exact F.tau_mulVec_inl _ _

end Two

theorem hypForm_exclusion {T : Type} [Group T] [Finite K] (F : HypForm r M K) (hr : 3 ≤ r)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {Q₀ : (Fin r ⊕ M → K) → K} (hQ : Q₀ = F.Q) (eT : T ≃* StatedProj (StatedOmega Q₀)) (s : ℕ)
    (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  subst hQ
  rintro ⟨eP⟩
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    ComponentClassification.SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs
      ⟨P, ⟨eP⟩⟩
  have hchar : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := three_mul_le_pRank_omega F hr hK
    rw [← SectionRank.pRank_top_eq_of_mulEquiv one_lt_two eT, ←
      SectionRank.pRank_eq_open_pRank_top] at hle
    omega
  ·
    have hkchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    obtain ⟨φ, hφ⟩ := exists_sl2_hom_omega F hr hkchar
    obtain ⟨H, ⟨eH⟩⟩ := UnbalancedGS.SymplecticExclusion.exists_quaternion_of_sl2_hom hkchar
      (eT.symm.toMonoidHom.comp φ) (by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Ne, map_eq_one_iff _ eT.symm.injective]
        exact hφ)
    exact hQ8 ⟨H, ⟨eH⟩⟩

theorem quadOdd_eq (n : ℕ) :
    StatedQuadOdd n K = (HypForm.tail n Unit fun w : Unit → K => w () ^ 2).Q := by
  funext v
  simp [StatedQuadOdd, HypForm.Q, HypForm.tail, dotProduct, fromCols_mulVec]

theorem quadMinus_eq (n : ℕ) (b c : K) :
    StatedQuadMinus n K b c = (HypForm.tail (n - 1) (Fin 2) fun w : Fin 2 → K =>
      w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2).Q := by
  funext v
  simp [StatedQuadMinus, HypForm.Q, HypForm.tail, dotProduct, fromCols_mulVec, add_assoc]

theorem quadPlus_eq (n : ℕ) : StatedQuadPlus n K = (HypForm.plus n).Q := by
  funext v
  simp [StatedQuadPlus, HypForm.Q, HypForm.plus, dotProduct]

end OrthogonalExclusion

open OrthogonalExclusion

theorem dihedral_sylow_orthogonal_model_exclusion {T : Type} [Group T] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hT : StatedClassicalModel T t n p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    exact hypForm_exclusion _ (by omega) hp hf hK (quadOdd_eq n) eT s hs P
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    have hn' : 4 ≤ n := hn
    exact hypForm_exclusion _ (by omega) hp hf hK (quadPlus_eq n) eT s hs P
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, -, ⟨eT⟩⟩ := hT
    have hn' : 4 ≤ n := hn
    exact hypForm_exclusion _ (by omega) hp hf hK (quadMinus_eq n b c) eT s hs P

end CFSG.ComponentClassification.UnbalancingLocal
