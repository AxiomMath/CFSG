module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallMixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

section Outer

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sp_conjAut_mem_inner [NeZero r] (A : SymplecticHigher.gsp r K) :
    SymplecticHigher.conjAut r K A ∈ inner (StatedProj (StatedSp r K)) := by
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨SymplecticFlag.proj r K s, ?_⟩
  rw [hs]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) x
  rw [MulAut.conj_apply, SymplecticHigher.conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem statedSp_outer_comm (hr : 3 ≤ r) (a b : Outer (StatedProj (StatedSp r K))) :
    a * b = b * a := by
  have : NeZero r := ⟨by omega⟩
  have key : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ σ : K ≃+* K,
      (α : Outer (StatedProj (StatedSp r K))) = (SymplecticHigher.fieldAut r K σ : _) := by
    intro α
    obtain ⟨A, σ, hα⟩ := (SymplecticHigher.automorphism_generation (r := r) (K := K) hr).2 α
    refine ⟨σ, ?_⟩
    rw [hα, QuotientGroup.mk_mul]
    have h1 : ((SymplecticHigher.conjAut r K A : MulAut (StatedProj (StatedSp r K))) :
        Outer (StatedProj (StatedSp r K))) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (sp_conjAut_mem_inner A)
    rw [h1, one_mul]
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨σ, hσ⟩ := key α
  obtain ⟨τ, hτ⟩ := key β
  rw [hσ, hτ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← map_mul, ← map_mul,
    ringEquiv_mul_comm σ τ]

theorem statedSp_two_outer_comm {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (a b : Outer (StatedProj (StatedSp 2 K))) : a * b = b * a := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  obtain ⟨Fr, hFr, hord, hzp⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data hf hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hf hFr hord hzp
  exact hcyc.commGroup.mul_comm a b

end Outer

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem commutatorElement_mem_inner_of_mulEquiv (e : A ≃* B)
    (hB : ∀ a b : Outer B, a * b = b * a) (θ ρ : MulAut A) :
    θ * ρ * θ⁻¹ * ρ⁻¹ ∈ inner A := by
  set θ' := MulAut.congr e θ
  set ρ' := MulAut.congr e ρ
  have h1 : θ' * ρ' * θ'⁻¹ * ρ'⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner B := by
    have hc := hB (θ' : Outer B) (ρ' : Outer B)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    have hmem := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal B).conj_mem _
      (Subgroup.inv_mem _ hc) (θ' * ρ')
    have e2 : θ' * ρ' * θ'⁻¹ * ρ'⁻¹ =
        (θ' * ρ') * ((θ' * ρ')⁻¹ * (ρ' * θ'))⁻¹ * (θ' * ρ')⁻¹ := by group
    rw [e2]
    exact hmem
  obtain ⟨y, hy⟩ := h1
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [← hy]
  ext b
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Transport

section SelfRigid

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem fieldRigidIn_self_of_outer_comm (hn : 3 ≤ n) (X : Subgroup (projectiveSL n K))
    (hOut : ∀ θ ρ : MulAut X, θ * ρ * θ⁻¹ * ρ⁻¹ ∈ inner X) {i j : Fin n} (hij : i ≠ j)
    (h : projectiveSL n K)
    (hroot : ∀ c : K, h * proj n K (SpecialLinearGroup.transvection hij c) * h⁻¹ ∈ X) :
    FieldRigidIn hn X X := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hc₁ : ∀ Y : Subgroup (projectiveSL n K),
      (Y.map φ₁).map (MulAut.conj γ).toMonoidHom = (Y.map β₁.toMonoidHom).map φ₁ := by
    intro Y
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₁ x).symm
  have hc₂ : ∀ Y : Subgroup (projectiveSL n K),
      (Y.map φ₂).map (MulAut.conj γ).toMonoidHom = (Y.map β₂.toMonoidHom).map φ₂ := by
    intro Y
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₂ x).symm
  have hβ₁X : X.map β₁.toMonoidHom = X := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have hβ₂X : X.map β₂.toMonoidHom = X := by
    apply Subgroup.map_injective hφ₂
    rw [← hc₂, ← hX, hc₁, hβ₁X]
  set ρ₁ : MulAut X := (β₁.subgroupMap X).trans (MulEquiv.subgroupCongr hβ₁X) with hρ₁
  set ρ₂ : MulAut X := (β₂.subgroupMap X).trans (MulEquiv.subgroupCongr hβ₂X) with hρ₂
  have hρ₁x : ∀ x : X, ((ρ₁ x : X) : projectiveSL n K) = β₁ x := fun x => rfl
  have hρ₂x : ∀ x : X, ((ρ₂ x : X) : projectiveSL n K) = β₂ x := fun x => rfl
  set θ : MulAut X := (X.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X.equivMapOfInjective φ₂ hφ₂).symm) with hθdef
  have hθ : ∀ x : X, φ₂ (θ x : X) = φ₁ x := by
    intro x
    have h := (X.equivMapOfInjective φ₂ hφ₂).apply_symm_apply
      ((MulEquiv.subgroupCongr hX) (X.equivMapOfInjective φ₁ hφ₁ x))
    exact congrArg Subtype.val h
  have hint : ρ₂ = θ * ρ₁ * θ⁻¹ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨z, rfl⟩ := θ.surjective x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    apply Subtype.ext
    apply hφ₂
    rw [hρ₂x, h₂, hθ, hθ, hρ₁x, h₁]
  obtain ⟨y, hy⟩ := hOut θ ρ₁
  have hyx : ∀ t : X, (β₂ t : projectiveSL n K) = (y : projectiveSL n K) * β₁ t * (y : _)⁻¹ := by
    intro t
    have h1 : ρ₂ t = θ (ρ₁ (θ⁻¹ t)) := by
      rw [hint]
      rfl
    have h2 : (θ * ρ₁ * θ⁻¹ * ρ₁⁻¹) (ρ₁ t) = θ (ρ₁ (θ⁻¹ t)) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [← hy, MulAut.conj_apply] at h2
    rw [← hρ₂x, h1, ← h2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hρ₁x]
  have key := linearFieldPart_eq_of_eqOn_conj_rootGroup hn (MulAut.conj (y : projectiveSL n K) * β₁)
    β₂ hij h fun c => by
      rw [MulAut.mul_apply, MulAut.conj_apply]
      exact (hyx ⟨_, hroot c⟩).symm
  rw [map_mul, linearFieldPart_mulAut_conj, one_mul] at key
  exact key

end SelfRigid

section Alt

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem proj_transvection_mem_autFixSubgroup_blockSwap {r : ℕ} (hr : n = 2 * r) (hr1 : 1 ≤ r)
    (C : GL (Fin n) K) (hC : (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r)
    (h0r : (⟨0, by omega⟩ : Fin n) ≠ ⟨r, by omega⟩) (c : K) :
    proj n K (SpecialLinearGroup.transvection h0r c) ∈
      autFixSubgroup (conjAut n K C * dualAut n K) := by
  have hrr : r + r = n := by omega
  have hCC : C * C = 1 := Units.ext (by
    rw [Units.val_mul, hC, UnitaryHigher.blockSwapJ_mul_self hrr, Units.val_one])
  have hCinv : C⁻¹ = C := inv_eq_of_mul_eq_one_right hCC
  have htt : SpecialLinearGroup.transvection h0r c * SpecialLinearGroup.transvection h0r c = 1 :=
    InvPlacement.transvection_mul_self h0r c
  have htinv : (SpecialLinearGroup.transvection h0r c)⁻¹ = SpecialLinearGroup.transvection h0r c :=
    inv_eq_of_mul_eq_one_right htt
  rw [mem_autFixSubgroup, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, hCinv, htinv, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.transvection_coe, hC]
  change UnitaryHigher.blockSwapJ n r * (Matrix.transvection _ _ c)ᵀ *
    UnitaryHigher.blockSwapJ n r = Matrix.transvection _ _ c
  rw [transvection_transpose_eq_transvection,
    blockSwapJ_mul_transvection_mul hrr (i := ⟨r, by omega⟩) (i' := ⟨0, by omega⟩)
      (j := ⟨0, by omega⟩) (j' := ⟨r, by omega⟩) (Or.inr (by simp)) (Or.inl (by simp))]

theorem perfectCore_eq_and_nonempty_mulEquiv_blockSwap {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr2 : 2 ≤ r) (hr : n = 2 * r) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) :
    perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)) =
        autFixSubgroup (conjAut n K C * dualAut n K) ∧
      Nonempty (autFixSubgroup (conjAut n K C * dualAut n K) ≃* StatedProj (StatedSp r K)) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : NeZero r := ⟨by omega⟩
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hK
    hn C (Or.inr ⟨r, hr, hC⟩)
  set e₂ : FourGroupEvenCanonical.matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃*
      StatedSp r K := (MulEquiv.subgroupCongr
        (congrArg FourGroupEvenCanonical.matrixIsometryGroup hC)).trans
      (CFSG.ComponentClassification.OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega))
  set e₃ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective _ UnitaryHigher.proj_bijective_of_charTwo
  set X := autFixSubgroup (conjAut n K C * dualAut n K) with hX
  set e : X ≃* StatedProj (StatedSp r K) :=
    ((MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup _)).trans e₁).trans
      (e₂.trans e₃) with he
  have hne : ¬(r = 2 ∧ Nat.card K = 2) := fun h => by omega
  obtain ⟨-, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr2 hne
  have hXp : Group.IsPerfect X := by
    rw [Group.isPerfect_def, commutator_def] at hperf ⊢
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  have hcomm : ⁅X, X⁆ = X := Subgroup.commutator_eq_self
  exact ⟨le_antisymm (perfectCore_le X) (le_perfectCore_of_perfect le_rfl hcomm), ⟨e⟩⟩

theorem fieldRigidIn_graph_alt_self {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {r : ℕ} (hr3 : 3 ≤ r) (hr : n = 2 * r) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) :
    FieldRigidIn hn (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))
      (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))) := by
  obtain ⟨heq, ⟨e⟩⟩ := perfectCore_eq_and_nonempty_mulEquiv_blockSwap hK hq hn (r := r)
    (by omega) hr C hC
  rw [heq]
  have h0r : (⟨0, by omega⟩ : Fin n) ≠ ⟨r, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  exact fieldRigidIn_self_of_outer_comm hn _
    (commutatorElement_mem_inner_of_mulEquiv e (statedSp_outer_comm hr3)) h0r 1
    (fun c => by
      rw [one_mul, inv_one, mul_one]
      exact proj_transvection_mem_autFixSubgroup_blockSwap hr (by omega) C hC h0r c)

theorem fieldRigidIn_graph_alt_self' {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {r : ℕ} (hr2 : 2 ≤ r) (hr : n = 2 * r) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) :
    FieldRigidIn hn (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))
      (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))) := by
  rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
  · obtain ⟨heq, ⟨e⟩⟩ := perfectCore_eq_and_nonempty_mulEquiv_blockSwap hK hq hn (r := 2)
      le_rfl hr C hC
    rw [heq]
    have h0r : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      omega
    exact fieldRigidIn_self_of_outer_comm hn _
      (commutatorElement_mem_inner_of_mulEquiv e (statedSp_two_outer_comm hK)) h0r 1
      (fun c => by
        rw [one_mul, inv_one, mul_one]
        exact proj_transvection_mem_autFixSubgroup_blockSwap hr (by omega) C hC h0r c)
  · exact fieldRigidIn_graph_alt_self hK hq hn hr3 hr C hC

end Alt

section Nonalt

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem conj_transvection_expand {i j : Fin n} (hij : i ≠ j) (c : K) :
    ((1 : Matrix (Fin n) (Fin n) K) + single i j 1) * (1 + single j i c) * (1 + single i j 1) =
      1 + (single i i c + single i j c + single j i c + single j j c) := by
  simp only [Matrix.add_mul, Matrix.mul_add, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij.symm, mul_one, one_mul]
  have h2 : (single i j (1 : K) : Matrix (Fin n) (Fin n) K) + single i j 1 = 0 := by
    rw [← single_add, CharTwo.add_self_eq_zero, single_zero]
  have e : ∀ X B D F Y : Matrix (Fin n) (Fin n) K,
      1 + X + (B + D) + (X + 0 + (F + Y)) = 1 + (D + Y + B + F) + (X + X) := by
    intros
    abel
  rw [e, h2, add_zero]

omit [Finite K] in
theorem proj_conj_transvection_mem_autFixSubgroup_dualAut {i j : Fin n} (hij : i ≠ j) (c : K) :
    proj n K (SpecialLinearGroup.transvection hij 1) *
        proj n K (SpecialLinearGroup.transvection hij.symm c) *
          (proj n K (SpecialLinearGroup.transvection hij 1))⁻¹ ∈
      autFixSubgroup (dualAut n K) := by
  set h := SpecialLinearGroup.transvection hij (1 : K) with hh
  set t := SpecialLinearGroup.transvection hij.symm c with ht
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right (InvPlacement.transvection_mul_self hij 1)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (InvPlacement.transvection_mul_self _ c)
  rw [← map_inv, ← map_mul, ← map_mul, mem_autFixSubgroup, dualAut_proj]
  congr 1
  have hginv : (h * t * h⁻¹)⁻¹ = h * t * h⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, htinv, hhinv, mul_assoc]
  rw [hginv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, hhinv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hh, ht, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, conj_transvection_expand hij c]
  rw [transpose_add, transpose_one, transpose_add, transpose_add, transpose_add, transpose_single,
    transpose_single, transpose_single, transpose_single]
  abel

theorem perfectCore_eq_and_nonempty_mulEquiv_dualAut_odd {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr2 : 2 ≤ r) (hr : n = 2 * r + 1) :
    perfectCore (autFixSubgroup (dualAut n K)) = autFixSubgroup (dualAut n K) ∧
      Nonempty (autFixSubgroup (dualAut n K) ≃* StatedProj (StatedSp r K)) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : NeZero r := ⟨by omega⟩
  have hδ : conjAut n K 1 * dualAut n K = dualAut n K := by rw [map_one, one_mul]
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hK
    hn (1 : GL (Fin n) K) (Or.inl Units.val_one)
  rw [hδ] at e₁
  obtain ⟨e₀⟩ := CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := n))
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate hr)
    (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker hr)
  set e₂ := (CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv (k := K) hr).trans e₀
  set e₃ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective _ UnitaryHigher.proj_bijective_of_charTwo
  set X := autFixSubgroup (dualAut n K) with hX
  set e : X ≃* StatedProj (StatedSp r K) :=
    ((MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup _)).trans e₁).trans
      (e₂.trans e₃) with he
  have hne : ¬(r = 2 ∧ Nat.card K = 2) := fun h => by omega
  obtain ⟨-, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr2 hne
  have hXp : Group.IsPerfect X := by
    rw [Group.isPerfect_def, commutator_def] at hperf ⊢
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  have hcomm : ⁅X, X⁆ = X := Subgroup.commutator_eq_self
  exact ⟨le_antisymm (perfectCore_le X) (le_perfectCore_of_perfect le_rfl hcomm), ⟨e⟩⟩

theorem fieldRigidIn_graph_nonalt_self_of_odd {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr2 : 2 ≤ r) (hr : n = 2 * r + 1) :
    FieldRigidIn hn (perfectCore (autFixSubgroup (dualAut n K)))
      (perfectCore (autFixSubgroup (dualAut n K))) := by
  obtain ⟨heq, ⟨e⟩⟩ := perfectCore_eq_and_nonempty_mulEquiv_dualAut_odd hK hq hn hr2 hr
  rw [heq]
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hOut : ∀ θ ρ : MulAut (autFixSubgroup (dualAut n K)),
      θ * ρ * θ⁻¹ * ρ⁻¹ ∈ inner (autFixSubgroup (dualAut n K)) := by
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
    · exact commutatorElement_mem_inner_of_mulEquiv e (statedSp_two_outer_comm hK)
    · exact commutatorElement_mem_inner_of_mulEquiv e (statedSp_outer_comm hr3)
  exact fieldRigidIn_self_of_outer_comm hn _ hOut h01.symm
    (proj n K (SpecialLinearGroup.transvection h01 1))
    (proj_conj_transvection_mem_autFixSubgroup_dualAut h01)

end Nonalt

section Final

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem innerGraphFieldRigid_of_nonalt_even {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (hAD : InnerNonaltFieldRigid K (Nat.le_of_succ_le hn))
    (hDD : Even n → FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (autFixSubgroup (dualAut n K))) (perfectCore (autFixSubgroup (dualAut n K)))) :
    InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine innerGraphFieldRigid_of_residual hK hq hn hAD ⟨?_, fun r C hr hC => ?_⟩
  · rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    · exact hDD hev
    · exact fieldRigidIn_graph_nonalt_self_of_odd hK hq _ (r := r) (by omega) hr
  · exact fieldRigidIn_graph_alt_self' hK hq _ (r := r) (by omega) hr C hC

theorem innerGraphFieldRigid_of_odd {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hodd : Odd n) : InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  refine innerGraphFieldRigid_of_cases' hK hn fun hq => ?_
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hnev : ¬ Even n := Nat.not_even_iff_odd.2 hodd
  refine ⟨innerMaxFieldRigid hq hn, ?_, ?_⟩
  · intro k P C hP hC
    rcases hC with h1 | ⟨r, hr, hJ⟩
    · exact fieldRigidIn_inner_graph_of_symplectic hK hq hn P hP C (Or.inr ⟨h1, hodd⟩)
    · exact absurd ⟨r, by omega⟩ hnev
  · intro C C' hC hC'
    rcases hC with h1 | ⟨r, hr, -⟩
    · rcases hC' with h1' | ⟨r', hr', -⟩
      · rw [conjAut_mul_dualAut_eq_of_eq_one h1, conjAut_mul_dualAut_eq_of_eq_one h1']
        obtain ⟨r, hr⟩ := hodd
        exact fieldRigidIn_graph_nonalt_self_of_odd hK hq _ (r := r) (by omega) hr
      · exact absurd ⟨r', by omega⟩ hnev
    · exact absurd ⟨r, by omega⟩ hnev

end Final

end CFSG.SeitzReduction.LinearPilot
