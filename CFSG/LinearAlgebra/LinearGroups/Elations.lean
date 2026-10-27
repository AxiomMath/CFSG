module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer

public section

namespace CFSG.LinearGroups

open Matrix Module
open scoped Pointwise LinearAlgebra.Projectivization

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_center_iff_exists_units {A : SpecialLinearGroup (Fin n) K} :
    A ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) ↔
      ∃ l : Kˣ, l ^ n = 1 ∧ (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (l : K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, one_pow 0, Subsingleton.elim _ _⟩
    · obtain ⟨l, rfl⟩ := IsUnit.of_pow_eq_one hr hn.ne'
      exact ⟨l, Units.ext (by simpa using hr), hA.symm⟩
  · rintro ⟨l, hl, hA⟩
    exact ⟨l, by simpa using congrArg Units.val hl, hA.symm⟩

@[expose] def scalarSubgroup (n : ℕ) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  (Subgroup.center (SpecialLinearGroup (Fin n) K)).copy
    {A | ∃ l : Kˣ, l ^ n = 1 ∧ (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (l : K)}
    (Set.ext fun _ => mem_center_iff_exists_units.symm)

theorem mem_scalarSubgroup_iff {A : SpecialLinearGroup (Fin n) K} :
    A ∈ scalarSubgroup n K ↔
      ∃ l : Kˣ, l ^ n = 1 ∧ (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (l : K) :=
  Iff.rfl

theorem scalarSubgroup_eq_center :
    scalarSubgroup n K = Subgroup.center (SpecialLinearGroup (Fin n) K) :=
  Subgroup.copy_eq _ _ _

instance scalarSubgroup_normal : (scalarSubgroup n K).Normal := by
  rw [scalarSubgroup_eq_center]
  infer_instance

@[expose] noncomputable def scalarQuotientEquivPSL :
    SpecialLinearGroup (Fin n) K ⧸ scalarSubgroup n K ≃*
      ProjectiveSpecialLinearGroup (Fin n) K :=
  QuotientGroup.quotientMulEquivOfEq scalarSubgroup_eq_center

theorem scalarQuotientEquivPSL_mk (A : SpecialLinearGroup (Fin n) K) :
    scalarQuotientEquivPSL
        (QuotientGroup.mk A : SpecialLinearGroup (Fin n) K ⧸ scalarSubgroup n K) =
      QuotientGroup.mk A :=
  rfl

@[expose] def elationGenerators (L : Submodule K (Fin n → K)) :
    Set (SpecialLinearGroup (Fin n) K) :=
  {A | (∀ w, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w ∈ L) ∧
    ∀ w ∈ L, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = 0}

@[expose] def elationSubgroup (L : Submodule K (Fin n → K)) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  Subgroup.closure (elationGenerators L)

@[expose] noncomputable def projectiveElationSubgroup (L : Submodule K (Fin n → K)) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) K) :=
  (elationSubgroup L).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)))

theorem sub_one_mulVec (A : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = A • w - w := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

theorem mem_elationGenerators_iff {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} :
    A ∈ elationGenerators L ↔ (∀ w, A • w - w ∈ L) ∧ ∀ w ∈ L, A • w = w := by
  simp only [elationGenerators, Set.mem_ofPred_eq, sub_one_mulVec, sub_eq_zero]

theorem smul_eq_self_of_mem_elationGenerators {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ elationGenerators L) : A • L = L := by
  ext w
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [(mem_elationGenerators_iff.mp hA).2 u hu]
  · exact fun hw => ⟨w, hw, (mem_elationGenerators_iff.mp hA).2 w hw⟩

theorem exists_eq_span_of_finrank_eq_one {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    ∃ v : Fin n → K, v ≠ 0 ∧ L = K ∙ v :=
  ⟨(Projectivization.mk'' L hL).rep, Projectivization.rep_nonzero _, by
    rw [← Projectivization.submodule_eq, Projectivization.submodule_mk'']⟩

theorem elationGenerators_eq_lineStab {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    elationGenerators L =
      (Matrix.SpecialLinearGroup.lineStab L : Set (SpecialLinearGroup (Fin n) K)) := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_finrank_eq_one hL
  ext A
  rw [mem_elationGenerators_iff, SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_lineStab_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun w hw => ?_⟩⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [smul_comm, Matrix.SpecialLinearGroup.lineStab_fix_of_span v hv A h]

theorem elationSubgroup_eq_lineStab {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    elationSubgroup L = Matrix.SpecialLinearGroup.lineStab L := by
  rw [elationSubgroup, elationGenerators_eq_lineStab hL, Subgroup.closure_eq]

theorem linear_elation_abelian {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    (elationSubgroup L : Set (SpecialLinearGroup (Fin n) K)) = elationGenerators L ∧
      ∀ a ∈ elationSubgroup L, ∀ b ∈ elationSubgroup L, a * b = b * a := by
  obtain ⟨v, hv, hLv⟩ := exists_eq_span_of_finrank_eq_one hL
  refine ⟨by rw [elationSubgroup_eq_lineStab hL, elationGenerators_eq_lineStab hL], ?_⟩
  intro a ha b hb
  rw [elationSubgroup_eq_lineStab hL, hLv] at ha hb
  exact Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span' v hv a b ha hb

theorem conj_mem_elationGenerators {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ elationGenerators L)
    (g : SpecialLinearGroup (Fin n) K) : g * A * g⁻¹ ∈ elationGenerators (g • L) := by
  rw [mem_elationGenerators_iff] at hA ⊢
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · have h := Submodule.smul_mem_pointwise_smul _ g L (hA.1 (g⁻¹ • w))
    rwa [smul_sub, smul_inv_smul, ← mul_smul, ← mul_smul] at h
  · obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw
    rw [mul_smul, mul_smul, inv_smul_smul, hA.2 u hu]

theorem conj_smul_elationSubgroup (L : Submodule K (Fin n → K))
    (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj g • elationSubgroup L = elationSubgroup (g • L) := by
  rw [Subgroup.pointwise_smul_def, elationSubgroup, elationSubgroup]
  refine (MonoidHom.map_closure _ _).trans (congrArg Subgroup.closure ?_)
  ext B
  simp only [Set.mem_image, MulDistribMulAction.toMonoidEnd_apply]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact conj_mem_elationGenerators hA g
  · intro hB
    refine ⟨g⁻¹ * B * g⁻¹⁻¹, ?_, ?_⟩
    · have := conj_mem_elationGenerators hB g⁻¹
      rwa [inv_smul_smul] at this
    · simp [mul_assoc]

theorem linear_elation_conjugation (L : Submodule K (Fin n → K))
    (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj g • elationSubgroup L = elationSubgroup (g • L) ∧
      elationSubgroup L ≤ MulAction.stabilizer (SpecialLinearGroup (Fin n) K) L ∧
      ∀ h ∈ MulAction.stabilizer (SpecialLinearGroup (Fin n) K) L, ∀ a ∈ elationSubgroup L,
        h * a * h⁻¹ ∈ elationSubgroup L := by
  refine ⟨conj_smul_elationSubgroup L g, ?_, fun h hh a ha => ?_⟩
  · rw [elationSubgroup, Subgroup.closure_le]
    exact fun A hA => smul_eq_self_of_mem_elationGenerators hA
  · have hconj := conj_smul_elationSubgroup L h
    rw [MulAction.mem_stabilizer_iff.mp hh] at hconj
    rw [← hconj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.inv_apply, mul_assoc] using ha

theorem linear_elation_elementary_containment {i j : Fin n} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈
      elationSubgroup (K ∙ (Pi.single i 1 : Fin n → K)) := by
  refine Subgroup.subset_closure ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [coe_transvection, add_sub_cancel_left]
    refine Submodule.mem_span_singleton.mpr ⟨c * w j, ?_⟩
    ext k
    by_cases hk : k = i
    · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk]
    · simp [Matrix.mulVec, dotProduct, hk, Ne.symm hk]
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [coe_transvection, add_sub_cancel_left]
    ext k
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, Ne.symm hij]

theorem special_linear_projective_double_transitivity {L₁ L₂ M₁ M₂ : Submodule K (Fin n → K)}
    (hL₁ : finrank K L₁ = 1) (hL₂ : finrank K L₂ = 1) (hM₁ : finrank K M₁ = 1)
    (hM₂ : finrank K M₂ = 1) (hL : L₁ ≠ L₂) (hM : M₁ ≠ M₂) :
    ∃ g : SpecialLinearGroup (Fin n) K, g • L₁ = M₁ ∧ g • L₂ = M₂ := by
  have h2 : ∀ {a b c d : ℙ K (Fin n → K)}, a ≠ b → c ≠ d →
      ∃ g : SpecialLinearGroup (Fin n) K, g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp inferInstance
  have hne : ∀ {L L' : Submodule K (Fin n → K)} (h : finrank K L = 1) (h' : finrank K L' = 1),
      L ≠ L' → Projectivization.mk'' L h ≠ Projectivization.mk'' L' h' := by
    intro L L' h h' hLL' hp
    apply hLL'
    rw [← Projectivization.submodule_mk'' L h, hp, Projectivization.submodule_mk'']
  obtain ⟨g, hg₁, hg₂⟩ := h2 (hne hL₁ hL₂ hL) (hne hM₁ hM₂ hM)
  refine ⟨g, ?_, ?_⟩
  · rw [← Projectivization.submodule_mk'' L₁ hL₁, ← PSL.smul_submodule, hg₁,
      Projectivization.submodule_mk'']
  · rw [← Projectivization.submodule_mk'' L₂ hL₂, ← PSL.smul_submodule, hg₂,
      Projectivization.submodule_mk'']

theorem linear_elation_conjugate_generation {L : Submodule K (Fin n → K)}
    (hL : finrank K L = 1) :
    Subgroup.normalClosure (elationSubgroup L : Set (SpecialLinearGroup (Fin n) K)) = ⊤ := by
  set N := Subgroup.normalClosure (elationSubgroup L : Set (SpecialLinearGroup (Fin n) K))
  have hconj : ∀ g : SpecialLinearGroup (Fin n) K, elationSubgroup (g • L) ≤ N := by
    intro g x hx
    rw [← conj_smul_elationSubgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hmem := Subgroup.normalClosure_normal.conj_mem _ (Subgroup.subset_normalClosure hx) g
    simpa [MulAut.inv_apply, mul_assoc] using hmem
  rw [eq_top_iff, ← special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  have hei : (Pi.single i (1 : K) : Fin n → K) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) K)
    (Projectivization.mk'' L hL) (Projectivization.mk K _ hei)
  have hgL : g • L = K ∙ (Pi.single i 1 : Fin n → K) := by
    rw [← Projectivization.submodule_mk'' L hL, ← PSL.smul_submodule, hg,
      Projectivization.submodule_mk]
  exact hconj g (hgL ▸ linear_elation_elementary_containment hij c)

end CFSG.LinearGroups
