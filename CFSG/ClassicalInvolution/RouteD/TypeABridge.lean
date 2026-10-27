module

public import CFSG.ClassicalInvolution.Generic.InductionSL2
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.RootSystem
open CFSG.ClassicalInvolution.Phan (blockMat_apply_of_not_mem_left)
open scoped MatrixGroups

section Lengths

theorem symmetrizer_A_succ (k : ℕ) (i j : Fin k) (h : i.val + 1 = j.val) :
    symmetrizer (isFiniteType_A k) i = symmetrizer (isFiniteType_A k) j := by
  have e1 : CartanMatrix.A k i j = -1 := by
    unfold CartanMatrix.A
    simp only [Matrix.of_apply]
    have : i ≠ j := fun e => by rw [e] at h; omega
    simp [this, h]
  have e2 : CartanMatrix.A k j i = -1 := by
    unfold CartanMatrix.A
    simp only [Matrix.of_apply]
    have : j ≠ i := fun e => by rw [e] at h; omega
    simp [this, h]
  have hc := form_comm (isFiniteType_A k) (Pi.single i 1) (Pi.single j 1)
  rw [form_single_left, form_single_left] at hc
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, e1, e2] at hc
  push_cast at hc
  linarith

theorem symmetrizer_A_eq (k : ℕ) (i j : Fin k) :
    symmetrizer (isFiniteType_A k) i = symmetrizer (isFiniteType_A k) j := by
  have key : ∀ n : ℕ, ∀ i j : Fin k, i.val + n = j.val →
      symmetrizer (isFiniteType_A k) i = symmetrizer (isFiniteType_A k) j := by
    intro n
    induction n with
    | zero => intro i j h; rw [Fin.ext (by omega : i.val = j.val)]
    | succ n ih =>
      intro i j h
      have hl : i.val + 1 < k := by have := j.isLt; omega
      exact (symmetrizer_A_succ k i ⟨i.val + 1, hl⟩ rfl).trans (ih ⟨i.val + 1, hl⟩ j (by simp; omega))
  rcases le_total i.val j.val with h | h
  · exact key (j.val - i.val) i j (by omega)
  · exact (key (i.val - j.val) j i (by omega)).symm

theorem form_eq_of_mem_roots_A {k : ℕ} {γ δ : Fin k → ℤ}
    (hγ : γ ∈ roots (isFiniteType_A k) ∅) (hδ : δ ∈ roots (isFiniteType_A k) ∅) :
    form (isFiniteType_A k) (toRat γ) (toRat γ) = form (isFiniteType_A k) (toRat δ) (toRat δ) := by
  have hlen : ∀ {γ : Fin k → ℤ}, γ ∈ roots (isFiniteType_A k) ∅ → ∃ i : Fin k,
      form (isFiniteType_A k) (toRat γ) (toRat γ) = 2 * symmetrizer (isFiniteType_A k) i := by
    intro γ hγ
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
    · refine ⟨i, ?_⟩
      rw [form_weylAction, toRat_single, form_single_single]
    · exact absurd hi (Set.notMem_empty i)
  obtain ⟨i, hi⟩ := hlen hγ
  obtain ⟨j, hj⟩ := hlen hδ
  rw [hi, hj, symmetrizer_A_eq k i j]

theorem isLongestRoot_of_mem_roots {F : Type} [Field F] {k : ℕ} {γ : Fin k → ℤ}
    (hγ : γ ∈ roots (isFiniteType_A k) ∅) : IsLongestRoot (rootDatum k F) γ :=
  ⟨hγ, fun _ hδ => (form_eq_of_mem_roots_A hδ hγ).le⟩

end Lengths

section Mono

variable {F : Type} [Field F]

theorem monomial_conj_transvection {n : ℕ} {g : SL(n, F)} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (g : Matrix (Fin n) (Fin n) F) τ) {a b : Fin n} (hab : a ≠ b) :
    ∃ ε : F, ε ≠ 0 ∧ ∀ c : F, g * SpecialLinearGroup.transvection hab c * g⁻¹ =
      SpecialLinearGroup.transvection (τ.injective.ne hab) (ε * c) := by
  obtain ⟨αa, hαa, ha⟩ := hg a
  obtain ⟨αb, hαb, hb⟩ := hg b
  refine ⟨αa * αb⁻¹, mul_ne_zero hαa (inv_ne_zero hαb), fun c => ?_⟩
  apply Subtype.ext
  have hMN : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = 1 :=
    coe_mul_coe_inv g
  have hNM : ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = 1 :=
    coe_inv_mul_coe g
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  refine Matrix.ext_of_mulVec_single fun k => ?_
  obtain ⟨αj, hαj, hj⟩ := hg (τ.symm k)
  have hNk : ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single k 1 =
      αj⁻¹ • Pi.single (τ.symm k) 1 := by
    have h1 : ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) *ᵥ
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single (τ.symm k) 1) = Pi.single (τ.symm k) 1 := by
      rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [hj, Matrix.mulVec_smul, Equiv.apply_symm_apply] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hαj, one_smul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hNk, Matrix.mulVec_smul, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add]
  have hsm : ∀ (i : Fin n) (v : F), Function.update (0 : Fin n → F) i v = Pi.single i v :=
    fun _ _ => rfl
  have hMa : ∀ v : F, (g : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single a v =
      (αa * v) • Pi.single (τ a) (1 : F) := by
    intro v
    rw [show (Pi.single a v : Fin n → F) = v • Pi.single a (1 : F) by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], Matrix.mulVec_smul, ha, smul_smul,
      mul_comm v αa]
  have hsingle : ∀ (i : Fin n) (v : F), (Pi.single i v : Fin n → F) = v • Pi.single i (1 : F) :=
    fun i v => by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsm, hMa, hj, Equiv.apply_symm_apply, hsm]
  by_cases hjb : τ.symm k = b
  · subst hjb
    have hαjb : αj = αb := by
      have := hj.symm.trans hb
      have h3 := congr_fun this k
      simpa only [Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        mul_one] using h3
    have hk : τ (τ.symm k) = k := Equiv.apply_symm_apply τ k
    rw [Pi.single_eq_same, hk, Pi.single_eq_same, hαjb]
    ext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> (try field_simp) <;> (try ring)
  · have h1 : (Pi.single (τ.symm k) 1 : Fin n → F) b = 0 := Pi.single_eq_of_ne (Ne.symm hjb) _
    have h2 : (Pi.single k 1 : Fin n → F) (τ b) = 0 := by
      refine Pi.single_eq_of_ne (fun h => hjb ?_) _
      rw [← h]; simp
    rw [h1, h2, mul_zero, mul_zero, mul_zero, zero_smul, add_zero, Pi.single_zero, add_zero,
      smul_smul, inv_mul_cancel₀ hαj, one_smul]

end Mono

section Bridge

variable {F : Type} [Field F] {m : ℕ}

theorem map_conj_rootSubgroup {g : SL(m + 1, F)} {τ : Equiv.Perm (Fin (m + 1))}
    (hg : IsMonomialFor (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) τ) {a b : Fin (m + 1)}
    (hab : a ≠ b) :
    (rootSubgroup m F hab).map (MulAut.conj g).toMonoidHom =
      rootSubgroup m F (τ.injective.ne hab) := by
  obtain ⟨ε, hε, h⟩ := monomial_conj_transvection hg hab
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab y).mp hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h c]
    exact transvection_mem_rootSubgroup _ _
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
    refine ⟨SpecialLinearGroup.transvection hab (ε⁻¹ * c), transvection_mem_rootSubgroup _ _, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]

theorem rootSubgroup_sup_eq_map_conj_rootSL2 (hn : 2 ≤ m + 1) {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ g : SL(m + 1, F), rootSubgroup m F hij ⊔ rootSubgroup m F hij.symm =
      (rootSL2 F hn).map (MulAut.conj g).toMonoidHom := by
  have hm : 0 < m := by omega
  obtain ⟨g, τ, hg, h0, h1⟩ := exists_monomial_pair (K := F) hn hij
  refine ⟨g, ?_⟩
  have h01 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := fun e => by
    have := congrArg Fin.val e; simp at this
  have e1 := map_conj_rootSubgroup hg h01
  have e2 := map_conj_rootSubgroup hg h01.symm
  have hroot : rootSubgroup m F h01 ⊔ rootSubgroup m F h01.symm = rootSL2 F hn := by
    have := rankOne_eq_range (K := F) (n := m) ⟨0, hm⟩
    rw [rankOne_rootGroup] at this
    exact this
  rw [← hroot, Subgroup.map_sup, e1, e2]
  subst h0 h1
  rfl

open CFSG.ClassicalInvolution.Generic in
theorem fundamentalSubgroups_psl_subset (hn : 2 ≤ m + 1) :
    fundamentalSubgroups .PSL (rootDatum m F) ⊆ longRootSet (K := F) hn := by
  rintro R ⟨g, γ₀, hγ, rfl⟩
  let γ : Fin m → ℤ := γ₀
  have hγr : γ ∈ roots (isFiniteType_A m) ∅ := by
    rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact h.1
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨hij, hs⟩ := idx_spec m hγr
  have hX : rootGroup m F γ = rootSubgroup m F hij := rootGroup_eq m F hij hs
  have hneg : toStd m (-γ) = Pi.single (idx m γ).2 1 - Pi.single (idx m γ).1 1 := by
    rw [toStd_neg, hs, neg_sub]
  have hX' : rootGroup m F (-γ) = rootSubgroup m F hij.symm := rootGroup_eq m F hij.symm hneg
  obtain ⟨g₁, hg₁⟩ := rootSubgroup_sup_eq_map_conj_rootSL2 (F := F) hn hij
  rw [mem_longRootSet_iff]
  refine ⟨g * g₁, ?_⟩
  show conjSub g (rootGroup m F γ ⊔ rootGroup m F (-γ)) = _
  rw [hX, hX', hg₁, conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

open CFSG.ClassicalInvolution.Generic in
theorem longRootSet_subset_fundamentalSubgroups_psl (hn : 2 ≤ m + 1) :
    longRootSet (K := F) hn ⊆ fundamentalSubgroups .PSL (rootDatum m F) := by
  intro R hR
  have hm : 0 < m := by omega
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hn).mp hR
  have hroot : rootSL2 F hn = rootGroup m F (Pi.single ⟨0, hm⟩ 1) ⊔
      rootGroup m F (-Pi.single ⟨0, hm⟩ 1) := (rankOne_eq_range (K := F) (n := m) ⟨0, hm⟩).symm
  refine ⟨g, Pi.single ⟨0, hm⟩ 1, Or.inl (isLongestRoot_of_mem_roots (Or.inl ⟨1, ⟨0, hm⟩, by simp; rfl⟩)),
    ?_⟩
  show Subgroup.map _ (rootSL2 F hn) = Subgroup.map _ (rootGroup m F _ ⊔ rootGroup m F _)
  rw [hroot]
  rfl

theorem rootSL2_two_eq_top (hn : 2 ≤ 2) : rootSL2 F hn = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact ⟨x, Subtype.ext (blockMat_two_zero (x : Matrix (Fin 2) (Fin 2) F))⟩

theorem longRootSet_two_subset (hn : 2 ≤ 2) :
    longRootSet (K := F) hn ⊆ {⊤} := by
  intro R hR
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hn).mp hR
  rw [rootSL2_two_eq_top]
  exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)

theorem longRootSet_two_ncard_le (hn : 2 ≤ 2) : (longRootSet (K := F) hn).ncard ≤ 1 :=
  (Set.ncard_le_ncard (longRootSet_two_subset hn)).trans (by simp)

theorem iSup_longRootSet_eq_top (h2 : (2 : F) ≠ 0) (hn : 2 ≤ m + 1) :
    ⨆ R ∈ longRootSet (K := F) hn, R = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top (m := m) (F := F)]
  refine iSup_le fun k => iSup_le fun s => ?_
  have hk := isLongRootSL2_range_blockSL h2 (K := F) (n := m + 1) (j := k.val)
    (by have := k.isLt; omega)
  have hmem : (blockSL2 F m k).range ∈ longRootSet (K := F) hn := ⟨_, hk⟩
  have hle : fundamentalRootSubgroup m F k s ≤ (blockSL2 F m k).range := by
    rw [← rankOne_eq_range, rankOne_rootGroup]
    cases s
    · exact le_sup_right
    · exact le_sup_left
  exact hle.trans (le_iSup₂_of_le _ hmem le_rfl)

noncomputable abbrev tailBlock (F : Type) [Field F] (k : ℕ) : SL(k, F) →* SL(k + 2, F) :=
  blockSL F (k + 2) k 2 (by omega)

theorem tailBlock_injective (F : Type) [Field F] (k : ℕ) : Function.Injective (tailBlock F k) :=
  blockSL_injective _

theorem map_map_conj {G H : Type*} [Group G] [Group H] (φ : G →* H) (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map φ = (A.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_tailBlock_mem_longRootSet (h2 : (2 : F) ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    {R : Subgroup SL(k, F)} (hR : R ∈ longRootSet (K := F) hk) :
    R.map (tailBlock F k) ∈ longRootSet (K := F) (by omega : 2 ≤ k + 2) := by
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hk).mp hR
  have h1 : (rootSL2 F hk).map (tailBlock F k) = (blockSL F (k + 2) 2 2 (by omega)).range := by
    rw [rootSL2, ← MonoidHom.range_comp, blockSL_comp]
  rw [map_map_conj, h1]
  exact longRootSet_conjInvariant (by omega) _ _ ⟨_, isLongRootSL2_range_blockSL h2 (by omega)⟩

theorem tailBlock_commutes_rootSL2 {k : ℕ} (hn : 2 ≤ k + 2) (s : SL(k, F)) (r : SL(2, F)) :
    tailBlock F k s * blockSL F (k + 2) 2 0 (by omega) r =
      blockSL F (k + 2) 2 0 (by omega) r * tailBlock F k s :=
  blockSL_comm _ _ (Or.inr (by omega)) s r

theorem tailBlock_eq_one_of_mem_center {k : ℕ} {s : SL(k, F)}
    (hs : tailBlock F k s ∈ Subgroup.center SL(k + 2, F)) : s = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  have h0 : ((tailBlock F k s : SL(k + 2, F)) : Matrix (Fin (k + 2)) (Fin (k + 2)) F)
      ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    rw [coe_blockSL, blockMat_apply_of_not_mem_left _ (by simp)]
    simp
  have hr1 : r = 1 := by
    rw [← hr] at h0
    simpa [Matrix.scalar_apply] using h0
  apply tailBlock_injective F k
  rw [map_one]
  apply Subtype.ext
  rw [← hr, hr1, map_one]
  rfl

end Bridge

end CFSG.ClassicalInvolution.RouteD
