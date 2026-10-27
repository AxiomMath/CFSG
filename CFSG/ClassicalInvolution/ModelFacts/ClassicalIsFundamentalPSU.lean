module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSU
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.Open
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ComponentClassification Module
open scoped MatrixGroups

section Transport

variable {p f : ℕ} [Fact p.Prime] {Y Y' : Type} [Group Y] [Group Y']

theorem isClassicalMember_map_mulEquiv {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z)
    (φ : Y ≃* Y') : IsClassicalMember p f (L.map φ.toMonoidHom) (φ z) where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map φ.toMonoidHom
  subnormal := by
    have h1 := isSubnormal_comap φ.symm.toMonoidHom h.subnormal
    have e1 : L.comap φ.symm.toMonoidHom = L.map φ.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_map_equiv]
      rfl
    have e2 : (Subgroup.centralizer ({z} : Set Y)).comap φ.symm.toMonoidHom =
        Subgroup.centralizer ({φ z} : Set Y') := by
      ext x
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        have := congrArg φ hx
        simpa using this
      · intro hx
        apply φ.injective
        simpa using hx
    rwa [e1, e2] at h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* L.map φ.toMonoidHom := L.equivMapOfInjective φ.toMonoidHom φ.injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map φ.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

end Transport

section FixCols

variable {F : Type} [Field F] {σ : F ≃+* F} {n r : ℕ}

variable (σ n) in
@[expose] def fixCols (e : Fin r → Fin n) : Subgroup (SU σ n) where
  carrier := {g | ∀ c, c ∉ Set.range e → ∀ a, mat σ n g a c = (1 : Matrix (Fin n) (Fin n) F) a c}
  mul_mem' {g h} hg hh c hc a := by
    rw [map_mul, Matrix.mul_apply]
    calc ∑ b, mat σ n g a b * mat σ n h b c
        = ∑ b, mat σ n g a b * (1 : Matrix (Fin n) (Fin n) F) b c := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hh c hc b]
      _ = ((mat σ n g : Matrix (Fin n) (Fin n) F) * (1 : Matrix (Fin n) (Fin n) F)) a c := by
          rw [Matrix.mul_apply]
      _ = (1 : Matrix (Fin n) (Fin n) F) a c := by rw [Matrix.mul_one]; exact hg c hc a
  one_mem' c _ a := by rw [map_one]
  inv_mem' {g} hg c hc a := by
    have h1 : (mat σ n g⁻¹ * mat σ n g) a c = (1 : Matrix (Fin n) (Fin n) F) a c := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [Matrix.mul_apply] at h1
    calc mat σ n g⁻¹ a c = ∑ b, mat σ n g⁻¹ a b * (1 : Matrix (Fin n) (Fin n) F) b c := by
          rw [← Matrix.mul_apply, Matrix.mul_one]
      _ = ∑ b, mat σ n g⁻¹ a b * mat σ n g b c := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hg c hc b]
      _ = (1 : Matrix (Fin n) (Fin n) F) a c := h1

theorem mem_fixCols {e : Fin r → Fin n} {g : SU σ n} :
    g ∈ fixCols σ n e ↔
      ∀ c, c ∉ Set.range e → ∀ a, mat σ n g a c = (1 : Matrix (Fin n) (Fin n) F) a c := Iff.rfl

theorem isBlkOn_of_mem_fixCols {e : Fin r → Fin n} (hrev : ∀ i, e (Fin.rev i) = Fin.rev (e i))
    {g : SU σ n} (hg : g ∈ fixCols σ n e) : IsBlkOn e (mat σ n g) := by
  intro a b hab
  rcases hab with ha | hb
  · have hra : Fin.rev a ∉ Set.range e := by
      rintro ⟨i, hi⟩
      apply ha
      refine ⟨Fin.rev i, ?_⟩
      rw [hrev, hi, Fin.rev_rev]
    have := mat_rev_apply_of_col (x := g) (s := Fin.rev a) (fun a' => hg _ hra a') b
    rwa [Fin.rev_rev] at this
  · exact hg b hb a

theorem mat_mulVec_eq_self {e : Fin r → Fin n} {g : SU σ n} (hg : g ∈ fixCols σ n e)
    {u : Fin n → F} (hu : ∀ c ∈ Set.range e, u c = 0) : mat σ n g *ᵥ u = u := by
  funext a
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ c, mat σ n g a c * u c = ∑ c, (1 : Matrix (Fin n) (Fin n) F) a c * u c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : c ∈ Set.range e
        · rw [hu c hc, mul_zero, mul_zero]
        · rw [hg c hc a]
    _ = u a := by
        have := congrFun (Matrix.one_mulVec u) a
        simpa [Matrix.mulVec, dotProduct] using this

end FixCols

section RankOne

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem col_eq_one_of_hasWt {i : Fin n} (hi : i ≠ Fin.rev i) {x : SU σ n}
    (hx : HasWt (wt2 (2 • weight n i)) (mat σ n x - 1)) :
    ∀ c, c ≠ i → c ≠ Fin.rev i → ∀ a, mat σ n x a c = (1 : Matrix (Fin n) (Fin n) F) a c := by
  intro c _ hcr a
  by_contra hne
  have hne' : (mat σ n x - 1) a c ≠ 0 := by
    rw [Matrix.sub_apply]
    exact sub_ne_zero.mpr hne
  have hw := hx a c hne'
  rw [mem_wt2] at hw
  rcases hw with hw | hw
  · exact hcr (eq_of_weight_sub_eq_two_smul hi hw).2
  · have h4 : weight n a - weight n c = (4 : ℕ) • weight n i := by rw [hw, ← mul_smul]; norm_num
    exact weight_ne_zero hi (eq_zero_of_weight_sub_eq_nsmul h4 (by norm_num))

theorem rootGroup_le_fixCols (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)} {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = 2 • weight n (lowIdx k)) :
    rootGroup σ hσ n γ ≤ fixCols σ n (lastIdxEven k) := by
  intro x hx c hc a
  have h1 := rootGroup_le_wt2Subgroup hσ γ hx
  rw [mem_wt2Subgroup, hγ] at h1
  exact col_eq_one_of_hasWt (lowIdx_ne_rev k k) h1.1 c (fun h => hc ⟨0, h.symm⟩)
    (fun h => hc ⟨1, h.symm⟩) a

theorem rootGroup_le_fixCols_neg (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)}
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k))) :
    rootGroup σ hσ n (-γ) ≤ fixCols σ n (lastIdxEven k) := by
  intro x hx c hc a
  have h1 := rootGroup_le_wt2Subgroup hσ (-γ) hx
  rw [mem_wt2Subgroup, hγ] at h1
  exact col_eq_one_of_hasWt (rev_ne_rev_rev (lowIdx_ne_rev k k)) h1.1 c
    (fun h => hc ⟨1, h.symm⟩) (fun h => hc ⟨0, by rw [h, Fin.rev_rev]; rfl⟩) a

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem rankOne_eq_fixCols (hF : Nat.card F = (p ^ f) ^ 2) {k : Fin (n / 2)}
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = 2 • weight n (lowIdx k))
    (hγ' : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k))) :
    rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
      rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ) =
        fixCols (unitaryInvolution F p f) n (lastIdxEven k) := by
  have hσ := unitaryInvolution_involutive hF
  have hpp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hpp
  set σ := unitaryInvolution F p f with hσdef
  set R := rootGroup σ hσ n γ ⊔ rootGroup σ hσ n (-γ) with hRdef
  set L := fixCols σ n (lastIdxEven k) with hLdef
  have hRL : R ≤ L := sup_le (rootGroup_le_fixCols hσ hγ) (rootGroup_le_fixCols_neg hσ hγ')
  refine le_antisymm hRL ?_
  have hL : ∀ g ∈ L, IsBlkOn (lastIdxEven k) (mat σ n g) := fun g hg =>
    isBlkOn_of_mem_fixCols lastIdxEven_rev hg
  let β := unitaryBlockHom σ lastIdxEven_injective lastIdxEven_rev L hL
  have hβ : Function.Injective β := unitaryBlockHom_injective
  have hS : ⊤ ≤ (R.subgroupOf L).map β := by
    rw [← rankOne_two_eq_top hF]
    refine sup_le ?_ ?_
    · rw [rootGroup_two_eq_range hσ]
      rintro _ ⟨c, rfl⟩
      have hmem : longRootHom σ hpp c ∈ rootGroup σ hσ n γ :=
        longRootHom_mem hσ hpp hγ.symm c
      have hmemR : longRootHom σ hpp c ∈ R := Subgroup.mem_sup_left hmem
      refine ⟨⟨longRootHom σ hpp c, hRL hmemR⟩, Subgroup.mem_subgroupOf.mpr hmemR,
        mat_injective ?_⟩
      change (longRootMatrix (lowIdx k) (c.toAdd : F)).submatrix (lastIdxEven k) (lastIdxEven k) =
        longRootMatrix 0 (c.toAdd : F)
      exact submatrix_longRootMatrix (F := F) (i := 0) (j := lowIdx k) lastIdxEven_injective
        lastIdxEven_rev rfl _
    · rw [rootGroup_two_neg_eq_range hσ]
      rintro _ ⟨c, rfl⟩
      have hmem : longRootHom σ hp' c ∈ rootGroup σ hσ n (-γ) :=
        longRootHom_mem hσ hp' hγ'.symm c
      have hmemR : longRootHom σ hp' c ∈ R := Subgroup.mem_sup_right hmem
      refine ⟨⟨longRootHom σ hp' c, hRL hmemR⟩, Subgroup.mem_subgroupOf.mpr hmemR,
        mat_injective ?_⟩
      change (longRootMatrix (Fin.rev (lowIdx k)) (c.toAdd : F)).submatrix (lastIdxEven k)
        (lastIdxEven k) = longRootMatrix 1 (c.toAdd : F)
      exact submatrix_longRootMatrix (F := F) (i := 1) (j := Fin.rev (lowIdx k))
        lastIdxEven_injective lastIdxEven_rev rfl _
  intro x hx
  obtain ⟨t, ht, hbt⟩ := hS (Subgroup.mem_top (β ⟨x, hx⟩))
  have : t = ⟨x, hx⟩ := hβ hbt
  subst this
  exact Subgroup.mem_subgroupOf.mp ht

end RankOne

section Plane

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem herm_mulVec_mulVec {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    (u v : Fin n → F) : herm σ (P *ᵥ u) (P *ᵥ v) = ∑ r, σ (u r) * v (Fin.rev r) := by
  have h1 : (fun r => σ ((P *ᵥ u) r)) = (P.map σ) *ᵥ (fun a => σ (u a)) := by
    funext r
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have h2 : herm σ (P *ᵥ u) (P *ᵥ v) = ((P.map σ) *ᵥ (fun a => σ (u a))) ⬝ᵥ (P *ᵥ v) := by
    rw [← h1]
    rfl
  have h3 : ((P.map σ) *ᵥ (fun a => σ (u a))) ⬝ᵥ (P *ᵥ v) =
      (fun a => σ (u a)) ⬝ᵥ ((conjTr σ P) *ᵥ (P *ᵥ v)) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    rfl
  rw [h2, h3, Matrix.mulVec_mulVec, hP]
  simp only [dotProduct, Matrix.mulVec, antidiag, Matrix.of_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp

theorem herm_mulVec_col {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    (u : Fin n → F) (c : Fin n) :
    herm σ (P *ᵥ u) (P *ᵥ Pi.single c 1) = σ (u (Fin.rev c)) := by
  rw [herm_mulVec_mulVec hP]
  have : ∀ r, (Pi.single c (1 : F) : Fin n → F) (Fin.rev r) = if r = Fin.rev c then 1 else 0 :=
    fun r => by
      rw [Pi.single_apply]
      by_cases h : r = Fin.rev c
      · have : Fin.rev r = c := by rw [h, Fin.rev_rev]
        rw [ite_eq_left this, ite_eq_left h]
      · have : Fin.rev r ≠ c := fun h' => h (by rw [← h', Fin.rev_rev])
        rw [ite_eq_right this, ite_eq_right h]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem herm_col_col {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    (c d : Fin n) :
    herm σ (P *ᵥ Pi.single c 1) (P *ᵥ Pi.single d 1) = if Fin.rev d = c then 1 else 0 := by
  rw [herm_mulVec_col hP, Pi.single_apply]
  split_ifs
  · exact map_one σ
  · exact map_zero σ

@[expose] def colPlane (P : Matrix (Fin n) (Fin n) F) (i : Fin n) : Submodule F (Fin n → F) :=
  Submodule.span F {P *ᵥ Pi.single i 1, P *ᵥ Pi.single (Fin.rev i) 1}

theorem mem_colPlane {P : Matrix (Fin n) (Fin n) F} {i : Fin n} {v : Fin n → F} :
    v ∈ colPlane P i ↔
      ∃ a b : F, a • (P *ᵥ Pi.single i 1) + b • (P *ᵥ Pi.single (Fin.rev i) 1) = v :=
  Submodule.mem_span_pair

theorem nondeg_colPlane {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    {i : Fin n} (hi : i ≠ Fin.rev i) : Nondeg σ (colPlane P i) := by
  intro v hv hvt
  obtain ⟨a, b, rfl⟩ := mem_colPlane.mp hv
  have hx : P *ᵥ Pi.single i 1 ∈ colPlane P i := Submodule.subset_span (by simp)
  have hy : P *ᵥ Pi.single (Fin.rev i) 1 ∈ colPlane P i := Submodule.subset_span (by simp)
  have hxy : herm σ (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single (Fin.rev i) 1) = 1 := by
    rw [herm_col_col hP, ite_eq_left (Fin.rev_rev i)]
  have hxx : herm σ (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single i 1) = 0 := by
    rw [herm_col_col hP, ite_eq_right (fun h => hi h.symm)]
  have hyx : herm σ (P *ᵥ Pi.single (Fin.rev i) 1) (P *ᵥ Pi.single i 1) = 1 := by
    rw [herm_col_col hP, ite_eq_left rfl]
  have hyy : herm σ (P *ᵥ Pi.single (Fin.rev i) 1) (P *ᵥ Pi.single (Fin.rev i) 1) = 0 := by
    rw [herm_col_col hP, ite_eq_right (fun h => hi (by rwa [Fin.rev_rev] at h))]
  have h1 := hvt _ hy
  have h2 := hvt _ hx
  rw [herm_add_left, herm_smul_left, herm_smul_left, hxy, hyy] at h1
  rw [herm_add_left, herm_smul_left, herm_smul_left, hxx, hyx] at h2
  have ha : a = 0 := by
    have : σ a = 0 := by simpa using h1
    simpa using this
  have hb : b = 0 := by
    have : σ b = 0 := by simpa using h2
    simpa using this
  rw [ha, hb]
  simp

theorem finrank_colPlane {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    {i : Fin n} (hi : i ≠ Fin.rev i) : finrank F (colPlane P i) = 2 := by
  have hxy : herm σ (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single (Fin.rev i) 1) = 1 := by
    rw [herm_col_col hP, ite_eq_left (Fin.rev_rev i)]
  have hxx : herm σ (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single i 1) = 0 := by
    rw [herm_col_col hP, ite_eq_right (fun h => hi h.symm)]
  have hyx : herm σ (P *ᵥ Pi.single (Fin.rev i) 1) (P *ᵥ Pi.single i 1) = 1 := by
    rw [herm_col_col hP, ite_eq_left rfl]
  have hyy : herm σ (P *ᵥ Pi.single (Fin.rev i) 1) (P *ᵥ Pi.single (Fin.rev i) 1) = 0 := by
    rw [herm_col_col hP, ite_eq_right (fun h => hi (by rwa [Fin.rev_rev] at h))]
  have hind : LinearIndependent F ![P *ᵥ Pi.single i 1, P *ᵥ Pi.single (Fin.rev i) 1] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (herm σ (P *ᵥ Pi.single (Fin.rev i) 1)) hab
    have h2 := congrArg (herm σ (P *ᵥ Pi.single i 1)) hab
    rw [herm_add_right, herm_smul_right, herm_smul_right, hyx, hyy] at h1
    rw [herm_add_right, herm_smul_right, herm_smul_right, hxx, hxy] at h2
    have h0 : ∀ x : Fin n → F, herm σ x 0 = 0 := fun x => by simp [herm]
    rw [h0] at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  have h5 := finrank_span_eq_card hind
  have hr : Set.range ![P *ᵥ Pi.single i 1, P *ᵥ Pi.single (Fin.rev i) 1] =
      {P *ᵥ Pi.single i 1, P *ᵥ Pi.single (Fin.rev i) 1} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    simp [eq_comm]
  rw [hr] at h5
  rw [colPlane, h5]
  simp

theorem mem_perp_colPlane_iff {P : Matrix (Fin n) (Fin n) F} (hP : conjTr σ P * P = antidiag n)
    {i : Fin n} (u : Fin n → F) :
    P *ᵥ u ∈ perp σ (colPlane P i) ↔ u (Fin.rev i) = 0 ∧ u i = 0 := by
  have hx : P *ᵥ Pi.single i 1 ∈ colPlane P i := Submodule.subset_span (by simp)
  have hy : P *ᵥ Pi.single (Fin.rev i) 1 ∈ colPlane P i := Submodule.subset_span (by simp)
  constructor
  · intro h
    have h1 := h _ hx
    have h2 := h _ hy
    rw [herm_mulVec_col hP] at h1 h2
    rw [Fin.rev_rev] at h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩ s hs
    obtain ⟨a, b, rfl⟩ := mem_colPlane.mp hs
    rw [herm_add_right, herm_smul_right, herm_smul_right, herm_mulVec_col hP,
      herm_mulVec_col hP, Fin.rev_rev, h1, h2]
    simp

end Plane

section Stabilizer

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem suMat_conjEquiv (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (x : SU (unitaryInvolution F p f) n) :
    suMat (conjEquiv P hP x) = (P : Matrix (Fin n) (Fin n) F) * mat (unitaryInvolution F p f) n x *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  show (((conjEquiv P hP x : SUid (unitaryInvolution F p f) n) : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) = _
  rw [coe_conjEquiv, Units.val_mul, Units.val_mul]
  rfl

theorem mat_conjEquiv_symm (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (y : SUid (unitaryInvolution F p f) n) :
    mat (unitaryInvolution F p f) n ((conjEquiv P hP).symm y) =
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * suMat y *
        (P : Matrix (Fin n) (Fin n) F) := rfl

theorem mem_map_fixCols_iff {k : Fin (n / 2)} (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) (y : Su F p f n) :
    y ∈ (fixCols (unitaryInvolution F p f) n (lastIdxEven k)).map (conjEquiv P hP).toMonoidHom ↔
      ∀ w ∈ perp (unitaryInvolution F p f)
        (colPlane (P : Matrix (Fin n) (Fin n) F) (lowIdx k)), y • w = w := by
  have hPP : (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set Pm : Matrix (Fin n) (Fin n) F := (P : Matrix (Fin n) (Fin n) F) with hPm
  set Pinv : Matrix (Fin n) (Fin n) F := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    with hPinv
  constructor
  · intro hy w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, rfl⟩ : ∃ u, w = Pm *ᵥ u :=
      ⟨Pinv *ᵥ w, by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]⟩
    have hw' := (mem_perp_colPlane_iff hP (i := lowIdx k) u).mp hw
    have hu0 : ∀ c ∈ Set.range (lastIdxEven k), u c = 0 := by
      rintro c ⟨j, rfl⟩
      fin_cases j
      · exact hw'.2
      · exact hw'.1
    have hxu := mat_mulVec_eq_self hx hu0
    show suMat (conjEquiv P hP x) *ᵥ (Pm *ᵥ u) = Pm *ᵥ u
    have e : (Pm * mat (unitaryInvolution F p f) n x * Pinv) *ᵥ (Pm *ᵥ u) =
        Pm *ᵥ (mat (unitaryInvolution F p f) n x *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      calc Pm * mat (unitaryInvolution F p f) n x * Pinv * Pm
          = Pm * mat (unitaryInvolution F p f) n x * (Pinv * Pm) := Matrix.mul_assoc _ _ _
        _ = Pm * mat (unitaryInvolution F p f) n x := by rw [hPiP, Matrix.mul_one]
    rw [suMat_conjEquiv, e, hxu]
  · intro h
    refine Subgroup.mem_map.mpr ⟨(conjEquiv P hP).symm y, ?_, by simp⟩
    intro c hc a
    have hc1 : c ≠ lowIdx k := fun h' => hc ⟨0, h'.symm⟩
    have hc2 : c ≠ Fin.rev (lowIdx k) := fun h' => hc ⟨1, h'.symm⟩
    have hw : Pm *ᵥ Pi.single c 1 ∈ perp (unitaryInvolution F p f) (colPlane Pm (lowIdx k)) := by
      rw [mem_perp_colPlane_iff hP]
      refine ⟨?_, ?_⟩
      · rw [Pi.single_apply, ite_eq_right (Ne.symm hc2)]
      · rw [Pi.single_apply, ite_eq_right (Ne.symm hc1)]
    have h1 : suMat y *ᵥ (Pm *ᵥ Pi.single c 1) = Pm *ᵥ Pi.single c 1 := h _ hw
    have h2 : mat (unitaryInvolution F p f) n ((conjEquiv P hP).symm y) *ᵥ Pi.single c 1 =
        Pi.single c 1 := by
      rw [mat_conjEquiv_symm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
        Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
    have h3 : mat (unitaryInvolution F p f) n ((conjEquiv P hP).symm y) a c =
        (Pi.single c (1 : F) : Fin n → F) a := by
      have := congrFun h2 a
      rw [Matrix.mulVec_single_one] at this
      exact this
    rw [h3, Pi.single_apply, Matrix.one_apply]

end Stabilizer

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_isLongRootSU2_map_rankOne (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {k : Fin (n / 2)} {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = 2 • weight n (lowIdx k))
    (hγ' : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k))) (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) :
    ∃ i : Su F p f n, IsLongRootSU2 F p f hn
      ((rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
        rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ)).map
          (conjEquiv P hP).toMonoidHom) i := by
  rw [rankOne_eq_fixCols hF hγ hγ']
  exact exists_isLongRootSU2_of_nondeg hF hp2 hn
    (V := colPlane (P : Matrix (Fin n) (Fin n) F) (lowIdx k))
    (nondeg_colPlane hP (lowIdx_ne_rev k k)) (finrank_colPlane hP (lowIdx_ne_rev k k))
    (fun y => mem_map_fixCols_iff P hP y)

theorem eq_map_conj_of_map_eq {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {A B : Subgroup G}
    {c : H} (h : A.map φ.toMonoidHom = (B.map φ.toMonoidHom).map (MulAut.conj c).toMonoidHom) :
    A = B.map (MulAut.conj (φ.symm c)).toMonoidHom := by
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  show A.map φ.toMonoidHom = (B.map (MulAut.conj (φ.symm c)).toMonoidHom).map φ.toMonoidHom
  rw [h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem exists_conj_of_isLongRootSU2 {n : ℕ} {hn : 2 ≤ n} {L₁ L₂ : Subgroup (Su F p f n)}
    {i₁ i₂ : Su F p f n} (h₁ : IsLongRootSU2 F p f hn L₁ i₁) (h₂ : IsLongRootSU2 F p f hn L₂ i₂) :
    ∃ c : Su F p f n, L₁ = L₂.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨g₁, hg₁, -⟩ := h₁
  obtain ⟨g₂, hg₂, -⟩ := h₂
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  rw [hg₁, hg₂]
  ext y
  rw [mem_map_conj_iff_of_group, mem_map_conj_iff_of_group, mem_map_conj_iff_of_group]
  have : g₂⁻¹ * ((g₁ * g₂⁻¹)⁻¹ * y * (g₁ * g₂⁻¹)) * g₂ = g₁⁻¹ * y * g₁ := by group
  rw [this]

end Main

section Model

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

variable {p f : ℕ} [Fact p.Prime]

theorem exists_longest_root_psu (hp : p.Prime) {n : ℕ} (hadm : StatedLieAdmissible .PSU n p f) :
    ∃ (k : Fin (n / 2)) (γ : Fin (n / 2) → ℤ),
      IsLongestRoot (Unitary.rootDatum (card_galoisField_two_mul p f hadm.2.1) n) γ ∧
        toStd n γ = 2 • weight n (lowIdx k) ∧
        toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k)) := by
  have hf : 1 ≤ f := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hM := modelUniv_PSU (n := n) (p := p) (f := f) hf
  let k : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩
  have hk1 : ¬ k.val + 1 < n / 2 := by
    show ¬ n / 2 - 1 + 1 < n / 2
    omega
  have hk2 : k.val + 1 = n / 2 := by
    show n / 2 - 1 + 1 = n / 2
    omega
  refine ⟨k, ?_⟩
  by_cases he : Even n
  · refine ⟨Pi.single k 1, ?_, toStd_last_even hk1 he, toStd_neg_last_even hk1 he⟩
    have h := isLongestRoot_single .PSU n p f hp (by trivial) hadm
    rw [hM] at h
    exact h k ⟨he, hk2⟩
  · refine ⟨2 • Pi.single k 1, ?_, ?_, ?_⟩
    · have h := isLongestRoot_two_nsmul_single_PSU n p f hp hadm he
      rw [hM] at h
      exact h k hk2
    · rw [toStd_nsmul_two, toStd_last_odd hk1 he]
    · rw [← smul_neg, toStd_nsmul_two, toStd_neg_last_odd hk1 he]

theorem exists_conj_rankOne_of_isClassicalMember {F : Type} [Field F] [Finite F] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    {k : Fin (n / 2)} {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = 2 • weight n (lowIdx k))
    (hγ' : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k)))
    {L : Subgroup (SU (unitaryInvolution F p f) n)} {z : SU (unitaryInvolution F p f) n}
    (hL : IsClassicalMember p f L z) :
    ∃ c : SU (unitaryInvolution F p f) n, L =
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
        rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ)).map
          (MulAut.conj c).toMonoidHom := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  have hL' := isClassicalMember_map_mulEquiv hL (conjEquiv P hP)
  have hLR : IsLongRootSU2 F p f hn (L.map (conjEquiv P hP).toMonoidHom) (conjEquiv P hP z) :=
    isLongRootSU2_of_isClassicalMember hF hp2 hq hn hL'
  obtain ⟨i₀, hR⟩ := exists_isLongRootSU2_map_rankOne hF hp2 hn hγ hγ' P hP
  obtain ⟨c, hc⟩ := exists_conj_of_isLongRootSU2 hLR hR
  exact ⟨(conjEquiv P hP).symm c, eq_map_conj_of_map_eq _ hc⟩

theorem classicalMembersFundamental_psu (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .PSU n p f) : ClassicalMembersFundamental p f .PSU n f hp := by
  have hf : 1 ≤ f := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn2 : 2 ≤ n := by omega
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  have hM : Generic.modelUniv .PSU n p f hp =
      ⟨↥(SU (unitaryInvolution (GaloisField p (2 * f)) p f) n),
        Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ :=
    (rfl : Generic.modelUniv .PSU n p f hp = modelUniv .PSU n p f hp).trans
      (modelUniv_PSU (n := n) (p := p) (f := f) hf)
  obtain ⟨k, γ, hγlong, hγ, hγ'⟩ := exists_longest_root_psu hp hadm
  suffices h : ∀ M : LieUniversal, M =
      ⟨↥(SU (unitaryInvolution (GaloisField p (2 * f)) p f) n),
        Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        L ∈ Generic.fundamentalSubgroups .PSU M.D from h _ hM
  intro M hM' L z hL
  subst hM'
  obtain ⟨c, hc⟩ := exists_conj_rankOne_of_isClassicalMember hF hp2 hq hn2 hγ hγ' hL
  exact ⟨c, γ, Or.inl hγlong, hc⟩

end Model

end CFSG.ClassicalInvolution.ModelFacts
