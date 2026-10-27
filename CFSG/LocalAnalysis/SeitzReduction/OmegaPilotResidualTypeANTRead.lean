module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviEqual

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)

section Group

theorem mapsTo_of_mapsTo_of_isEmpty {X : Type*} [Group X] [Finite X] (N₁ N₂ N₃ : Subgroup X)
    [N₁.Normal] [N₂.Normal] [N₃.Normal] (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)),
      ∀ M : Subgroup X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    [IsSimpleGroup (X ⧸ N₃)] (hnc : ∃ a b : X ⧸ N₃, a * b ≠ b * a)
    (h₁ : IsEmpty (X ⧸ N₁ ≃* X ⧸ N₃)) (h23 : N₂ ≠ N₃) (θ : MulAut X)
    (hθ : ∀ m ∈ N₂, θ m ∈ N₂) : ∀ m ∈ N₃, θ m ∈ N₃ := by
  set M : Subgroup X := N₃.map θ.toMonoidHom with hMdef
  have hMn : M.Normal := ‹N₃.Normal›.map _ θ.surjective
  set e : X ⧸ N₃ ≃* X ⧸ M := QuotientGroup.congr N₃ M θ rfl with he
  have : IsSimpleGroup (X ⧸ M) := MulEquiv.isSimpleGroup e.symm
  have hnc' : ∃ a b : X ⧸ M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' := congrArg e.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : N₁ ⊓ N₂ ⊓ N₃ ≤ M := le_of_isPGroup_of_simple hnc' h123
  have hMtop : M ≠ ⊤ := by
    rintro hM
    have hnt : Nontrivial (X ⧸ M) := IsSimpleGroup.toNontrivial
    have hsub : Subsingleton (X ⧸ M) := by
      rw [hM]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
  have hN₃top : N₃ ≠ ⊤ := by
    rintro hN
    have hnt : Nontrivial (X ⧸ N₃) := IsSimpleGroup.toNontrivial
    have hsub : Subsingleton (X ⧸ N₃) := by
      rw [hN]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
  have key : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)), N ≤ M → M = N := fun N hN hle =>
    (hq N hN M hMn hle).resolve_right hMtop
  have hM3 : M = N₃ := by
    rcases le_or_le_of_inf_le hnc' hinf with h | h
    · rcases le_or_le_of_inf_le hnc' h with h' | h'
      · exfalso
        have hM1 : M = N₁ := key N₁ (by simp) h'
        exact h₁.false ((QuotientGroup.quotientMulEquivOfEq hM1.symm).trans e.symm)
      · exfalso
        have hM2 : M = N₂ := key N₂ (by simp) h'
        have hle : N₂.map θ.toMonoidHom ≤ N₃.map θ.toMonoidHom := by
          rw [← hMdef, hM2]
          rintro _ ⟨m, hm, rfl⟩
          exact hθ m hm
        have h23' : N₂ ≤ N₃ := (Subgroup.map_le_map_iff_of_injective θ.injective).mp hle
        rcases hq N₂ (by simp) N₃ inferInstance h23' with h3 | h3
        · exact h23 h3.symm
        · exact hN₃top h3
    · exact key N₃ (by simp) h
  intro m hm
  have hθm : θ m ∈ M := ⟨m, hm, rfl⟩
  rwa [hM3] at hθm

end Group

section Trace

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ)
  (h : ℓ + 2 = n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hq4 : 4 ≤ Nat.card K)

omit [Finite K] in
include P in
theorem symm_mem_lowPerp_of_mapsTo (hn : 3 ≤ n) (g : similarityPairs (coordinateQuadPlus n K))
    (hTW : ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) :
    (coordinateSemilinearMap g.val).symm v ∈ lowPerp K n ℓ := by
  have hB := (regular_coordinateQuadPlus n K hn).1
  have h1 := symm_mem_ker_of_mapsTo_range hB (lowNil P) (polar_lowNil_left P) g
    (by rw [range_lowNil]; exact hTW) v (by rw [ker_lowNil]; exact hv)
  rwa [ker_lowNil] at h1

omit [Finite K] in
include P in
theorem kappa_rel (hn : 3 ≤ n) (g : similarityPairs (coordinateQuadPlus n K))
    (hTW : ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    (y : matrixProjectiveDerived (coordinateQuadPlus n K)) (t : K)
    (hy : ∀ u ∈ lowPerp K n ℓ, projLift hQ y (projLift hQ y u) - t • projLift hQ y u + u ∈
      lowSpan K n ℓ) :
    ∀ v ∈ lowPerp K n ℓ,
      projLift hQ (matrixProjectiveConjugationHom _ g y)
          (projLift hQ (matrixProjectiveConjugationHom _ g y) v) -
        g.val.right t • projLift hQ (matrixProjectiveConjugationHom _ g y) v + v ∈
          lowSpan K n ℓ := by
  intro v hv
  set T := coordinateSemilinearMap g.val with hT
  have hu := symm_mem_lowPerp_of_mapsTo P hn g hTW hv
  have hv' : v = T (T.symm v) := (T.apply_symm_apply v).symm
  have e1 : projLift hQ (matrixProjectiveConjugationHom _ g y) v =
      T (projLift hQ y (T.symm v)) := by
    conv_lhs => rw [hv']
    exact projLift_kappa_apply hQ g y (T.symm v)
  have e2 : projLift hQ (matrixProjectiveConjugationHom _ g y)
      (projLift hQ (matrixProjectiveConjugationHom _ g y) v) =
        T (projLift hQ y (projLift hQ y (T.symm v))) := by
    rw [e1]
    exact projLift_kappa_apply hQ g y _
  have key : T (projLift hQ y (projLift hQ y (T.symm v)) - t • projLift hQ y (T.symm v) +
      T.symm v) = T (projLift hQ y (projLift hQ y (T.symm v))) -
        g.val.right t • T (projLift hQ y (T.symm v)) + v := by
    rw [map_add, map_sub, hT, coordinateSemilinearMap_smul, AddEquiv.apply_symm_apply]
  rw [e2, e1, ← key]
  exact hTW _ (hy _ hu)

theorem trace_coreSLPair_fst_kappa (hn : 3 ≤ n)
    (g : similarityPairs (coordinateQuadPlus n K))
    (hgX : ∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P)
    (hTW : ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    (h₂ : ∀ m : typeACore K P, (coreSLPair P h hQ hq4 m).1 = 1 →
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX m)).1 = 1)
    (h₃ : ∀ m : typeACore K P, (coreSLPair P h hQ hq4 m).2 = 1 →
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX m)).2 = 1)
    (x : typeACore K P) :
    Matrix.trace ((coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX x)).1 :
        Matrix (Fin 2) (Fin 2) K) =
      g.val.right (Matrix.trace ((coreSLPair P h hQ hq4 x).1 : Matrix (Fin 2) (Fin 2) K)) := by
  obtain ⟨y, hy⟩ := coreSLPair_surjective P h hQ hq4 ((coreSLPair P h hQ hq4 x).1, 1)
  have hy1 : (coreSLPair P h hQ hq4 y).1 = (coreSLPair P h hQ hq4 x).1 := by rw [hy]
  have hy2 : (coreSLPair P h hQ hq4 y).2 = 1 := by rw [hy]
  have hz : (coreSLPair P h hQ hq4 (y⁻¹ * x)).1 = 1 := by
    rw [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hy1, inv_mul_cancel]
  have hx : x = y * (y⁻¹ * x) := by group
  have hθx : (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX x)).1 =
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y)).1 := by
    conv_lhs => rw [hx]
    rw [map_mul, map_mul, Prod.fst_mul, h₂ _ hz, mul_one]
  have hθy : (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y)).2 = 1 :=
    h₃ y hy2
  have hrel := kappa_rel P hQ hn g hTW (y : matrixProjectiveDerived _) _
    (fun u hu => projLift_rel_left P h hQ hq4 y hy2 hu)
  have hθyC : ((restrictAutOfMapsTo _ (typeACore K P) hgX y : typeACore K P) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) =
        matrixProjectiveConjugationHom _ g y := coe_restrictAutOfMapsTo _ _ _ y
  have key := eq_trace_left P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y) hθy
    (g.val.right (Matrix.trace ((coreSLPair P h hQ hq4 y).1 : Matrix (Fin 2) (Fin 2) K)))
    (by rw [hθyC]; exact hrel)
  rw [hθx, ← key, hy1]

theorem trace_coreSLPair_snd_kappa (hn : 3 ≤ n)
    (g : similarityPairs (coordinateQuadPlus n K))
    (hgX : ∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P)
    (hTW : ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    (h₂ : ∀ m : typeACore K P, (coreSLPair P h hQ hq4 m).1 = 1 →
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX m)).1 = 1)
    (h₃ : ∀ m : typeACore K P, (coreSLPair P h hQ hq4 m).2 = 1 →
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX m)).2 = 1)
    (x : typeACore K P) :
    Matrix.trace ((coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX x)).2 :
        Matrix (Fin 2) (Fin 2) K) =
      g.val.right (Matrix.trace ((coreSLPair P h hQ hq4 x).2 : Matrix (Fin 2) (Fin 2) K)) := by
  obtain ⟨y, hy⟩ := coreSLPair_surjective P h hQ hq4 (1, (coreSLPair P h hQ hq4 x).2)
  have hy1 : (coreSLPair P h hQ hq4 y).1 = 1 := by rw [hy]
  have hy2 : (coreSLPair P h hQ hq4 y).2 = (coreSLPair P h hQ hq4 x).2 := by rw [hy]
  have hz : (coreSLPair P h hQ hq4 (y⁻¹ * x)).2 = 1 := by
    rw [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hy2, inv_mul_cancel]
  have hx : x = y * (y⁻¹ * x) := by group
  have hθx : (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX x)).2 =
      (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y)).2 := by
    conv_lhs => rw [hx]
    rw [map_mul, map_mul, Prod.snd_mul, h₃ _ hz, mul_one]
  have hθy : (coreSLPair P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y)).1 = 1 :=
    h₂ y hy1
  have hrel := kappa_rel P hQ hn g hTW (y : matrixProjectiveDerived _) _
    (fun u hu => projLift_rel_right P h hQ hq4 y hy1 hu)
  have hθyC : ((restrictAutOfMapsTo _ (typeACore K P) hgX y : typeACore K P) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) =
        matrixProjectiveConjugationHom _ g y := coe_restrictAutOfMapsTo _ _ _ y
  have key := eq_trace_right P h hQ hq4 (restrictAutOfMapsTo _ (typeACore K P) hgX y) hθy
    (g.val.right (Matrix.trace ((coreSLPair P h hQ hq4 y).2 : Matrix (Fin 2) (Fin 2) K)))
    (by rw [hθyC]; exact hrel)
  rw [hθx, ← key, hy2]

end Trace

section Sections

open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlockEquivOne longBlock mat_longBlock
  stdBlock stdBlock_blockMat)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ)
  (h : ℓ + 2 = n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hq4 : 4 ≤ Nat.card K)

omit [Finite K] [CharP K 2] in
theorem spMatTrace_longBlockEquivOne (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    spMatTrace (longBlockEquivOne K A) = Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) := by
  have hM : ((longBlockEquivOne K A : StatedSp 1 K) : GL (Fin 1 ⊕ Fin 1) K).val =
      CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl 0) (Sum.inr 0) (A : Matrix (Fin 2) (Fin 2) K) :=
    mat_longBlock 0 A
  have h00 := congrFun (congrFun (stdBlock_blockMat (0 : Fin 1) (A : Matrix (Fin 2) (Fin 2) K)) 0) 0
  have h11 := congrFun (congrFun (stdBlock_blockMat (0 : Fin 1) (A : Matrix (Fin 2) (Fin 2) K)) 1) 1
  simp only [stdBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11
  rw [spMatTrace, hM, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one,
    Matrix.trace_fin_two]
  simp only [Matrix.diag_apply]
  rw [h00, h11]

@[expose] noncomputable def coreSpLeft : typeACore K P →* StatedSp 1 K :=
  (longBlockEquivOne K).toMonoidHom.comp ((MonoidHom.fst _ _).comp (coreSLPair P h hQ hq4))

@[expose] noncomputable def coreSpRight : typeACore K P →* StatedSp 1 K :=
  (longBlockEquivOne K).toMonoidHom.comp ((MonoidHom.snd _ _).comp (coreSLPair P h hQ hq4))

theorem mem_ker_coreSpLeft (x : typeACore K P) :
    x ∈ (coreSpLeft P h hQ hq4).ker ↔ (coreSLPair P h hQ hq4 x).1 = 1 := by
  rw [MonoidHom.mem_ker]
  exact MulEquiv.map_eq_one_iff (longBlockEquivOne K)

theorem mem_ker_coreSpRight (x : typeACore K P) :
    x ∈ (coreSpRight P h hQ hq4).ker ↔ (coreSLPair P h hQ hq4 x).2 = 1 := by
  rw [MonoidHom.mem_ker]
  exact MulEquiv.map_eq_one_iff (longBlockEquivOne K)

theorem coreSpLeft_surjective : Function.Surjective (coreSpLeft P h hQ hq4) := by
  intro A
  obtain ⟨x, hx⟩ := coreSLPair_surjective P h hQ hq4 ((longBlockEquivOne K).symm A, 1)
  refine ⟨x, ?_⟩
  change longBlockEquivOne K (coreSLPair P h hQ hq4 x).1 = A
  rw [hx, MulEquiv.apply_symm_apply]

theorem coreSpRight_surjective : Function.Surjective (coreSpRight P h hQ hq4) := by
  intro B
  obtain ⟨x, hx⟩ := coreSLPair_surjective P h hQ hq4 (1, (longBlockEquivOne K).symm B)
  refine ⟨x, ?_⟩
  change longBlockEquivOne K (coreSLPair P h hQ hq4 x).2 = B
  rw [hx, MulEquiv.apply_symm_apply]

theorem spMatTrace_coreSpLeft (x : typeACore K P) :
    spMatTrace (coreSpLeft P h hQ hq4 x) =
      Matrix.trace ((coreSLPair P h hQ hq4 x).1 : Matrix (Fin 2) (Fin 2) K) :=
  spMatTrace_longBlockEquivOne _

theorem spMatTrace_coreSpRight (x : typeACore K P) :
    spMatTrace (coreSpRight P h hQ hq4 x) =
      Matrix.trace ((coreSLPair P h hQ hq4 x).2 : Matrix (Fin 2) (Fin 2) K) :=
  spMatTrace_longBlockEquivOne _

theorem ker_coreSpLeft_inf_ker_coreSpRight :
    (coreSpLeft P h hQ hq4).ker ⊓ (coreSpRight P h hQ hq4).ker =
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker := by
  ext x
  rw [Subgroup.mem_inf, mem_ker_coreSpLeft, mem_ker_coreSpRight, MonoidHom.mem_ker,
    ← coreSLPair_eq_one_iff P h hQ hq4 x, Prod.ext_iff]
  rfl

theorem spLeviSection_coreSpLeft {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hTW : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    (h₃ : ∀ (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
      (hβ : ∀ x ∈ typeACore K P, β x ∈ typeACore K P),
      (∀ m ∈ (coreSpLeft P h hQ hq4).ker,
        restrictAutOfMapsTo β _ hβ m ∈ (coreSpLeft P h hQ hq4).ker) →
      ∀ m ∈ (coreSpRight P h hQ hq4).ker,
        restrictAutOfMapsTo β _ hβ m ∈ (coreSpRight P h hQ hq4).ker) :
    SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) (coreSpLeft P h hQ hq4).ker := by
  refine spLeviSection_of_hom _ le_rfl (coreSpLeft P h hQ hq4) (coreSpLeft_surjective P h hQ hq4)
    fun β hβ hN x => ?_
  obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
  have hfp : plusFieldPart hf hK hn (matrixProjectiveConjugationHom _ g) = g.val.right :=
    orthAutFieldPart_kappa _ _ g
  rw [spMatTrace_coreSpLeft, spMatTrace_coreSpLeft, hfp]
  exact trace_coreSLPair_fst_kappa P h hQ hq4 (by omega) g hβ (hTW g hβ)
    (fun m hm => (mem_ker_coreSpLeft P h hQ hq4 _).mp
      (hN m ((mem_ker_coreSpLeft P h hQ hq4 m).mpr hm)))
    (fun m hm => (mem_ker_coreSpRight P h hQ hq4 _).mp
      (h₃ _ hβ hN m ((mem_ker_coreSpRight P h hQ hq4 m).mpr hm))) x

theorem spLeviSection_coreSpRight {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hTW : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ)
    (h₂ : ∀ (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
      (hβ : ∀ x ∈ typeACore K P, β x ∈ typeACore K P),
      (∀ m ∈ (coreSpRight P h hQ hq4).ker,
        restrictAutOfMapsTo β _ hβ m ∈ (coreSpRight P h hQ hq4).ker) →
      ∀ m ∈ (coreSpLeft P h hQ hq4).ker,
        restrictAutOfMapsTo β _ hβ m ∈ (coreSpLeft P h hQ hq4).ker) :
    SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) (coreSpRight P h hQ hq4).ker := by
  refine spLeviSection_of_hom _ le_rfl (coreSpRight P h hQ hq4)
    (coreSpRight_surjective P h hQ hq4) fun β hβ hN x => ?_
  obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
  have hfp : plusFieldPart hf hK hn (matrixProjectiveConjugationHom _ g) = g.val.right :=
    orthAutFieldPart_kappa _ _ g
  rw [spMatTrace_coreSpRight, spMatTrace_coreSpRight, hfp]
  exact trace_coreSLPair_snd_kappa P h hQ hq4 (by omega) g hβ (hTW g hβ)
    (fun m hm => (mem_ker_coreSpLeft P h hQ hq4 _).mp
      (h₂ _ hβ hN m ((mem_ker_coreSpLeft P h hQ hq4 m).mpr hm)))
    (fun m hm => (mem_ker_coreSpRight P h hQ hq4 _).mp
      (hN m ((mem_ker_coreSpRight P h hQ hq4 m).mpr hm))) x

end Sections

end CFSG.SeitzReduction.OmegaPilot
