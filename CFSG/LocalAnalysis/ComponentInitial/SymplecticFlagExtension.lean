module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open Module Matrix Submodule CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsTotallyIsotropic (B : BilinForm K V) (W : Submodule K V) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, B x y = 0

@[expose] def IsCompleteIsotropicFlag (B : BilinForm K V) (r : ℕ) (F : ℕ → Submodule K V) :
    Prop :=
  (∀ i ≤ r, finrank K (F i) = i) ∧ (∀ i < r, F i ≤ F (i + 1)) ∧
    ∀ i ≤ r, IsTotallyIsotropic B (F i)

@[expose] def IsSymplecticBasis {r : ℕ} (B : BilinForm K V) (b : Basis (Fin r ⊕ Fin r) K V) :
    Prop :=
  BilinForm.toMatrix b B = fromBlocks 0 1 (-1) 0

theorem IsTotallyIsotropic.mono {B : BilinForm K V} {W W' : Submodule K V}
    (h : IsTotallyIsotropic B W') (hW : W ≤ W') : IsTotallyIsotropic B W :=
  fun x hx y hy => h x (hW hx) y (hW hy)

theorem IsSymplecticBasis.isTotallyIsotropic {r : ℕ} {B : BilinForm K V}
    {b : Basis (Fin r ⊕ Fin r) K V} (hb : IsSymplecticBasis B b) (s : Set (Fin r)) :
    IsTotallyIsotropic B (span K (b '' (Sum.inl '' s))) := by
  have hpair : ∀ i j : Fin r, B (b (Sum.inl i)) (b (Sum.inl j)) = 0 := fun i j => by
    have := congrFun₂ hb (Sum.inl i) (Sum.inl j)
    rwa [BilinForm.toMatrix_apply, fromBlocks_apply₁₁, Matrix.zero_apply] at this
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨i, -, rfl⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨j, -, rfl⟩, rfl⟩ := hy
      exact hpair i j
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  | zero => simp
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply, hx, hz, add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem finrank_span_image_lt {n : ℕ} {u : Fin n → V} (hu : LinearIndependent K u) {i : ℕ}
    (hi : i ≤ n) : finrank K (span K (u '' {j : Fin n | (j : ℕ) < i})) = i := by
  have hset : {j : Fin n | (j : ℕ) < i} = Set.range (Fin.castLE hi) := by
    ext j
    constructor
    · intro hj
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [hset, ← Set.range_comp, finrank_span_eq_card (hu.comp _ (Fin.castLE_injective hi)),
    Fintype.card_fin]

theorem finrank_span_inl_image {r : ℕ} (b : Basis (Fin r ⊕ Fin r) K V) {i : ℕ} (hi : i ≤ r) :
    finrank K (span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < i}))) = i := by
  rw [← Set.image_comp]
  exact finrank_span_image_lt (b.linearIndependent.comp _ Sum.inl_injective) hi

theorem flag_le {W : ℕ → Submodule K V} {k : ℕ} (hmono : ∀ i < k, W i ≤ W (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) : W i ≤ W j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hmono j (by omega))

theorem finrank_comap_orthogonal_add_one [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsAlt) {a f : V} (hfe : B f a = 1) {W : Submodule K V}
    (haW : a ∈ W) (hW : ∀ x ∈ W, B a x = 0) :
    finrank K (W.comap (B.orthogonal (span K {a, f})).subtype) + 1 = finrank K W := by
  set Z := B.orthogonal (span K {a, f})
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfe
    exact zero_ne_one hfe
  have hcomap : W.comap Z.subtype = (W ⊓ Z).comap Z.subtype := by
    rw [comap_inf, comap_subtype_self, inf_top_eq]
  rw [hcomap, (comapSubtypeEquivOfLe (inf_le_right : W ⊓ Z ≤ Z)).finrank_eq]
  have hsup : span K {a} ⊔ (W ⊓ Z) = W := by
    refine le_antisymm (sup_le ((span_singleton_le_iff_mem _ _).mpr haW) inf_le_left)
      fun x hx => ?_
    have hxZ : x - B f x • a ∈ Z := by
      have h := hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe x
      rwa [hW x hx, zero_smul, add_zero] at h
    have hsum : x = B f x • a + (x - B f x • a) := by abel
    rw [hsum]
    exact add_mem_sup (smul_mem _ _ (mem_span_singleton_self a))
      ⟨sub_mem hx (smul_mem _ _ haW), hxZ⟩
  have hinf : span K {a} ⊓ (W ⊓ Z) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, -, hzZ⟩
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
    have h := (BilinForm.mem_orthogonal_iff.mp hzZ) f (subset_span (by simp))
    rw [map_smul, hfe, smul_eq_mul, mul_one] at h
    rw [h, zero_smul]
    exact zero_mem _
  have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {a}) (W ⊓ Z)
  rw [hsup, hinf, finrank_bot, add_zero, finrank_span_singleton ha0] at h
  omega

theorem exists_basis_J_of_flag : ∀ (r : ℕ) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : BilinForm K V), B.IsAlt → B.Nondegenerate →
    finrank K V = 2 * r → ∀ (k : ℕ), k ≤ r → ∀ (W : ℕ → Submodule K V),
      (∀ i ≤ k, finrank K (W i) = i) → (∀ i < k, W i ≤ W (i + 1)) →
      IsTotallyIsotropic B (W k) →
      ∃ b : Basis (Fin r ⊕ Fin r) K V, (∀ x y, B (b x) (b y) = Matrix.J (Fin r) K x y) ∧
        ∀ j : Fin r, (j : ℕ) < k → b (Sum.inl j) ∈ W (j + 1) := by
  intro r
  induction r with
  | zero =>
    intro V _ _ _ B _ _ hV k _ W _ _ _
    have : Subsingleton V := finrank_zero_iff.mp (by rw [hV])
    exact ⟨Basis.empty V, fun x => isEmptyElim x, fun j => j.elim0⟩
  | succ r ih =>
    intro V _ _ _ B hB hnd hV k hk W hdim hmono hiso
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
      have hm : m = r + 1 := by
        have := finrank_eq_card_basis b
        simp only [Fintype.card_sum, Fintype.card_fin] at this
        omega
      subst hm
      exact ⟨b, fun x y => by rw [← hb, BilinForm.toMatrix_apply],
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    have h1 : finrank K (W 1) = 1 := hdim 1 hk1
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ W 1, a ≠ 0 := (Submodule.ne_bot_iff _).mp fun h => by
      rw [h, finrank_bot] at h1
      exact zero_ne_one h1
    obtain ⟨y, hy⟩ : ∃ y, B y a ≠ 0 := by
      by_contra! h
      exact ha0 (hnd.2 a h)
    set f := (B y a)⁻¹ • y with hf
    have hfe : B f a = 1 := by
      rw [hf, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy]
    set Z := B.orthogonal (span K {a, f}) with hZdef
    have hZ : finrank K Z = 2 * r := by
      have : finrank K Z + 2 = finrank K V := hB.finrank_orthogonal_span_pair_add_two hnd hfe
      omega
    have hWa : ∀ i, 1 ≤ i → i ≤ k → a ∈ W i := fun i hi hik => flag_le hmono hi hik ha
    have hiso' : ∀ i ≤ k, ∀ x ∈ W i, B a x = 0 := fun i hik x hx =>
      hiso a (flag_le hmono hk1 le_rfl ha) x (flag_le hmono hik le_rfl hx)
    set W' : ℕ → Submodule K Z := fun i => (W (i + 1)).comap Z.subtype with hW'
    have hdim' : ∀ i ≤ k - 1, finrank K (W' i) = i := by
      intro i hi
      have h := finrank_comap_orthogonal_add_one hB hfe (hWa (i + 1) (by omega) (by omega))
        (hiso' (i + 1) (by omega))
      rw [hdim (i + 1) (by omega)] at h
      exact Nat.succ_injective h
    have hmono' : ∀ i < k - 1, W' i ≤ W' (i + 1) := fun i hi =>
      comap_mono (hmono (i + 1) (by omega))
    have hiso'' : IsTotallyIsotropic (B.restrict Z) (W' (k - 1)) := by
      intro x hx z hz
      rw [BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      have hk' : k - 1 + 1 = k := by omega
      have hx' : (x : V) ∈ W k := by
        have := hx
        simp only [hW', mem_comap, subtype_apply, hk'] at this
        exact this
      have hz' : (z : V) ∈ W k := by
        have := hz
        simp only [hW', mem_comap, subtype_apply, hk'] at this
        exact this
      exact hiso _ hx' _ hz'
    obtain ⟨c, hc, hcW⟩ := ih (B.restrict Z) (fun z => hB.self_eq_zero z)
      (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd) hZ (k - 1) (by omega) W' hdim'
      hmono' hiso''
    have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin r) K x y := fun x y => by
      rw [← hc x y, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    obtain ⟨b, hb, hbd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
    refine ⟨b, hb, fun j hj => ?_⟩
    rw [hbd]
    induction j using Fin.cases with
    | zero => simpa using ha
    | succ j =>
      have h := hcW j (by simp at hj; omega)
      simp only [hW', mem_comap, subtype_apply] at h
      simpa using h

theorem exists_isSymplecticBasis_of_J {r : ℕ} {B : BilinForm K V} (b : Basis (Fin r ⊕ Fin r) K V)
    (hb : ∀ x y, B (b x) (b y) = Matrix.J (Fin r) K x y) :
    ∃ b' : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b' ∧
      ∀ j, b' (Sum.inl j) = b (Sum.inl j) := by
  refine ⟨b.unitsSMul (Sum.elim 1 (-1)), ?_, fun j => by simp [Basis.unitsSMul_apply]⟩
  ext (x | x) (y | y) <;>
    simp [BilinForm.toMatrix_apply, Basis.unitsSMul_apply, hb, Matrix.J, Units.smul_def,
      one_apply]

theorem exists_symplecticBasis_of_flag [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) {k : ℕ} (hk : k ≤ r)
    (W : ℕ → Submodule K V) (hdim : ∀ i ≤ k, finrank K (W i) = i)
    (hmono : ∀ i < k, W i ≤ W (i + 1)) (hiso : IsTotallyIsotropic B (W k)) :
    ∃ b : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b ∧
      ∀ i ≤ k, W i = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < i})) := by
  obtain ⟨b₀, hb₀, hW₀⟩ := exists_basis_J_of_flag r B hB hnd hV k hk W hdim hmono hiso
  obtain ⟨b, hb, hbb₀⟩ := exists_isSymplecticBasis_of_J b₀ hb₀
  refine ⟨b, hb, fun i hik => ?_⟩
  refine (eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [span_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hbb₀]
    exact flag_le hmono hj hik (hW₀ j (by simp at hj; omega))
  · rw [finrank_span_inl_image b (hik.trans hk), hdim i hik]

theorem finrank_le_of_isTotallyIsotropic [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) {W : Submodule K V}
    (hW : IsTotallyIsotropic B W) : finrank K W ≤ r := by
  have h := BilinForm.finrank_add_finrank_orthogonal hB.isRefl W
  rw [BilinForm.orthogonal_top_eq_bot hnd, inf_bot_eq, finrank_bot, add_zero] at h
  have hle : W ≤ B.orthogonal W := fun x hx =>
    (BilinForm.mem_orthogonal_iff).mpr fun y hy => hW y hy x hx
  have := Submodule.finrank_mono hle
  omega

theorem exists_completeIsotropicFlag [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) {W : Submodule K V}
    (hW : IsTotallyIsotropic B W) :
    ∃ b : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b ∧
      W = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < finrank K W})) := by
  set d := finrank K W
  have hd : d ≤ r := finrank_le_of_isTotallyIsotropic hB hnd hV hW
  set v := Module.finBasis K W
  set Wf : ℕ → Submodule K V := fun i =>
    span K ((fun j : Fin d => (v j : V)) '' {j | (j : ℕ) < i}) with hWf
  have hli : LinearIndependent K (fun j : Fin d => (v j : V)) :=
    v.linearIndependent.map' W.subtype (ker_subtype W)
  have hdim : ∀ i ≤ d, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
  have hmono : ∀ i < d, Wf i ≤ Wf (i + 1) := fun i _ =>
    span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hWd : Wf d = W := by
    refine eq_of_le_of_finrank_eq ?_ (by rw [hdim d le_rfl])
    rw [span_le]
    rintro _ ⟨j, -, rfl⟩
    exact (v j).2
  obtain ⟨b, hb, hbW⟩ := exists_symplecticBasis_of_flag hB hnd hV hd Wf hdim hmono
    (by rw [hWd]; exact hW)
  exact ⟨b, hb, by rw [← hbW d le_rfl, hWd]⟩

section Standard

variable {r : ℕ} {K : Type} [Field K]

theorem pairedSympForm_isAlt : (pairedSympForm K r).IsAlt :=
  fun v => pairedSympForm_self v

theorem pairedSympForm_nondegenerate : (pairedSympForm K r).Nondegenerate := by
  rw [pairedSympForm, BilinForm.nondegenerate_toBilin'_iff_det_ne_zero,
    CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J, det_neg, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact (isUnit_det_J (Fin r) K).ne_zero

theorem finrank_standard : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
  simp [two_mul]

theorem toMatrix_pairedSympForm :
    BilinForm.toMatrix (Pi.basisFun K (Fin r ⊕ Fin r)) (pairedSympForm K r) =
      fromBlocks 0 1 (-1) 0 := by
  rw [BilinForm.toMatrix_basisFun, pairedSympForm, BilinForm.toMatrix'_toBilin']

theorem exists_statedSp_mulVec_basis {b b' : Basis (Fin r ⊕ Fin r) K (Fin r ⊕ Fin r → K)}
    (hb : IsSymplecticBasis (pairedSympForm K r) b)
    (hb' : IsSymplecticBasis (pairedSympForm K r) b') :
    ∃ g : StatedSp r K, ∀ x, ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ b x = b' x := by
  set e := b.isometryEquivOfToMatrixEq b' (hb.trans hb'.symm)
  set φ : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) := e.toLinearEquiv
  have hφ : φ ∈ CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup
      (pairedSympForm K r) :=
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => e.map_app y x
  set M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin r ⊕ Fin r)) φ
  have hM : M ∈ StatedSp r K := by
    have h := (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometry_iff_matrix
      (Pi.basisFun K (Fin r ⊕ Fin r)) (pairedSympForm K r) φ).mp hφ
    rw [toMatrix_pairedSympForm] at h
    exact SymplecticTorusWeyl.mem_statedSp_iff.mpr h
  refine ⟨⟨M, hM⟩, fun x => ?_⟩
  have h := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
    (Pi.basisFun K (Fin r ⊕ Fin r)) φ (b x)
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at h
  change M.val *ᵥ b x = b' x
  rw [h]
  exact b.isometryEquivOfToMatrixEq_apply_basis b' (hb.trans hb'.symm) x

theorem map_span_basis {g : StatedSp r K} {b b' : Basis (Fin r ⊕ Fin r) K (Fin r ⊕ Fin r → K)}
    (hg : ∀ x, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ b x =
      b' x) (s : Set (Fin r ⊕ Fin r)) :
    (span K (b '' s)).map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = span K (b' '' s) := by
  rw [map_span, ← Set.image_comp]
  congr 1
  exact Set.image_congr fun x _ => hg x

theorem exists_statedSp_map_flag {F F' : ℕ → Submodule K (Fin r ⊕ Fin r → K)}
    (hF : IsCompleteIsotropicFlag (pairedSympForm K r) r F)
    (hF' : IsCompleteIsotropicFlag (pairedSympForm K r) r F') :
    ∃ g : StatedSp r K, ∀ i, 1 ≤ i → i ≤ r →
      (F i).map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = F' i := by
  obtain ⟨b, hb, hbF⟩ := exists_symplecticBasis_of_flag pairedSympForm_isAlt
    pairedSympForm_nondegenerate finrank_standard le_rfl F hF.1 hF.2.1 (hF.2.2 r le_rfl)
  obtain ⟨b', hb', hbF'⟩ := exists_symplecticBasis_of_flag pairedSympForm_isAlt
    pairedSympForm_nondegenerate finrank_standard le_rfl F' hF'.1 hF'.2.1 (hF'.2.2 r le_rfl)
  obtain ⟨g, hg⟩ := exists_statedSp_mulVec_basis hb hb'
  refine ⟨g, fun i _ hi => ?_⟩
  rw [hbF i hi, hbF' i hi, ← Set.image_comp, ← Set.image_comp]
  rw [Set.image_comp, Set.image_comp b']
  exact map_span_basis hg _

theorem exists_statedSp_map_eq {W W' : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W)
    (hW' : IsTotallyIsotropic (pairedSympForm K r) W') (hd : finrank K W = finrank K W') :
    ∃ g : StatedSp r K, W.map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W' := by
  obtain ⟨b, hb, hbW⟩ := exists_completeIsotropicFlag pairedSympForm_isAlt
    pairedSympForm_nondegenerate finrank_standard hW
  obtain ⟨b', hb', hbW'⟩ := exists_completeIsotropicFlag pairedSympForm_isAlt
    pairedSympForm_nondegenerate finrank_standard hW'
  obtain ⟨g, hg⟩ := exists_statedSp_mulVec_basis hb hb'
  refine ⟨g, ?_⟩
  rw [hbW, hbW', hd]
  exact map_span_basis hg _

end Standard

theorem symplectic_higher_isotropic_flag_extension :
    (∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
      (B : BilinForm K V), B.IsAlt → B.Nondegenerate → finrank K V = 2 * r →
      ∀ (k : ℕ) (W : ℕ → Submodule K V), 1 ≤ k → k ≤ r → (∀ i ≤ k, finrank K (W i) = i) →
        (∀ i < k, W i < W (i + 1)) → (∀ i ≤ k, IsTotallyIsotropic B (W i)) →
        ∃ b : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b ∧
          ∀ i, 1 ≤ i → i ≤ k → W i = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < i}))) ∧
    (∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
      (B : BilinForm K V), B.IsAlt → B.Nondegenerate → finrank K V = 2 * r →
      ∀ W : Submodule K V, IsTotallyIsotropic B W → finrank K W ≤ r ∧
        ∃ F : ℕ → Submodule K V, IsCompleteIsotropicFlag B r F ∧ F (finrank K W) = W) ∧
    (∀ {K : Type} [Field K] {r : ℕ} (F F' : ℕ → Submodule K (Fin r ⊕ Fin r → K)),
      IsCompleteIsotropicFlag (pairedSympForm K r) r F →
      IsCompleteIsotropicFlag (pairedSympForm K r) r F' →
      ∃ g : StatedSp r K, ∀ i, 1 ≤ i → i ≤ r →
        (F i).map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = F' i) ∧
    (∀ {K : Type} [Field K] {r : ℕ} (W W' : Submodule K (Fin r ⊕ Fin r → K)),
      IsTotallyIsotropic (pairedSympForm K r) W →
      IsTotallyIsotropic (pairedSympForm K r) W' → finrank K W = finrank K W' →
      ∃ g : StatedSp r K, W.map (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W') := by
  refine ⟨fun B hB hnd hV k W _ hk hdim hmono hiso => ?_, fun B hB hnd hV W hW => ?_,
    fun F F' hF hF' => exists_statedSp_map_flag hF hF',
    fun W W' hW hW' hd => exists_statedSp_map_eq hW hW' hd⟩
  · obtain ⟨b, hb, hbW⟩ := exists_symplecticBasis_of_flag hB hnd hV hk W hdim
      (fun i hi => (hmono i hi).le) (hiso k le_rfl)
    exact ⟨b, hb, fun i _ hi => hbW i hi⟩
  · refine ⟨finrank_le_of_isTotallyIsotropic hB hnd hV hW, ?_⟩
    obtain ⟨b, hb, hbW⟩ := exists_completeIsotropicFlag hB hnd hV hW
    refine ⟨fun i => span _ (b '' (Sum.inl '' {j : Fin _ | (j : ℕ) < i})),
      ⟨fun i hi => finrank_span_inl_image b hi, fun i _ => span_mono (Set.image_mono
        (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)),
        fun i _ => hb.isTotallyIsotropic _⟩, hbW.symm⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
