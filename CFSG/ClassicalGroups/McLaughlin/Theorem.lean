module

public import CFSG.ClassicalGroups.McLaughlin.Centres
public import CFSG.ClassicalGroups.McLaughlin.SympForm
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.ClassicalGroups.McLaughlin

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem smulRight_mul_smulRight_same (φ : Dual K V) (u w : V) :
    φ.smulRight u * φ.smulRight w = φ w • φ.smulRight u := by
  ext z
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul,
    smul_smul, LinearMap.smul_apply]
  module

private theorem isRootElt_add_vec {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {u w : V}
    {φ : Dual K V} (hu : IsRootElt X u φ) (hw : IsRootElt X w φ) :
    IsRootElt X (u + w) φ := by
  refine ⟨by simp [hu.1, hw.1], fun c => ?_⟩
  obtain ⟨g, hg, hgu⟩ := hu.2 c
  obtain ⟨h, hh, hhw⟩ := hw.2 c
  refine ⟨g * h, X.mul_mem hg hh, ?_⟩
  have hsum : φ.smulRight (u + w) = φ.smulRight u + φ.smulRight w := by
    ext z
    simp [LinearMap.smulRight_apply, add_smul]
  have hz : φ.smulRight u * φ.smulRight w = 0 := by
    rw [smulRight_mul_smulRight_same, hw.1, zero_smul]
  rw [Units.val_mul, hgu, hhw, hsum, smul_add]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hz, smul_zero,
    add_zero]
  abel

private theorem isRootElt_vec_smul {X : Subgroup (LinearMap.GeneralLinearGroup K V)} {u : V}
    {φ : Dual K V} (a : K) (hu : IsRootElt X u φ) : IsRootElt X (a • u) φ := by
  refine ⟨by simp [hu.1], fun c => ?_⟩
  obtain ⟨g, hg, hgu⟩ := hu.2 (c * a)
  refine ⟨g, hg, ?_⟩
  rw [hgu]
  congr 1
  ext z
  simp [LinearMap.smulRight_apply, smul_smul]
  congr 1
  ring

section CaseB

variable [FiniteDimensional K V]

private theorem caseB_comm {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hirr : Irred X)
    (hcentre : ∀ w : V, w ≠ 0 → IsCentre X w) {v w : V} {φ : Dual K V} (hv : v ≠ 0)
    (hφ : IsRootElt X v φ) (hw : φ w = 0) (hwa : w ∉ axisSpace X v) :
    IsRootElt X w φ := by
  have hw0 : w ≠ 0 := fun h => hwa (by rw [h]; exact Submodule.zero_mem _)
  have hvw : v ∉ axisSpace X w := fun h =>
    hwa ((mem_axisSpace_comm hirr (hcentre v hv) (hcentre w hw0)).mpr h)
  obtain ⟨μ, hμ, hμv⟩ : ∃ μ : Dual K V, IsRootElt X w μ ∧ μ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hvw (mem_axisSpace_iff.mpr h)
  exact isRootElt_comm hμ hφ hw hμv

private theorem caseB_ker {X : Subgroup (LinearMap.GeneralLinearGroup K V)} (hirr : Irred X)
    (hcentre : ∀ w : V, w ≠ 0 → IsCentre X w)
    (hcodim : ∀ w : V, w ≠ 0 → finrank K (axisSpace X w) + 2 ≤ finrank K V)
    {v x : V} {φ : Dual K V} (hv : v ≠ 0) (hφ : IsRootElt X v φ) (hx : φ x = 0) :
    IsRootElt X x φ := by
  by_cases hxa : x ∈ axisSpace X v
  · obtain ⟨y, hy, hya⟩ : ∃ y : V, φ y = 0 ∧ y ∉ axisSpace X v := by
      by_contra h
      push Not at h
      have heq : LinearMap.ker φ ≤ axisSpace X v := fun y hy =>
        h y (LinearMap.mem_ker.mp hy)
      have h1 : finrank K (LinearMap.ker φ) ≤ finrank K (axisSpace X v) :=
        Submodule.finrank_mono heq
      have h2 := LinearMap.finrank_range_add_finrank_ker φ
      have h3 : finrank K (LinearMap.range φ) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range φ)
      have h4 := hcodim v hv
      omega
    have hyr : IsRootElt X y φ := caseB_comm hirr hcentre hv hφ hy hya
    have hxy : IsRootElt X (x + y) φ := by
      refine caseB_comm hirr hcentre hv hφ (by simp [hx, hy]) ?_
      intro h
      apply hya
      have := Submodule.sub_mem _ h hxa
      rwa [add_sub_cancel_left] at this
    have hneg : IsRootElt X (-y) φ := by
      have := isRootElt_vec_smul (-1 : K) hyr
      rwa [neg_one_smul] at this
    have := isRootElt_add_vec hxy hneg
    rwa [show x + y + -y = x by abel] at this
  · exact caseB_comm hirr hcentre hv hφ hx hxa

private theorem exists_ne_zero_of_ker_pair (ψ₁ ψ₂ : Dual K V) (h3 : 3 ≤ finrank K V) :
    ∃ x : V, x ≠ 0 ∧ ψ₁ x = 0 ∧ ψ₂ x = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (ψ₁.prod ψ₂)
  have h2 : finrank K (LinearMap.range (ψ₁.prod ψ₂)) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (ψ₁.prod ψ₂))
    rw [Module.finrank_prod, Module.finrank_self] at this
    omega
  have h4 : 0 < finrank K (LinearMap.ker (ψ₁.prod ψ₂)) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h4
  have hx' : (ψ₁.prod ψ₂) x = 0 := LinearMap.mem_ker.mp hx
  refine ⟨x, fun h => hx0 (Subtype.ext h), congrArg Prod.fst hx', congrArg Prod.snd hx'⟩

private theorem caseB_all_forms {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hirr : Irred X) (hcentre : ∀ w : V, w ≠ 0 → IsCentre X w)
    (hcodim : ∀ w : V, w ≠ 0 → finrank K (axisSpace X w) + 2 ≤ finrank K V)
    {v : V} (hv : v ≠ 0) : ∀ ψ : Dual K V, ∃ w : V, w ≠ 0 ∧ IsRootElt X w ψ := by
  have hmem : v ∈ axisSpace X v := mem_axisSpace_iff.mpr fun φ hφ => hφ.1
  have hpos : 0 < finrank K (axisSpace X v) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hmem⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hn3 : 3 ≤ finrank K V := by
    have := hcodim v hv
    omega
  obtain ⟨W, hW⟩ : ∃ W : Submodule K (Dual K V),
      ∀ ψ : Dual K V, ψ ∈ W ↔ ∃ w : V, w ≠ 0 ∧ IsRootElt X w ψ := by
    refine ⟨{ carrier := {ψ | ∃ w : V, w ≠ 0 ∧ IsRootElt X w ψ}
              add_mem' := ?_
              zero_mem' := ⟨v, hv, isRootElt_zero X v⟩
              smul_mem' := ?_ }, fun ψ => Iff.rfl⟩
    · rintro ψ₁ ψ₂ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      obtain ⟨x, hx0, hx1, hx2⟩ := exists_ne_zero_of_ker_pair ψ₁ ψ₂ hn3
      exact ⟨x, hx0, isRootElt_add (caseB_ker hirr hcentre hcodim hw₁ h₁ hx1)
        (caseB_ker hirr hcentre hcodim hw₂ h₂ hx2)⟩
    · rintro a ψ ⟨w, hw, h⟩
      exact ⟨w, hw, isRootElt_smul a h⟩
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (⨅ u ∈ {u : V | IsCentre X u}, axisSpace X u) := by
      simp only [Submodule.mem_iInf, Set.mem_setOf_eq]
      intro u hu
      rw [mem_axisSpace_iff]
      intro φ hφ
      rw [Submodule.mem_dualCoannihilator] at hx
      exact hx φ ((hW φ).mpr ⟨u, hu.1, hφ⟩)
    rw [iInf_axisSpace_eq_bot hirr ⟨v, hcentre v hv⟩] at hx'
    exact hx'
  have hWtop : W = ⊤ := by
    calc W = W.dualCoannihilator.dualAnnihilator :=
          Subspace.dualCoannihilator_dualAnnihilator_eq.symm
      _ = ⊤ := by rw [hbot, Submodule.dualAnnihilator_bot]
  intro ψ
  exact (hW ψ).mp (by rw [hWtop]; exact Submodule.mem_top)

private theorem det_one_add_smulRight_of_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (φ : Dual K V) (u : V) (hφu : φ u = 0) :
    LinearMap.det (1 + φ.smulRight u : V →ₗ[K] V) = 1 := by
  have h : Matrix.vecMulVec (b.repr u) (⇑φ ∘ ⇑b) =
      Matrix.replicateCol Unit (b.repr u) * Matrix.replicateRow Unit (⇑φ ∘ ⇑b) := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
  have hdot : (⇑φ ∘ ⇑b) ⬝ᵥ (b.repr u) = φ u := by
    conv_rhs => rw [← b.sum_repr u]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one, LinearMap.toMatrix_smulRight,
    h, Matrix.det_one_add_replicateCol_mul_replicateRow, hdot, hφu, add_zero]

private theorem toLinAlgEquiv_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) {i j : ι} (hij : i ≠ j) (c : K) :
    Matrix.toLinAlgEquiv b (Matrix.transvection i j c) =
      1 + c • (b.coord j).smulRight (b i) := by
  apply b.ext
  intro k
  rw [Matrix.toLinAlgEquiv_self]
  simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    add_smul, Finset.sum_add_distrib, ite_smul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp_all [eq_comm]

private theorem sl_le_of_full_transvections {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hall : ∀ (u : V) (φ : Dual K V), φ u = 0 → IsRootElt X u φ) (hn : 2 ≤ finrank K V)
    (g : LinearMap.GeneralLinearGroup K V) (hg : LinearMap.det (g : V →ₗ[K] V) = 1) : g ∈ X := by
  let b : Module.Basis (Fin (finrank K V)) K V := Module.finBasis K V
  haveI : Nontrivial (Fin (finrank K V)) := Fin.nontrivial_iff_two_le.mpr hn
  let S : Matrix.GeneralLinearGroup (Fin (finrank K V)) K →* LinearMap.GeneralLinearGroup K V :=
    Units.map (Matrix.toLinAlgEquiv b).toMonoidHom
  let ψ : Matrix.SpecialLinearGroup (Fin (finrank K V)) K →* LinearMap.GeneralLinearGroup K V :=
    S.comp Matrix.SpecialLinearGroup.toGL
  have hψ : ∀ A : Matrix.SpecialLinearGroup (Fin (finrank K V)) K,
      ((ψ A : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
        Matrix.toLinAlgEquiv b (A : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K) :=
    fun A => rfl
  have hH : X.comap ψ = ⊤ := by
    apply CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    intro i j hij c
    rw [Subgroup.mem_comap]
    have h0 : (b.coord j) (b i) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg hij]
    obtain ⟨h, hh, hh'⟩ := (hall (b i) (b.coord j) h0).2 c
    convert hh using 1
    apply Units.ext
    rw [hψ]
    show Matrix.toLinAlgEquiv b (Matrix.transvection i j c) = _
    rw [toLinAlgEquiv_transvection b hij c, hh']
  let M : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    ((Matrix.toLinAlgEquiv b).symm g : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K)
  have h1 : Matrix.toLinAlgEquiv b M = (g : V →ₗ[K] V) := by
    rw [AlgEquiv.apply_symm_apply]
  have hMdet : M.det = 1 := by
    have h2 : LinearMap.det (Matrix.toLin b b M) = M.det := LinearMap.det_toLin b M
    have h3 : Matrix.toLin b b M = (g : V →ₗ[K] V) := h1
    rw [← h2, h3, hg]
  let s : Matrix.SpecialLinearGroup (Fin (finrank K V)) K := ⟨M, hMdet⟩
  have hs : s ∈ X.comap ψ := by
    rw [hH]
    exact Subgroup.mem_top _
  have hψs : ψ s = g := by
    apply Units.ext
    rw [hψ]
    exact h1
  rw [← hψs]
  exact Subgroup.mem_comap.mp hs

theorem eq_sl_of_axisSpace {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hK : 3 ≤ Nat.card K) (hgen : GenByRoots X) (hirr : Irred X) {v : V} (hv : v ≠ 0)
    (hB : finrank K (axisSpace X v) + 1 < finrank K V) :
    ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ X ↔ LinearMap.det (g : V →ₗ[K] V) = 1 := by
  have hmem : v ∈ axisSpace X v := mem_axisSpace_iff.mpr fun φ hφ => hφ.1
  have hpos : 0 < finrank K (axisSpace X v) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hmem⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hn : 2 ≤ finrank K V := by omega
  have hcentre : ∀ w : V, w ≠ 0 → IsCentre X w := fun w hw =>
    isCentre_of_ne_zero hK hn hgen hirr hw
  have hcodim : ∀ w : V, w ≠ 0 → finrank K (axisSpace X w) + 2 ≤ finrank K V := by
    intro w hw
    have := finrank_axisSpace_eq hirr (hcentre w hw) (hcentre v hv)
    omega
  have hroot : ∀ (u : V) (φ : Dual K V), φ u = 0 → IsRootElt X u φ := by
    intro u φ hφu
    obtain ⟨w, hw, hwφ⟩ := caseB_all_forms hirr hcentre hcodim hv φ
    exact caseB_ker hirr hcentre hcodim hw hwφ hφu
  have hX : X ≤ ((LinearMap.det : (V →ₗ[K] V) →* K).comp (Units.coeHom _)).ker := by
    rw [hgen, Subgroup.closure_le]
    rintro t ⟨u, φ, _, _, hφ, ht⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.coeHom_apply, ht]
    exact det_one_add_smulRight_of_eq_zero (Module.finBasis K V) φ u hφ.1
  intro g
  exact ⟨fun hg => (MonoidHom.mem_ker.mp (hX hg)), fun hdet =>
    sl_le_of_full_transvections hroot hn g hdet⟩

private theorem gl_inv_val_apply (y : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((y⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((y : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

private theorem gl_val_inv_apply (y : LinearMap.GeneralLinearGroup K V) (x : V) :
    (y : V →ₗ[K] V) (((y⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem exists_alt_isometry_of_axisSpace_hyperplane
    {X : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hK : 3 ≤ Nat.card K) (hn : 2 ≤ finrank K V) (hgen : GenByRoots X) (hirr : Irred X)
    (hA : ∀ v : V, v ≠ 0 → finrank K (axisSpace X v) + 1 = finrank K V) :
    ∃ β : LinearMap.BilinForm K V, β.Nondegenerate ∧ (∀ x, β x x = 0) ∧
      ∀ g : LinearMap.GeneralLinearGroup K V,
        g ∈ X ↔ ∀ x y, β ((g : V →ₗ[K] V) x) ((g : V →ₗ[K] V) y) = β x y := by
  have hcentre : ∀ w : V, w ≠ 0 → IsCentre X w := fun w hw =>
    isCentre_of_ne_zero hK hn hgen hirr hw
  have hW : ∀ v : V, v ≠ 0 → finrank K (centreForms X v) = 1 := by
    intro v hv
    have h1 : finrank K (centreForms X v) +
        finrank K (centreForms X v).dualCoannihilator = finrank K V :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq (centreForms X v)
    have h2 : (centreForms X v).dualCoannihilator = axisSpace X v := rfl
    rw [h2] at h1
    have h3 := hA v hv
    omega
  have hex : ∀ v : V, ∃ φ : Dual K V, (v = 0 → φ = 0) ∧
      (v ≠ 0 → IsRootElt X v φ ∧ φ ≠ 0 ∧
        ∀ ψ : Dual K V, IsRootElt X v ψ → ∃ c : K, ψ = c • φ) := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, fun _ => rfl, fun h => absurd hv h⟩
    · obtain ⟨φ, hφ0, hφ⟩ := (hcentre v hv).2
      refine ⟨φ, fun h => absurd h hv, fun _ => ⟨hφ, hφ0, fun ψ hψ => ?_⟩⟩
      have hnz : (⟨φ, hφ⟩ : ↥(centreForms X v)) ≠ 0 := fun h => hφ0 (congrArg Subtype.val h)
      have hfin : finrank K ↥(centreForms X v) = 1 := hW v hv
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨φ, hφ⟩ : ↥(centreForms X v)) hnz).mp
        hfin (⟨ψ, hψ⟩ : ↥(centreForms X v))
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
  choose δ hδ0 hδ using hex
  have hker : ∀ v : V, v ≠ 0 → ∀ w : V, w ∈ axisSpace X v ↔ δ v w = 0 := by
    intro v hv w
    constructor
    · intro hw
      exact mem_axisSpace_iff.mp hw (δ v) (hδ v hv).1
    · intro hw
      rw [mem_axisSpace_iff]
      intro ψ hψ
      obtain ⟨c, rfl⟩ := (hδ v hv).2.2 ψ hψ
      simp [hw]
  have hδv : ∀ v : V, δ v v = 0 := by
    intro v
    by_cases hv : v = 0
    · rw [hv, hδ0 0 rfl]
      rfl
    · exact (hδ v hv).1.1
  have hsymm : ∀ v w : V, δ v w = 0 ↔ δ w v = 0 := by
    intro v w
    by_cases hv : v = 0
    · subst hv
      rw [hδ0 0 rfl]
      simp
    by_cases hw : w = 0
    · subst hw
      rw [hδ0 0 rfl]
      simp
    rw [← hker v hv w, ← hker w hw v]
    exact mem_axisSpace_comm hirr (hcentre v hv) (hcentre w hw)
  have hY : X = Subgroup.closure {g : LinearMap.GeneralLinearGroup K V | ∃ (v : V) (c : K),
      (g : V →ₗ[K] V) = 1 + c • (δ v).smulRight v} := by
    apply le_antisymm
    · rw [hgen, Subgroup.closure_le]
      rintro t ⟨u, φ, hu, -, hroot, ht⟩
      obtain ⟨c, rfl⟩ := (hδ u hu).2.2 φ hroot
      apply Subgroup.subset_closure
      refine ⟨u, c, ?_⟩
      rw [ht]
      ext z
      simp [LinearMap.smulRight_apply, smul_smul]
    · rw [Subgroup.closure_le]
      rintro t ⟨v, c, ht⟩
      by_cases hv : v = 0
      · rw [hv, hδ0 0 rfl] at ht
        have h1 : t = 1 := Units.ext (by rw [ht]; simp)
        rw [h1]
        exact X.one_mem
      · obtain ⟨g, hg, hgeq⟩ := (hδ v hv).1.2 c
        have h1 : t = g := Units.ext (by rw [ht, hgeq])
        rw [h1]
        exact hg
  have hinv : ∀ y ∈ X, ∀ v : V, LinearMap.ker (δ ((y : V →ₗ[K] V) v)) =
      (LinearMap.ker (δ v)).map (y : V →ₗ[K] V) := by
    intro y hy v
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_map]
    by_cases hv : v = 0
    · subst hv
      rw [map_zero, hδ0 0 rfl]
      constructor
      · intro _
        exact ⟨((y⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x, by simp,
          gl_val_inv_apply y x⟩
      · intro _
        simp
    · have hyv : (y : V →ₗ[K] V) v ≠ 0 := by
        intro h
        apply hv
        have h' := gl_inv_val_apply y v
        rw [h, map_zero] at h'
        exact h'.symm
      constructor
      · intro h
        refine ⟨((y⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x, ?_,
          gl_val_inv_apply y x⟩
        exact (hker v hv _).mp ((mem_axisSpace_smul_iff hy v x).mp ((hker _ hyv x).mpr h))
      · rintro ⟨z, hz, rfl⟩
        refine (hker _ hyv _).mp ((mem_axisSpace_smul_iff hy v _).mpr ?_)
        rw [gl_inv_val_apply y z]
        exact (hker v hv z).mpr hz
  obtain ⟨β, hβnd, hβalt, hβ⟩ := exists_alt_form_of_sympData δ
    (fun v hv => (hδ v hv).2.1) hδv hsymm X hY hinv
  have hβA : β.IsAlt := fun x => hβalt x
  have anti : ∀ x y : V, β x y = -β y x := by
    intro x y
    have h := hβalt (x + y)
    simp only [map_add, LinearMap.add_apply, hβalt x, hβalt y, zero_add, add_zero] at h
    linear_combination h
  have hprop : ∀ v : V, v ≠ 0 → ∃ μ : K, ∀ z : V, β v z = μ * δ v z := by
    intro v hv
    obtain ⟨z0, hz0⟩ : ∃ z0 : V, δ v z0 ≠ 0 := by
      by_contra h
      push Not at h
      exact (hδ v hv).2.1 (LinearMap.ext fun z => h z)
    refine ⟨β v z0 / δ v z0, fun z => ?_⟩
    set t := δ v z / δ v z0 with ht
    have hw : δ v (z - t • z0) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hz0, sub_self]
    have hβw : β v (z - t • z0) = 0 := (hβ v (z - t • z0) hv).mpr hw
    have hsplit : β v z = t * β v z0 := by
      have h1 : β v ((z - t • z0) + t • z0) = β v (z - t • z0) + β v (t • z0) := map_add _ _ _
      rw [sub_add_cancel] at h1
      rw [h1, hβw, zero_add, map_smul, smul_eq_mul]
    rw [hsplit, ht]
    ring
  have hsub : X ≤ CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup β := by
    rw [hY, Subgroup.closure_le]
    rintro t ⟨v, c, ht⟩
    rw [SetLike.mem_coe, CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
    by_cases hv : v = 0
    · rw [hv, hδ0 0 rfl] at ht
      have h1 : (t : V →ₗ[K] V) = 1 := by
        rw [ht]
        ext z
        simp
      intro x y
      rw [h1]
      simp
    · obtain ⟨μ, hμ⟩ := hprop v hv
      intro x y
      rw [ht]
      have hvv : β v v = 0 := hβalt v
      have hxv : β x v = -(μ * δ v x) := by rw [anti x v, hμ x]
      have hvy : β v y = μ * δ v y := hμ y
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        Module.End.one_apply, LinearMap.smulRight_apply]
      rw [hxv, hvy, hvv]
      ring
  have hgen2 : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup β ≤ X := by
    rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hβA hβnd,
      Subgroup.closure_le]
    rintro T ⟨a, c, rfl⟩
    by_cases ha : a = 0
    · subst ha
      have h1 : CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβA 0 c = 1 :=
        Units.ext (LinearMap.ext fun x => by
          simp [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply])
      rw [h1]
      exact X.one_mem
    · obtain ⟨μ, hμ⟩ := hprop a ha
      obtain ⟨g, hg, hgeq⟩ := (hδ a ha).1.2 (-(c * μ))
      have h1 : CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβA a c = g := by
        apply Units.ext
        apply LinearMap.ext
        intro x
        rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, hgeq]
        have hxa : β x a = -(μ * δ a x) := by rw [anti x a, hμ x]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
          LinearMap.smulRight_apply, smul_eq_mul, hxa]
        module
      rw [h1]
      exact hg
  refine ⟨β, hβnd, hβalt, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact hsub hg
  · exact hgen2 (CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr hg)

end CaseB

end CFSG.ClassicalGroups.McLaughlin

end
