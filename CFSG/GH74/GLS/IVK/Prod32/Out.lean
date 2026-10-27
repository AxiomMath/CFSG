module

public import CFSG.GH74.GLS.IVK.Prod32.Basic
public import CFSG.GH74.GLS.IVK.Lifted.CentSylow

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.GH74.GLS.IVK.Lifted (slFieldAut)

section Unique

variable {F : Type} [Field F]

@[expose] def uSL (t : F) : SpecialLinearGroup (Fin 2) F := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
@[expose] def vSL (t : F) : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem scalar_of_commute_two (M : Matrix (Fin 2) (Fin 2) F)
    (h1 : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M) (h2 : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M) :
    ∃ μ : F, M = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.eta_fin_two M] at h1 h2
  simp only [Matrix.mul_fin_two] at h1 h2
  have a1 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h1
  have a2 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 1) h1
  have a3 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h2
  simp at a1 a2 a3
  have c11 : M 1 1 = M 0 0 := by linear_combination -a2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a1, a3, c11]


theorem map_toGL_uSL (σ : F ≃+* F) (t : F) :
    ((GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL (uSL t)) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, σ t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, GeneralLinearGroup.map_apply] <;> rfl

theorem map_toGL_vSL (σ : F ≃+* F) (t : F) :
    ((GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL (vSL t)) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 0; σ t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL, GeneralLinearGroup.map_apply] <;> rfl

theorem semilinear_unique {G G' : GL (Fin 2) F} {σ σ' : F ≃+* F}
    (h : ∀ b : SpecialLinearGroup (Fin 2) F,
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹ =
        G' * GeneralLinearGroup.map (σ' : F →+* F) (SpecialLinearGroup.toGL b) * G'⁻¹) :
    σ = σ' ∧ ∃ c : F, c ≠ 0 ∧ (G' : Matrix (Fin 2) (Fin 2) F) = c • (G : Matrix (Fin 2) (Fin 2) F) := by
  set M : GL (Fin 2) F := G'⁻¹ * G with hMdef
  have hM : ∀ b : SpecialLinearGroup (Fin 2) F,
      M * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * M⁻¹ =
        GeneralLinearGroup.map (σ' : F →+* F) (SpecialLinearGroup.toGL b) := by
    intro b
    have := h b
    calc M * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * M⁻¹
        = G'⁻¹ * (G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹) * G' := by
          rw [hMdef]; group
      _ = G'⁻¹ * (G' * GeneralLinearGroup.map (σ' : F →+* F) (SpecialLinearGroup.toGL b) * G'⁻¹) * G' := by
          rw [this]
      _ = _ := by group
  have hMmat : ∀ b : SpecialLinearGroup (Fin 2) F,
      (M : Matrix (Fin 2) (Fin 2) F) *
          ((GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) =
        ((GeneralLinearGroup.map (σ' : F →+* F) (SpecialLinearGroup.toGL b) : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) := by
    intro b
    have h1 := hM b
    have h2 : M * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) =
        GeneralLinearGroup.map (σ' : F →+* F) (SpecialLinearGroup.toGL b) * M := by
      rw [← h1]; group
    exact congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) h2
  have hu1 := hMmat (uSL 1)
  have hv1 := hMmat (vSL 1)
  rw [map_toGL_uSL, map_toGL_uSL, map_one, map_one] at hu1
  rw [map_toGL_vSL, map_toGL_vSL, map_one, map_one] at hv1
  obtain ⟨μ, hμ⟩ := scalar_of_commute_two (M : Matrix (Fin 2) (Fin 2) F) hu1 hv1
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hdet : IsUnit (M : Matrix (Fin 2) (Fin 2) F) := Units.isUnit M
    rw [hμ, h0, zero_smul, Matrix.isUnit_iff_isUnit_det] at hdet
    simp at hdet
  have hσ : σ = σ' := by
    ext t
    have h1 := hMmat (uSL t)
    rw [map_toGL_uSL, map_toGL_uSL, hμ] at h1
    have h2 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 1) h1
    simp at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact (hμ0 h2).elim
  refine ⟨hσ, μ⁻¹, inv_ne_zero hμ0, ?_⟩
  have hGM : (G : Matrix (Fin 2) (Fin 2) F) = (G' : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) := by
    have : G = G' * M := by rw [hMdef]; group
    exact congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) this
  rw [hGM, hμ, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

end Unique

section OutSL

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)
open CFSG.GH74.GLS.IVK.Lifted (gammaOf slFieldAut)
open CFSG.ABGDGroups (pGammaL2DetClass)

variable {F : Type} [Field F] [Finite F]

structure GoodF (F : Type) [Field F] [Finite F] : Prop where
  odd : Odd (Nat.card F)
  gt3 : 3 < Nat.card F

@[expose] noncomputable def outHom (hF : GoodF F) :
    MulAut (SpecialLinearGroup (Fin 2) F) →* SquareClass F × (F ≃+* F) :=
  ((pGammaL2DetClass F (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.odd)).comp
      (gammaOf hF.odd hF.gt3)).prod
    ((SemidirectProduct.rightHom).comp (gammaOf hF.odd hF.gt3))

theorem outHom_fst (hF : GoodF F) (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    (outHom hF α).1 =
      pGammaL2DetClass F (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.odd)
        (gammaOf hF.odd hF.gt3 α) := rfl

theorem outHom_snd (hF : GoodF F) (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    (outHom hF α).2 = (gammaOf hF.odd hF.gt3 α).right := rfl

theorem outHom_eq_one_iff (hF : GoodF F) (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    outHom hF α = 1 ↔ α ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut _).range := by
  rw [CFSG.GH74.GLS.IVK.Lifted.mem_inn_iff hF.odd hF.gt3,
    CFSG.ABGDGroups.left_mem_range_toPGL_iff (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.odd),
    Prod.ext_iff]
  rw [outHom_fst, outHom_snd]
  simp only [Prod.fst_one, Prod.snd_one]
  tauto

theorem outHom_of_rep (hF : GoodF F) {α : MulAut (SpecialLinearGroup (Fin 2) F)}
    {G : GL (Fin 2) F} {σ : F ≃+* F}
    (h : ∀ b : SpecialLinearGroup (Fin 2) F, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹) :
    outHom hF α = (squareClassMap F (Matrix.GeneralLinearGroup.det G), σ) := by
  obtain ⟨G₀, hG₀⟩ := Matrix.ProjGenLinGroup.mk_surjective (gammaOf hF.odd hF.gt3 α).left
  have hrep₀ := CFSG.GH74.GLS.IVK.semilinear_of_pGammaL2 hF.odd hF.gt3 α (gammaOf hF.odd hF.gt3 α)
    (CFSG.GH74.GLS.IVK.Lifted.thetaEquiv_gammaOf hF.odd hF.gt3 α) G₀ hG₀
  obtain ⟨hσ, c, hc, hGc⟩ := semilinear_unique (G := G) (G' := G₀) (σ := σ)
    (σ' := (gammaOf hF.odd hF.gt3 α).right) (fun b => by rw [← h b, ← hrep₀ b])
  refine Prod.ext ?_ ?_
  · show (outHom hF α).1 = squareClassMap F (Matrix.GeneralLinearGroup.det G)
    rw [outHom_fst, CFSG.ABGDGroups.pGammaL2DetClass_apply, ← hG₀,
      CFSG.Semidihedral.SemilinearOuterQuotient.pglDet_mk]
    have hdet : Matrix.GeneralLinearGroup.det G₀ =
        (Units.mk0 c hc) ^ 2 * Matrix.GeneralLinearGroup.det G := by
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hGc,
        Matrix.det_smul, Fintype.card_fin]
    rw [hdet, map_mul, (CFSG.Semidihedral.SemilinearOuterQuotient.squareClassMap_eq_one F _).mpr
      ⟨Units.mk0 c hc, sq _⟩, one_mul]
  · rw [outHom_snd]; exact hσ.symm

theorem exists_rep' (hF : GoodF F) (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    ∃ G : GL (Fin 2) F, (∀ b : SpecialLinearGroup (Fin 2) F, SpecialLinearGroup.toGL (α b) =
      G * GeneralLinearGroup.map ((outHom hF α).2 : F →+* F) (SpecialLinearGroup.toGL b) * G⁻¹) ∧
      (outHom hF α).1 = squareClassMap F (Matrix.GeneralLinearGroup.det G) := by
  obtain ⟨G, hG⟩ := CFSG.GH74.GLS.IVK.Lifted.exists_rep hF.odd hF.gt3 α
  exact ⟨G, hG, by rw [outHom_of_rep hF hG]⟩

omit [Finite F] in
theorem squareClassMap_eq_one_iff (u : Fˣ) : squareClassMap F u = 1 ↔ IsSquare (u : F) :=
  (CFSG.Semidihedral.SemilinearOuterQuotient.squareClassMap_eq_one F u).trans
    (CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff u)

theorem outHom_slFieldAut (hF : GoodF F) (σ : F ≃+* F) :
    outHom hF (slFieldAut σ) = (1, σ) := by
  have h : ∀ b : SpecialLinearGroup (Fin 2) F, SpecialLinearGroup.toGL (slFieldAut σ b) =
      (1 : GL (Fin 2) F) * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL b) *
        (1 : GL (Fin 2) F)⁻¹ := by
    intro b
    rw [CFSG.GH74.GLS.IVK.Lifted.slFieldAut_apply]
    simp only [inv_one, one_mul, mul_one]
    exact CFSG.Semidihedral.MatrixCoverData.toGL_field_map F σ b
  rw [outHom_of_rep hF h, map_one]
  rfl

end OutSL

section Coord

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F]

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)

@[expose] noncomputable def coordHom (K : Subgroup H) (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F) :
    ↥(normalizer (K : Set H)) →* SquareClass F × (F ≃+* F) :=
  (outHom hF).comp ((MulAut.congr ê).toMonoidHom.comp K.normalizerMonoidHom)

theorem congr_apply_eq {G L : Type*} [Group G] [Group L] (e : G ≃* L) (φ : MulAut G) (b : L) :
    MulAut.congr e φ b = e (φ (e.symm b)) := rfl

theorem coordHom_eq_one_iff (K : Subgroup H) (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hF : GoodF F)
    (x : ↥(normalizer (K : Set H))) :
    coordHom K ê hF x = 1 ↔ ∃ k ∈ K, ∀ y ∈ K, (x : H) * y * (x : H)⁻¹ = k * y * k⁻¹ := by
  rw [coordHom, MonoidHom.comp_apply, outHom_eq_one_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(ê.symm s : K), (ê.symm s).2, fun y hy => ?_⟩
    have h1 := congrArg (fun f : MulAut (SpecialLinearGroup (Fin 2) F) => f (ê ⟨y, hy⟩)) hs
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    rw [congr_apply_eq, MulEquiv.symm_apply_apply] at h1
    have h2 : K.normalizerMonoidHom x ⟨y, hy⟩ = ê.symm s * ⟨y, hy⟩ * (ê.symm s)⁻¹ := by
      apply ê.injective
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 := congrArg (fun w : K => (w : H)) h2
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h3
  · rintro ⟨k, hk, hkx⟩
    refine ⟨ê ⟨k, hk⟩, ?_⟩
    apply MulEquiv.ext
    intro b
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [congr_apply_eq]
    have h2 : K.normalizerMonoidHom x (ê.symm b) = ⟨k, hk⟩ * ê.symm b * ⟨k, hk⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
        InvMemClass.coe_inv]
      exact hkx _ (ê.symm b).2
    rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end Coord

section SLAct

variable {H : Type} [Group H]

theorem sl2_card_inj {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) :
    a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : a ^ 2 - 1 < b ^ 2 - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) (Nat.pow_lt_pow_left hlt (two_ne_zero))
    exact absurd h (ne_of_lt (Nat.mul_lt_mul'' hlt h1))
  · have h1 : b ^ 2 - 1 < a ^ 2 - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) (Nat.pow_lt_pow_left hgt (two_ne_zero))
    exact absurd h (ne_of_gt (Nat.mul_lt_mul'' hgt h1))

omit [Group H] in
theorem card_eq_of_sl2_equiv {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F']
    (e : SL2 F ≃* SL2 F') : Nat.card F = Nat.card F' := by
  have h1 : Nat.card (SL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h2 : Nat.card (SL2 F') = Nat.card F' * (Nat.card F' ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F').toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  rw [Nat.card_congr e.toEquiv] at h1
  exact sl2_card_inj Finite.one_lt_card Finite.one_lt_card (h1.symm.trans h2)

structure SLAct (K : Subgroup H) (a : H) {F : Type} [Field F] [Finite F]
    (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (σ : F ≃+* F) : Prop where
  norm : ∀ x ∈ K, a * x * a⁻¹ ∈ K
  act : ∀ (x : ↥K) (hx : a * (x : H) * a⁻¹ ∈ K), ê ⟨a * x * a⁻¹, hx⟩ = slFieldAut σ (ê x)

theorem stableAut_eq_slFieldAut {F : Type} [Field F] [Finite F] (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 2) F) :
    stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (specialLinearGroupEquivStatedSL 2 F g) =
      specialLinearGroupEquivStatedSL 2 F (slFieldAut σ g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem IndFAut.exists_slAct {K : Subgroup H} {a : H} (h : IndFAut K a)
    (htype : HasSL2Model ↥K (fun q => Odd q ∧ 5 ≤ q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) (σ : F ≃+* F),
      GoodF F ∧ SLAct K a ê σ := by
  obtain ⟨hnorm, ⟨F, _, _, e, σ, hact⟩ | ⟨h7, _⟩⟩ := h
  · obtain ⟨F', _, _, ⟨hodd', h5'⟩, ⟨e'⟩⟩ := htype
    have hcard : Nat.card F = Nat.card F' := card_eq_of_sl2_equiv (e.symm.trans e')
    refine ⟨F, inferInstance, inferInstance, e.trans (specialLinearGroupEquivStatedSL 2 F).symm, σ,
      ⟨?_, by omega⟩, ⟨hnorm, fun x hx => ?_⟩⟩
    · rw [hcard]; exact hodd'
    · have h0 := hact x hx
      apply (specialLinearGroupEquivStatedSL 2 F).injective
      have h1 : (specialLinearGroupEquivStatedSL 2 F)
          ((e.trans (specialLinearGroupEquivStatedSL 2 F).symm) ⟨a * x * a⁻¹, hx⟩) =
            e ⟨a * x * a⁻¹, hx⟩ := by simp
      have h2 : (specialLinearGroupEquivStatedSL 2 F)
          (slFieldAut σ ((e.trans (specialLinearGroupEquivStatedSL 2 F).symm) x)) =
            stableAut (StatedSL 2 F) (fieldStable_statedSL 2) σ (e x) := by
        rw [← stableAut_eq_slFieldAut]; simp
      rw [h1, h2, h0]
  · obtain ⟨F', _, _, _, ⟨e'⟩⟩ := htype
    exact (CFSG.GH74.GLS.IVK.Lifted.not_sl2_of_double_cover_alt7 h7 e').elim

omit [Group H] in
theorem mem_normalizer_of_conj_le {H : Type} [Group H] [Finite H] {K : Subgroup H} {a : H}
    (h : ∀ x ∈ K, a * x * a⁻¹ ∈ K) : a ∈ normalizer (K : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h z, fun hz => ?_⟩
  let f : K → K := fun x => ⟨a * x * a⁻¹, h x x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [f] at this
    apply Subtype.ext
    simpa using this
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj ⟨a * z * a⁻¹, hz⟩
  have := congrArg Subtype.val hx
  simp only [f] at this
  have hxz : (x : H) = z := by simpa using this
  rw [← hxz]; exact x.2

theorem coordHom_slAct {K : Subgroup H} {a : H} {F : Type} [Field F] [Finite F]
    {ê : ↥K ≃* SpecialLinearGroup (Fin 2) F} {σ : F ≃+* F} (hF : GoodF F)
    (h : SLAct K a ê σ) (ha : a ∈ normalizer (K : Set H)) :
    coordHom K ê hF ⟨a, ha⟩ = (1, σ) := by
  have : (MulAut.congr ê).toMonoidHom (K.normalizerMonoidHom ⟨a, ha⟩) = slFieldAut σ := by
    apply MulEquiv.ext
    intro b
    show MulAut.congr ê (K.normalizerMonoidHom ⟨a, ha⟩) b = slFieldAut σ b
    rw [congr_apply_eq]
    have hx : a * ((ê.symm b : ↥K) : H) * a⁻¹ ∈ K := h.norm _ (ê.symm b).2
    have h1 := h.act (ê.symm b) hx
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    congr 1
  show outHom hF ((MulAut.congr ê).toMonoidHom (K.normalizerMonoidHom ⟨a, ha⟩)) = (1, σ)
  rw [this, outHom_slFieldAut]

end SLAct

section FInner

variable {H : Type} [Group H] [Finite H]

theorem IndFAut.inner_trivial {K : Subgroup H} {a : H} (h : IndFAut K a)
    (htype : HasSL2Model ↥K (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥K 7)
    (hin : ∃ k ∈ K, ∀ y ∈ K, a * y * a⁻¹ = k * y * k⁻¹) : ∀ y ∈ K, a * y * a⁻¹ = y := by
  by_cases h7 : IsDoubleCoverOfAlt ↥K 7
  · rcases h with ⟨_, ⟨F, _, _, e, σ, _⟩ | ⟨_, htr | hni⟩⟩
    · exact (CFSG.GH74.GLS.IVK.Lifted.not_sl2_of_double_cover_alt7 h7 e).elim
    · exact htr
    · exact (hni hin).elim
  · obtain ⟨F, _, _, ê, σ, hF, hact⟩ := h.exists_slAct (htype.resolve_right h7)
    have ha : a ∈ normalizer (K : Set H) := mem_normalizer_of_conj_le hact.norm
    have h1 := coordHom_slAct hF hact ha
    obtain ⟨k, hk, hkx⟩ := hin
    have h2 : coordHom K ê hF ⟨a, ha⟩ = 1 :=
      (coordHom_eq_one_iff K ê hF ⟨a, ha⟩).mpr ⟨k, hk, hkx⟩
    rw [h1] at h2
    have hσ : σ = 1 := (Prod.ext_iff.mp h2).2
    subst hσ
    intro y hy
    have h3 := hact.act ⟨y, hy⟩ (hact.norm y hy)
    have : slFieldAut (1 : F ≃+* F) (ê ⟨y, hy⟩) = ê ⟨y, hy⟩ := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rfl
    rw [this] at h3
    exact congrArg Subtype.val (ê.injective h3)

theorem Hyp.a_not_mem_K {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}
    (h : Hyp H K₁ K₂ z T a) : a ∉ K₁ ⊔ K₂ := by
  intro haK
  have hS := h.setting
  obtain ⟨k₁, hk₁, k₂, hk₂, hak⟩ := (mem_sup_of_comm hS.comm a).mp haK
  have h1 : ∀ y ∈ K₁, a * y * a⁻¹ = y := by
    refine h.f₁.inner_trivial hS.type₁ ⟨k₁, hk₁, fun y hy => ?_⟩
    have := hS.comm y hy k₂ hk₂
    rw [hak]
    calc k₁ * k₂ * y * (k₁ * k₂)⁻¹ = k₁ * (k₂ * y * k₂⁻¹) * k₁⁻¹ := by group
      _ = k₁ * y * k₁⁻¹ := by
        have h2 : k₂ * y * k₂⁻¹ = y := by rw [← this]; group
        rw [h2]
  have h2 : ∀ y ∈ K₂, a * y * a⁻¹ = y := by
    refine h.f₂.inner_trivial hS.type₂ ⟨k₂, hk₂, fun y hy => ?_⟩
    have := hS.comm k₁ hk₁ y hy
    rw [hak]
    calc k₁ * k₂ * y * (k₁ * k₂)⁻¹ = (k₁ * (k₂ * y * k₂⁻¹)) * k₁⁻¹ := by group
      _ = k₂ * y * k₂⁻¹ := by
        have h3 : k₁ * (k₂ * y * k₂⁻¹) * k₁⁻¹ = k₂ * y * k₂⁻¹ :=
          by rw [hS.comm k₁ hk₁ _ (by
            have := K₂.mul_mem (K₂.mul_mem hk₂ hy) (K₂.inv_mem hk₂); exact this)]; group
        exact h3
  have hcent : ∀ m ∈ K₁ ⊔ K₂, a * m = m * a := by
    intro m hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := (mem_sup_of_comm hS.comm m).mp hm
    have e1 := h1 m₁ hm₁
    have e2 := h2 m₂ hm₂
    have f1 : a * m₁ = m₁ * a := mul_inv_eq_iff_eq_mul.mp e1
    have f2 : a * m₂ = m₂ * a := mul_inv_eq_iff_eq_mul.mp e2
    calc a * (m₁ * m₂) = (a * m₁) * m₂ := by group
      _ = m₁ * (a * m₂) := by rw [f1]; group
      _ = m₁ * (m₂ * a) := by rw [f2]
      _ = m₁ * m₂ * a := by group
  have hmem : a ∈ (Subgroup.center ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype := by
    refine Subgroup.mem_map.2 ⟨⟨a, haK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g g.2).symm
  rw [hS.zK] at hmem
  rcases eq_one_or_eq_of_mem_zpowers hS.z_ord hmem with h3 | h3
  · have := h.a_ord
    rw [h3, orderOf_one] at this
    omega
  · exact h.a_ne_z h3

end FInner

section OutAb

theorem out_abelian_of_type (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) {Q : Type} [Group Q] [Finite Q]
    (htype : HasSL2Model Q (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt Q 7) (α β : MulAut Q) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Q →* MulAut Q).range := by
  rcases htype with ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩ | h7
  · set ê := e.trans (specialLinearGroupEquivStatedSL 2 F).symm with hê
    obtain ⟨s, hs⟩ := CFSG.GH74.GLS.IVK.Lifted.out_abelian_sl hodd (by omega)
      (MulAut.congr ê α) (MulAut.congr ê β)
    refine ⟨ê.symm s, ?_⟩
    apply (MulAut.congr ê).injective
    rw [CFSG.GH74.GLS.IVK.Lifted.congr_conj, MulEquiv.apply_symm_apply, hs]
    simp only [map_mul, map_inv]
  · have hidx := (h2A7 Q h7).2.2.2.1
    change α * β * α⁻¹ * β⁻¹ ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf Q
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto

end OutAb

end CFSG.GH74.GLS.IVK.Prod3
