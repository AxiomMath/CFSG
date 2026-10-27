module

public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Blueprint.ChevalleyInfinitesimals

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Entrywise

variable {τ : Tag} {K L M : Type} [Field K] [Field L] [Field M]

@[expose] noncomputable def entrywiseCongr (φ : K →+* L) (A : Module.End K (RootModule τ K)) :
    Module.End L (RootModule τ L) :=
  Finsupp.linearCombination L fun b => Finsupp.mapRange φ φ.map_zero (A (Finsupp.single b 1))

theorem entrywiseCongr_single (φ : K →+* L) (A : Module.End K (RootModule τ K)) (b : Label τ) :
    entrywiseCongr φ A (Finsupp.single b 1) =
      Finsupp.mapRange φ φ.map_zero (A (Finsupp.single b 1)) := by
  simp [entrywiseCongr]

theorem entrywiseCongr_apply_mapRange (φ : K →+* L) (A : Module.End K (RootModule τ K))
    (x : RootModule τ K) :
    entrywiseCongr φ A (Finsupp.mapRange φ φ.map_zero x) =
      Finsupp.mapRange φ φ.map_zero (A x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add φ), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add φ)]
  | single b r =>
    have h1 : Finsupp.mapRange φ φ.map_zero (Finsupp.single b r) =
        φ r • Finsupp.single b (1 : L) := by
      simp
    have h2 : Finsupp.single b r = r • Finsupp.single b (1 : K) := by simp
    rw [h1, map_smul, entrywiseCongr_single, h2, map_smul]
    ext l
    simp

theorem entrywiseCongr_one (φ : K →+* L) :
    entrywiseCongr φ (1 : Module.End K (RootModule τ K)) = 1 := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp [entrywiseCongr]

theorem entrywiseCongr_mul (φ : K →+* L) (A B : Module.End K (RootModule τ K)) :
    entrywiseCongr φ (A * B) = entrywiseCongr φ A * entrywiseCongr φ B := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [entrywiseCongr_single, entrywiseCongr_single, entrywiseCongr_apply_mapRange,
    Module.End.mul_apply]

theorem entrywiseCongr_comp (φ : K →+* L) (ψ : L →+* M) (A : Module.End K (RootModule τ K)) :
    entrywiseCongr ψ (entrywiseCongr φ A) = entrywiseCongr (ψ.comp φ) A := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single, entrywiseCongr_single, entrywiseCongr_single]
  simp [Finsupp.mapRange_apply]

theorem entrywiseCongr_id (A : Module.End K (RootModule τ K)) :
    entrywiseCongr (RingHom.id K) A = A := by
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single]
  simp

@[expose] noncomputable def entrywiseCongrHom (φ : K →+* L) :
    Module.End K (RootModule τ K) →* Module.End L (RootModule τ L) where
  toFun := entrywiseCongr φ
  map_one' := entrywiseCongr_one φ
  map_mul' := entrywiseCongr_mul φ

theorem entrywiseCongr_symm_comp (φ : K ≃+* L) (A : Module.End K (RootModule τ K)) :
    entrywiseCongr φ.symm.toRingHom (entrywiseCongr φ.toRingHom A) = A := by
  rw [entrywiseCongr_comp, RingEquiv.symm_toRingHom_comp_toRingHom, entrywiseCongr_id]

theorem entrywiseCongr_comp_symm (φ : K ≃+* L) (A : Module.End L (RootModule τ L)) :
    entrywiseCongr φ.toRingHom (entrywiseCongr φ.symm.toRingHom A) = A := by
  rw [entrywiseCongr_comp, RingEquiv.toRingHom_comp_symm_toRingHom, entrywiseCongr_id]

@[expose] noncomputable def modGLCongr (τ : Tag) (φ : K ≃+* L) : ModGL τ K ≃* ModGL τ L where
  toFun := Units.map (entrywiseCongrHom φ.toRingHom)
  invFun := Units.map (entrywiseCongrHom φ.symm.toRingHom)
  left_inv g := Units.ext (entrywiseCongr_symm_comp φ (g : Module.End K (RootModule τ K)))
  right_inv g := Units.ext (entrywiseCongr_comp_symm φ (g : Module.End L (RootModule τ L)))
  map_mul' g h := map_mul _ g h

theorem coe_modGLCongr (τ : Tag) (φ : K ≃+* L) (g : ModGL τ K) :
    ((modGLCongr τ φ g : ModGL τ L) : Module.End L (RootModule τ L)) =
      entrywiseCongr φ.toRingHom (g : Module.End K (RootModule τ K)) := rfl

theorem mapRange_smul_semi (φ : K →+* L) (c : K) (v : RootModule τ K) :
    Finsupp.mapRange φ φ.map_zero (c • v) = φ c • Finsupp.mapRange φ φ.map_zero v := by
  ext l
  simp

theorem mapRange_sum_pow_smul (φ : K →+* L) (c : K) (s : Finset ℕ)
    (v : ℕ → RootModule τ K) :
    Finsupp.mapRange φ φ.map_zero (∑ k ∈ s, c ^ k • v k) =
      ∑ k ∈ s, φ c ^ k • Finsupp.mapRange φ φ.map_zero (v k) := by
  have h := map_sum
    (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom : (Label τ →₀ K) →+ (Label τ →₀ L))
    (fun k => c ^ k • v k) s
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  change Finsupp.mapRange φ φ.map_zero (c ^ k • v k) = _
  rw [mapRange_smul_semi, map_pow]

theorem entrywiseCongr_xOp (φ : K ≃+* L) (i : Fin τ.rank) (c : K) :
    entrywiseCongr φ.toRingHom (xOp τ K i c) = xOp τ L i (φ c) := by
  apply Finsupp.lhom_ext'
  intro b
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [mapRange_sum_pow_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mapRange_xCoeff_single]
  rfl

theorem entrywiseCongr_yOp (φ : K ≃+* L) (i : Fin τ.rank) (c : K) :
    entrywiseCongr φ.toRingHom (yOp τ K i c) = yOp τ L i (φ c) := by
  apply Finsupp.lhom_ext'
  intro b
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [mapRange_sum_pow_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mapRange_yCoeff_single]
  rfl

theorem map_adjointGroup (τ : Tag) (φ : K ≃+* L) :
    (adjointGroup τ K).map (modGLCongr τ φ).toMonoidHom = adjointGroup τ L := by
  unfold adjointGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext h
  constructor
  · rintro ⟨g, ⟨i, c, hg⟩, rfl⟩
    refine ⟨i, φ c, ?_⟩
    rcases hg with hg | hg
    · left
      rw [MulEquiv.coe_toMonoidHom, coe_modGLCongr, hg, entrywiseCongr_xOp]
    · right
      rw [MulEquiv.coe_toMonoidHom, coe_modGLCongr, hg, entrywiseCongr_yOp]
  · rintro ⟨i, c, hh⟩
    refine ⟨(modGLCongr τ φ).symm h, ⟨i, φ.symm c, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    have hinj : Function.Injective (entrywiseCongr (τ := τ) φ.toRingHom) := fun A B hAB => by
      rw [← entrywiseCongr_symm_comp φ A, hAB, entrywiseCongr_symm_comp]
    have hcoe : entrywiseCongr φ.toRingHom (((modGLCongr τ φ).symm h : ModGL τ K) :
        Module.End K (RootModule τ K)) = (h : Module.End L (RootModule τ L)) := by
      rw [← coe_modGLCongr, MulEquiv.apply_symm_apply]
    rcases hh with hh | hh
    · left
      apply hinj
      rw [hcoe, hh, entrywiseCongr_xOp, RingEquiv.apply_symm_apply]
    · right
      apply hinj
      rw [hcoe, hh, entrywiseCongr_yOp, RingEquiv.apply_symm_apply]

noncomputable def centerQuotientCongr {M N : Type} [Group M] [Group N] (e : M ≃* N)
    {H : Subgroup M} {H' : Subgroup N} (h : H.map e.toMonoidHom = H') :
    ↥H ⧸ Subgroup.center ↥H ≃* ↥H' ⧸ Subgroup.center ↥H' :=
  let E : ↥H ≃* ↥H' := (H.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)
  QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)

noncomputable def adjointQuotientCongr (τ : Tag) (φ : K ≃+* L) :
    AdjointQuotient τ K ≃* AdjointQuotient τ L :=
  centerQuotientCongr (modGLCongr τ φ) (map_adjointGroup τ φ)

theorem entrywiseCongr_entrywise (φ : K ≃+* L) (σ : K →+* K) (σ' : L →+* L)
    (hσ : ∀ c, φ (σ c) = σ' (φ c)) (A : Module.End K (RootModule τ K)) :
    entrywiseCongr φ.toRingHom (entrywise σ A) = entrywise σ' (entrywiseCongr φ.toRingHom A) := by
  apply Finsupp.lhom_ext'
  intro b
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single, entrywise_single, entrywise_single, entrywiseCongr_single]
  ext l
  simp [hσ]

theorem entrywiseCongr_diagramMap (t : TwistTag) (φ : K ≃+* L) :
    entrywiseCongr φ.toRingHom ((diagramMap t K : ModGL t.tag K) :
      Module.End K (RootModule t.tag K)) =
      ((diagramMap t L : ModGL t.tag L) : Module.End L (RootModule t.tag L)) := by
  apply Finsupp.lhom_ext'
  intro b
  refine LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywiseCongr_single]
  simp [diagramMap]

theorem modGLCongr_diagramMap (t : TwistTag) (φ : K ≃+* L) :
    modGLCongr t.tag φ (diagramMap t K) = diagramMap t L :=
  Units.ext (entrywiseCongr_diagramMap t φ)

theorem modGLCongr_twistHom (t : TwistTag) (φ : K ≃+* L) (σ : K →+* K) (σ' : L →+* L)
    (hσ : ∀ c, φ (σ c) = σ' (φ c)) (g : ModGL t.tag K) :
    modGLCongr t.tag φ (twistHom t K σ g) = twistHom t L σ' (modGLCongr t.tag φ g) := by
  have h1 : modGLCongr t.tag φ (Units.map (entrywiseHom σ) g) =
      Units.map (entrywiseHom σ') (modGLCongr t.tag φ g) :=
    Units.ext (entrywiseCongr_entrywise φ σ σ' hσ _)
  simp only [twistHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv, h1, modGLCongr_diagramMap]

theorem map_twistedFixedGroup (t : TwistTag) (φ : K ≃+* L) (σ : K →+* K) (σ' : L →+* L)
    (hσ : ∀ c, φ (σ c) = σ' (φ c)) :
    (twistedFixedGroup t K σ).map (modGLCongr t.tag φ).toMonoidHom = twistedFixedGroup t L σ' := by
  unfold twistedFixedGroup
  rw [Subgroup.map_inf _ _ (modGLCongr t.tag φ).toMonoidHom (modGLCongr t.tag φ).injective,
    map_adjointGroup]
  congr 1
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : twistHom t K σ g = g := hg
    show twistHom t L σ' (modGLCongr t.tag φ g) = modGLCongr t.tag φ g
    rw [← modGLCongr_twistHom t φ σ σ' hσ, hg']
  · intro hx
    refine ⟨(modGLCongr t.tag φ).symm x, ?_, MulEquiv.apply_symm_apply _ _⟩
    have hx' : twistHom t L σ' x = x := hx
    show twistHom t K σ ((modGLCongr t.tag φ).symm x) = (modGLCongr t.tag φ).symm x
    apply (modGLCongr t.tag φ).injective
    rw [modGLCongr_twistHom t φ σ σ' hσ, MulEquiv.apply_symm_apply, hx']

noncomputable def twistedQuotientCongr (t : TwistTag) (φ : K ≃+* L) (σ : K →+* K) (σ' : L →+* L)
    (hσ : ∀ c, φ (σ c) = σ' (φ c)) :
    DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
      DerivedCentralQuotient (twistedFixedGroup t L σ') :=
  centerQuotientCongr (modGLCongr t.tag φ) (by
    rw [Subgroup.map_commutator, map_twistedFixedGroup t φ σ σ' hσ])

end Entrywise


theorem untwistedChevalleyModel_unique {X Y : Type} [Group X] [Group Y] {τ : Tag} {q : ℕ}
    (hX : UntwistedChevalleyModel X τ q) (hY : UntwistedChevalleyModel Y τ q) :
    Nonempty (X ≃* Y) := by
  obtain ⟨K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
  obtain ⟨K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
  let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
  exact ⟨e₁.trans ((adjointQuotientCongr τ φ).trans e₂.symm)⟩

theorem twistedChevalleyModel_unique {X Y : Type} [Group X] [Group Y] {t : TwistTag} {q : ℕ}
    (hX : TwistedChevalleyModel X t q) (hY : TwistedChevalleyModel Y t q) :
    Nonempty (X ≃* Y) := by
  obtain ⟨K₁, _, _, hc₁, σ₁, hσ₁, ⟨e₁⟩⟩ := hX
  obtain ⟨K₂, _, _, hc₂, σ₂, hσ₂, ⟨e₂⟩⟩ := hY
  let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
  exact ⟨e₁.trans ((twistedQuotientCongr t φ σ₁ σ₂
    (fun c => by rw [hσ₁, hσ₂, map_pow])).trans e₂.symm)⟩

theorem chevalleyExceptionalModel_unique {X Y : Type} [Group X] [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {r e : ℕ} (hX : ChevalleyExceptionalModel X t r e)
    (hY : ChevalleyExceptionalModel Y t r e) : Nonempty (X ≃* Y) := by
  cases t
  case G2 => exact untwistedChevalleyModel_unique hX.2 hY.2
  case F4 => exact untwistedChevalleyModel_unique hX.2 hY.2
  case E6 => exact untwistedChevalleyModel_unique hX.2 hY.2
  case E7 => exact untwistedChevalleyModel_unique hX.2 hY.2
  case E8 => exact untwistedChevalleyModel_unique hX.2 hY.2
  case twistedE6 => exact twistedChevalleyModel_unique hX.2 hY.2
  case trialityD4 => exact twistedChevalleyModel_unique hX.2 hY.2
  all_goals exact hX.2.elim

end CFSG.ClassicalInvolution.Upgrade
