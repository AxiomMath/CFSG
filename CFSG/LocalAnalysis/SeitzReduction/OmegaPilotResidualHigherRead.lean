module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixFR

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Quot

variable {G : Type*} [Group G]

theorem subgroup_map_eq_of_mapsTo [Finite G] (μ : MulAut G) {N : Subgroup G} (h : ∀ x ∈ N, μ x ∈ N) :
    N.map (μ : G →* G) = N :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
    (Subgroup.card_map_of_injective μ.injective).ge

@[expose] noncomputable def quotAutOfMapsTo [Finite G] (N : Subgroup G) [N.Normal] (μ : MulAut G)
    (h : ∀ x ∈ N, μ x ∈ N) : MulAut (G ⧸ N) :=
  QuotientGroup.congr N N μ (subgroup_map_eq_of_mapsTo μ h)

theorem quotAutOfMapsTo_mk [Finite G] (N : Subgroup G) [N.Normal] (μ : MulAut G)
    (h : ∀ x ∈ N, μ x ∈ N) (x : G) :
    quotAutOfMapsTo N μ h (x : G ⧸ N) = ((μ x : G) : G ⧸ N) :=
  rfl

theorem quotReading_congr {X₁ X₂ Y : Type*} [Group X₁] [Group X₂] [Group Y] [Finite X₁]
    [Finite X₂] (ψ : X₁ ≃* X₂) {θ₁ : MulAut X₁} {θ₂ : MulAut X₂}
    (hθ : ∀ x, θ₂ (ψ x) = ψ (θ₁ x)) (M₁ : Subgroup X₁) (M₂ : Subgroup X₂) [M₁.Normal]
    [M₂.Normal] (hM : M₁.map (ψ : X₁ →* X₂) = M₂) (h₁ : ∀ m ∈ M₁, θ₁ m ∈ M₁)
    (h₂ : ∀ m ∈ M₂, θ₂ m ∈ M₂) (ε₁ : X₁ ⧸ M₁ ≃* Y) :
    (((QuotientGroup.congr M₁ M₂ ψ hM).symm.trans ε₁).symm.trans
        (quotAutOfMapsTo M₂ θ₂ h₂)).trans ((QuotientGroup.congr M₁ M₂ ψ hM).symm.trans ε₁) =
      (ε₁.symm.trans (quotAutOfMapsTo M₁ θ₁ h₁)).trans ε₁ := by
  ext y
  obtain ⟨z, rfl⟩ := ε₁.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set e := QuotientGroup.congr M₁ M₂ ψ hM with he
  have hmk : ∀ u : X₁, e (u : X₁ ⧸ M₁) = ((ψ u : X₂) : X₂ ⧸ M₂) := fun u => rfl
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply]
  rw [hmk, quotAutOfMapsTo_mk, hθ, ← hmk, MulEquiv.symm_apply_apply, quotAutOfMapsTo_mk]

end Quot

section Read

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

@[expose] def ReadsThrough (fp : MulAut C →* (L ≃+* L)) (X : Subgroup C) (Y : Type*) [Group Y]
    (R : MulAut Y → (L ≃+* L) → Prop) : Prop :=
  ∀ (M : Subgroup ↥X) [M.Normal] (ε : ↥X ⧸ M ≃* Y) (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X)
    (hM : ∀ m ∈ M, restrictAutOfMapsTo β X hβ m ∈ M),
    R ((ε.symm.trans (quotAutOfMapsTo M (restrictAutOfMapsTo β X hβ) hM)).trans ε) (fp β)

@[expose] def HasInvariantQuotient (X : Subgroup C) (Y : Type*) [Group Y] : Prop :=
  ∃ (M : Subgroup ↥X) (_ : M.Normal), Nonempty (↥X ⧸ M ≃* Y) ∧
    ∀ (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X), ∀ m ∈ M, restrictAutOfMapsTo β X hβ m ∈ M

theorem fieldRigidInOf_of_readsThrough (fp : MulAut C →* (L ≃+* L)) {X₁ X₂ : Subgroup C}
    {Y : Type*} [Group Y] {R : MulAut Y → (L ≃+* L) → Prop}
    (huniq : ∀ θ σ σ', R θ σ → R θ σ' → σ = σ') (hq : HasInvariantQuotient X₁ Y)
    (hr₁ : ReadsThrough fp X₁ Y R) (hr₂ : ReadsThrough fp X₂ Y R) : FieldRigidInOf fp X₁ X₂ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁ hc₁ hc₂
  set ψ : ↥X₁ ≃* ↥X₂ := (X₁.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X₂.equivMapOfInjective φ₂ hφ₂).symm) with hψ
  have hψφ : ∀ x : X₁, φ₂ (ψ x : C) = φ₁ x := fun x => by
    have h1 : X₂.equivMapOfInjective φ₂ hφ₂ (ψ x) =
        MulEquiv.subgroupCongr hX (X₁.equivMapOfInjective φ₁ hφ₁ x) := by
      rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun y : ↥(X₂.map φ₂) => (y : Γ)) h1
    simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  have hkey : ∀ x : X₁, β₂ (ψ x : C) = (ψ ⟨β₁ x, hβ₁ x x.2⟩ : C) := fun x => by
    apply hφ₂
    rw [hc₂, hψφ, hψφ, hc₁]
  have hβ₂ : ∀ y ∈ X₂, β₂ y ∈ X₂ := fun y hy => by
    obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
    have : y = (ψ x : C) := by rw [hx]
    rw [this, hkey]
    exact (ψ _).2
  have hθ : ∀ x : X₁, restrictAutOfMapsTo β₂ X₂ hβ₂ (ψ x) =
      ψ (restrictAutOfMapsTo β₁ X₁ hβ₁ x) := fun x =>
    Subtype.ext (by rw [coe_restrictAutOfMapsTo, hkey]; rfl)
  obtain ⟨M₁, hM₁, ⟨ε₁⟩, hinv⟩ := hq
  have hM₂ : (M₁.map (ψ : ↥X₁ →* ↥X₂)).Normal := hM₁.map _ ψ.surjective
  have hpres₁ := hinv β₁ hβ₁
  have hpres₂ : ∀ m ∈ M₁.map (ψ : ↥X₁ →* ↥X₂),
      restrictAutOfMapsTo β₂ X₂ hβ₂ m ∈ M₁.map (ψ : ↥X₁ →* ↥X₂) := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hpres₁ m hm, (hθ m).symm⟩
  have h1 := hr₁ M₁ ε₁ β₁ hβ₁ hpres₁
  have h2 := hr₂ (M₁.map (ψ : ↥X₁ →* ↥X₂))
    ((QuotientGroup.congr M₁ (M₁.map (ψ : ↥X₁ →* ↥X₂)) ψ rfl).symm.trans ε₁) β₂ hβ₂ hpres₂
  rw [quotReading_congr ψ hθ M₁ _ rfl hpres₁ hpres₂ ε₁] at h2
  exact huniq _ _ _ h1 h2

@[expose] def CoreRead (fp : MulAut C →* (L ≃+* L)) (X : Subgroup C) {ι : Type*}
    (Y : ι → Type*) [∀ i, Group (Y i)] (R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop) : Prop :=
  (∃ i, HasInvariantQuotient X (Y i)) ∧ ∀ i, ReadsThrough fp X (Y i) (R i)

theorem fieldRigidInOf_of_coreRead (fp : MulAut C →* (L ≃+* L)) {X₁ X₂ : Subgroup C}
    {ι : Type*} {Y : ι → Type*} [∀ i, Group (Y i)] {R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop}
    (huniq : ∀ i θ σ σ', R i θ σ → R i θ σ' → σ = σ') (h₁ : CoreRead fp X₁ Y R)
    (h₂ : CoreRead fp X₂ Y R) : FieldRigidInOf fp X₁ X₂ := by
  obtain ⟨⟨i, hi⟩, hr₁⟩ := h₁
  exact fieldRigidInOf_of_readsThrough fp (huniq i) hi (hr₁ i) (h₂.2 i)

end Read

section Transport

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

omit [Finite C] in
theorem mapsTo_conj_of_mapsTo_map {δ β' : MulAut C} {X : Subgroup C}
    (hβ' : ∀ x ∈ X.map δ.toMonoidHom, β' x ∈ X.map δ.toMonoidHom) :
    ∀ x ∈ X, (δ⁻¹ * β' * δ) x ∈ X := fun x hx => by
  obtain ⟨y, hy, hyx⟩ := hβ' _ (⟨x, hx, rfl⟩ : δ x ∈ X.map δ.toMonoidHom)
  have : (δ⁻¹ * β' * δ) x = y := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hyx]
    exact δ.symm_apply_apply y
  rw [this]
  exact hy

theorem restrictAutOfMapsTo_map_apply {δ β' : MulAut C} {X : Subgroup C}
    (hβ' : ∀ x ∈ X.map δ.toMonoidHom, β' x ∈ X.map δ.toMonoidHom) (x : X) :
    restrictAutOfMapsTo β' _ hβ' (X.equivMapOfInjective δ.toMonoidHom δ.injective x) =
      X.equivMapOfInjective δ.toMonoidHom δ.injective
        (restrictAutOfMapsTo (δ⁻¹ * β' * δ) X (mapsTo_conj_of_mapsTo_map hβ') x) := by
  apply Subtype.ext
  change β' (δ (x : C)) = δ ((δ⁻¹ * β' * δ) (x : C))
  rw [MulAut.mul_apply, MulAut.mul_apply]
  exact (δ.apply_symm_apply _).symm

theorem hasInvariantQuotient_map {X : Subgroup C} {Y : Type*} [Group Y]
    (h : HasInvariantQuotient X Y) (δ : MulAut C) :
    HasInvariantQuotient (X.map δ.toMonoidHom) Y := by
  obtain ⟨M, hM, ⟨ε⟩, hinv⟩ := h
  set d := X.equivMapOfInjective δ.toMonoidHom δ.injective with hd
  have : (M.map (d : ↥X →* ↥(X.map δ.toMonoidHom))).Normal := hM.map _ d.surjective
  refine ⟨M.map (d : ↥X →* ↥(X.map δ.toMonoidHom)), inferInstance,
    ⟨(QuotientGroup.congr M _ d rfl).symm.trans ε⟩, ?_⟩
  intro β' hβ'
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨_, hinv _ (mapsTo_conj_of_mapsTo_map hβ') m hm,
    (restrictAutOfMapsTo_map_apply hβ' m).symm⟩

variable [Finite L]

theorem readsThrough_map (fp : MulAut C →* (L ≃+* L)) {X : Subgroup C} {Y : Type*} [Group Y]
    {R : MulAut Y → (L ≃+* L) → Prop} (h : ReadsThrough fp X Y R) (δ : MulAut C) :
    ReadsThrough fp (X.map δ.toMonoidHom) Y R := by
  intro M' _ ε' β' hβ' hM'
  set d := X.equivMapOfInjective δ.toMonoidHom δ.injective with hd
  have hθ := restrictAutOfMapsTo_map_apply hβ'
  set M : Subgroup ↥X := M'.comap (d : ↥X →* ↥(X.map δ.toMonoidHom)) with hMdef
  have hMn : M.Normal := ‹M'.Normal›.comap _
  have hMM' : M.map (d : ↥X →* ↥(X.map δ.toMonoidHom)) = M' :=
    Subgroup.map_comap_eq_self_of_surjective d.surjective M'
  have hM : ∀ m ∈ M, restrictAutOfMapsTo (δ⁻¹ * β' * δ) X (mapsTo_conj_of_mapsTo_map hβ') m ∈ M :=
    fun m hm => by
      change d (restrictAutOfMapsTo (δ⁻¹ * β' * δ) X (mapsTo_conj_of_mapsTo_map hβ') m) ∈ M'
      rw [← hθ]
      exact hM' _ hm
  have key := h M ((QuotientGroup.congr M M' d hMM').trans ε') _
    (mapsTo_conj_of_mapsTo_map hβ') hM
  rw [← quotReading_congr d hθ M M' hMM' hM hM' ((QuotientGroup.congr M M' d hMM').trans ε')]
    at key
  have hε : (QuotientGroup.congr M M' d hMM').symm.trans
      ((QuotientGroup.congr M M' d hMM').trans ε') = ε' := by
    ext y
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [hε] at key
  have hfp : fp (δ⁻¹ * β' * δ) = fp β' := by
    rw [map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp δ)⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  rwa [hfp] at key

theorem coreRead_map (fp : MulAut C →* (L ≃+* L)) {X : Subgroup C} {ι : Type*}
    {Y : ι → Type*} [∀ i, Group (Y i)] {R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop}
    (h : CoreRead fp X Y R) (δ : MulAut C) : CoreRead fp (X.map δ.toMonoidHom) Y R :=
  ⟨let ⟨i, hi⟩ := h.1; ⟨i, hasInvariantQuotient_map hi δ⟩, fun i => readsThrough_map fp (h.2 i) δ⟩

end Transport

section Cores

open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem higherRankCoresRigid_of_coreRead
    {fp : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)}
    {ι : Type*} {Y : ι → Type*} [∀ i, Group (Y i)] {R : ∀ i, MulAut (Y i) → (K ≃+* K) → Prop}
    (huniq : ∀ i θ σ σ', R i θ σ → R i θ σ' → σ = σ')
    (h : ∀ s : matrixIsometries (coordinateQuadPlus n K),
      orderOf (isometryConjugationHom _ s) = 2 →
      2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank →
      CoreRead fp (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) Y R) :
    HigherRankCoresRigid n K fp :=
  fun s₁ s₂ h₁ h₂ hr₁ hr₂ => fieldRigidInOf_of_coreRead fp huniq (h s₁ h₁ hr₁) (h s₂ h₂ hr₂)

theorem isometryCore_conj (s a : matrixIsometries (coordinateQuadPlus n K)) :
    perfectCore (autFixSubgroup (isometryConjugationHom _ (a * s * a⁻¹))) =
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))).map
        (isometryConjugationHom _ a).toMonoidHom := by
  rw [map_mul, map_mul, map_inv, LinearPilot.autFixSubgroup_conj,
    CFSG.Quasithin.map_perfectCore]

theorem coreRead_conj
    {fp : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)}
    {ι : Type*} {Y : ι → Type*} [∀ i, Group (Y i)] {R : ∀ i, MulAut (Y i) → (K ≃+* K) → Prop}
    {s : matrixIsometries (coordinateQuadPlus n K)}
    (h : CoreRead fp (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) Y R)
    (a : matrixIsometries (coordinateQuadPlus n K)) :
    CoreRead fp (perfectCore (autFixSubgroup (isometryConjugationHom _ (a * s * a⁻¹)))) Y R := by
  rw [isometryCore_conj]
  exact coreRead_map fp h _

end Cores

end CFSG.SeitzReduction.OmegaPilot
