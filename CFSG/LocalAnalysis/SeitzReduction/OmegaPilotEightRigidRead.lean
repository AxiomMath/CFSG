module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualGeneric
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherKernels

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Read

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

@[expose] def ReadsThroughE (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L)) (X : Subgroup C)
    (Y : Type*) [Group Y] (R : MulAut Y → (L ≃+* L) → Prop) : Prop :=
  ∀ (M : Subgroup ↥X) [M.Normal] (ε : ↥X ⧸ M ≃* Y) (β : MulAut C) (hβE : β ∈ E)
    (hβ : ∀ x ∈ X, β x ∈ X) (hM : ∀ m ∈ M, restrictAutOfMapsTo β X hβ m ∈ M),
    R ((ε.symm.trans (quotAutOfMapsTo M (restrictAutOfMapsTo β X hβ) hM)).trans ε) (fp ⟨β, hβE⟩)

@[expose] def HasInvariantQuotientE (E : Subgroup (MulAut C)) (X : Subgroup C) (Y : Type*)
    [Group Y] : Prop :=
  ∃ (M : Subgroup ↥X) (_ : M.Normal), Nonempty (↥X ⧸ M ≃* Y) ∧
    ∀ (β : MulAut C), β ∈ E → ∀ (hβ : ∀ x ∈ X, β x ∈ X), ∀ m ∈ M,
      restrictAutOfMapsTo β X hβ m ∈ M

theorem fieldRigidInOfE_of_readsThroughE (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L))
    {X₁ X₂ : Subgroup C} {Y : Type*} [Group Y] {R : MulAut Y → (L ≃+* L) → Prop}
    (huniq : ∀ θ σ σ', R θ σ → R θ σ' → σ = σ') (hq : HasInvariantQuotientE E X₁ Y)
    (hr₁ : ReadsThroughE E fp X₁ Y R) (hr₂ : ReadsThroughE E fp X₂ Y R) :
    FieldRigidInOfE E fp X₁ X₂ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁E hβ₂E hβ₁ hc₁ hc₂
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
  have hpres₁ := hinv β₁ hβ₁E hβ₁
  have hpres₂ : ∀ m ∈ M₁.map (ψ : ↥X₁ →* ↥X₂),
      restrictAutOfMapsTo β₂ X₂ hβ₂ m ∈ M₁.map (ψ : ↥X₁ →* ↥X₂) := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hpres₁ m hm, (hθ m).symm⟩
  have h1 := hr₁ M₁ ε₁ β₁ hβ₁E hβ₁ hpres₁
  have h2 := hr₂ (M₁.map (ψ : ↥X₁ →* ↥X₂))
    ((QuotientGroup.congr M₁ (M₁.map (ψ : ↥X₁ →* ↥X₂)) ψ rfl).symm.trans ε₁) β₂ hβ₂E hβ₂ hpres₂
  rw [quotReading_congr ψ hθ M₁ _ rfl hpres₁ hpres₂ ε₁] at h2
  exact huniq _ _ _ h1 h2

@[expose] def CoreReadE (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L)) (X : Subgroup C)
    {ι : Type*} (Y : ι → Type*) [∀ i, Group (Y i)] (R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop) :
    Prop :=
  (∃ i, HasInvariantQuotientE E X (Y i)) ∧ ∀ i, ReadsThroughE E fp X (Y i) (R i)

theorem fieldRigidInOfE_of_coreReadE (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L))
    {X₁ X₂ : Subgroup C} {ι : Type*} {Y : ι → Type*} [∀ i, Group (Y i)]
    {R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop}
    (huniq : ∀ i θ σ σ', R i θ σ → R i θ σ' → σ = σ') (h₁ : CoreReadE E fp X₁ Y R)
    (h₂ : CoreReadE E fp X₂ Y R) : FieldRigidInOfE E fp X₁ X₂ := by
  obtain ⟨⟨i, hi⟩, hr₁⟩ := h₁
  exact fieldRigidInOfE_of_readsThroughE E fp (huniq i) hi (hr₁ i) (h₂.2 i)

end Read

section Transport

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

theorem hasInvariantQuotientE_map {E : Subgroup (MulAut C)} {X : Subgroup C} {Y : Type*}
    [Group Y] (h : HasInvariantQuotientE E X Y) {δ : MulAut C} (hδ : δ ∈ E) :
    HasInvariantQuotientE E (X.map δ.toMonoidHom) Y := by
  obtain ⟨M, hM, ⟨ε⟩, hinv⟩ := h
  set d := X.equivMapOfInjective δ.toMonoidHom δ.injective with hd
  have : (M.map (d : ↥X →* ↥(X.map δ.toMonoidHom))).Normal := hM.map _ d.surjective
  refine ⟨M.map (d : ↥X →* ↥(X.map δ.toMonoidHom)), inferInstance,
    ⟨(QuotientGroup.congr M _ d rfl).symm.trans ε⟩, ?_⟩
  intro β' hβ'E hβ'
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨_, hinv _ (mul_mem (mul_mem (inv_mem hδ) hβ'E) hδ) (mapsTo_conj_of_mapsTo_map hβ') m hm,
    (restrictAutOfMapsTo_map_apply hβ' m).symm⟩

variable [Finite L]

omit [Finite C] in
theorem fp_conj_eq {E : Subgroup (MulAut C)} (fp : E →* (L ≃+* L)) {δ β : MulAut C}
    (hδ : δ ∈ E) (hβ : β ∈ E) :
    fp ⟨δ⁻¹ * β * δ, mul_mem (mul_mem (inv_mem hδ) hβ) hδ⟩ = fp ⟨β, hβ⟩ := by
  have e1 : (⟨δ⁻¹ * β * δ, mul_mem (mul_mem (inv_mem hδ) hβ) hδ⟩ : E) =
      (⟨δ, hδ⟩ : E)⁻¹ * ⟨β, hβ⟩ * ⟨δ, hδ⟩ := Subtype.ext rfl
  rw [e1, map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp ⟨δ, hδ⟩)⁻¹, mul_assoc,
    inv_mul_cancel, mul_one]

theorem readsThroughE_map {E : Subgroup (MulAut C)} (fp : E →* (L ≃+* L)) {X : Subgroup C}
    {Y : Type*} [Group Y] {R : MulAut Y → (L ≃+* L) → Prop} (h : ReadsThroughE E fp X Y R)
    {δ : MulAut C} (hδ : δ ∈ E) : ReadsThroughE E fp (X.map δ.toMonoidHom) Y R := by
  intro M' _ ε' β' hβ'E hβ' hM'
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
    (mul_mem (mul_mem (inv_mem hδ) hβ'E) hδ) (mapsTo_conj_of_mapsTo_map hβ') hM
  rw [← quotReading_congr d hθ M M' hMM' hM hM' ((QuotientGroup.congr M M' d hMM').trans ε')]
    at key
  have hε : (QuotientGroup.congr M M' d hMM').symm.trans
      ((QuotientGroup.congr M M' d hMM').trans ε') = ε' := by
    ext y
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [hε, fp_conj_eq fp hδ hβ'E] at key
  exact key

theorem coreReadE_map {E : Subgroup (MulAut C)} (fp : E →* (L ≃+* L)) {X : Subgroup C}
    {ι : Type*} {Y : ι → Type*} [∀ i, Group (Y i)] {R : ∀ i, MulAut (Y i) → (L ≃+* L) → Prop}
    (h : CoreReadE E fp X Y R) {δ : MulAut C} (hδ : δ ∈ E) :
    CoreReadE E fp (X.map δ.toMonoidHom) Y R :=
  ⟨let ⟨i, hi⟩ := h.1; ⟨i, hasInvariantQuotientE_map hi hδ⟩,
    fun i => readsThroughE_map fp (h.2 i) hδ⟩

end Transport

section Three

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

theorem readsThroughE_of_three (E : Subgroup (MulAut C)) (fp : E →* (L ≃+* L)) {X : Subgroup C}
    {Y : Type*} [Group Y] [IsSimpleGroup Y] (hnc : ∃ a b : Y, a * b ≠ b * a)
    {R : MulAut Y → (L ≃+* L) → Prop} (N₁ N₂ N₃ : Subgroup ↥X) [N₁.Normal] [N₂.Normal]
    [N₃.Normal] (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hr : ∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      ∀ (ε : ↥X ⧸ N ≃* Y) (β : MulAut C) (hβE : β ∈ E) (hβ : ∀ x ∈ X, β x ∈ X)
        (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
        R ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε)
          (fp ⟨β, hβE⟩)) :
    ReadsThroughE E fp X Y R := by
  intro M _ ε β hβE hβ hM
  have : IsSimpleGroup (↥X ⧸ M) := MulEquiv.isSimpleGroup ε
  have hnc' : ∃ a b : ↥X ⧸ M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨ε.symm a, ε.symm b, fun h => hab ?_⟩
    have h' := congrArg ε h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : N₁ ⊓ N₂ ⊓ N₃ ≤ M := le_of_isPGroup_of_simple hnc' h123
  have hMtop : M ≠ ⊤ := by
    rintro rfl
    have hnt : Nontrivial (↥X ⧸ (⊤ : Subgroup ↥X)) := IsSimpleGroup.toNontrivial
    exact (not_nontrivial_iff_subsingleton.mpr QuotientGroup.subsingleton_quotient_top) hnt
  have key : ∀ N : Subgroup ↥X, N.Normal → N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) → N ≤ M →
      R ((ε.symm.trans (quotAutOfMapsTo M (restrictAutOfMapsTo β X hβ) hM)).trans ε)
        (fp ⟨β, hβE⟩) := by
    intro N hNn hmem hNM
    rcases hq N hmem M inferInstance hNM with rfl | hM'
    · exact hr M hmem ε β hβE hβ hM
    · exact absurd hM' hMtop
  rcases le_or_le_of_inf_le hnc' hinf with h | h
  · rcases le_or_le_of_inf_le hnc' h with h' | h'
    · exact key N₁ inferInstance (by simp) h'
    · exact key N₂ inferInstance (by simp) h'
  · exact key N₃ inferInstance (by simp) h

end Three

end CFSG.SeitzReduction.OmegaPilot
