module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidRead
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Defs

variable {C : Type*} [Group C] [Finite C]

@[expose] def SpLeviSectionE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) (X : Subgroup C)
    (N : Subgroup ↥X) [N.Normal] : Prop :=
  (∀ r : ℕ, 1 ≤ r → IsEmpty (↥X ⧸ N ≃* StatedProj (StatedSp r K))) ∨
    ∃ (r₀ : ℕ) (_ : 1 ≤ r₀) (ε₀ : ↥X ⧸ N ≃* StatedProj (StatedSp r₀ K)),
      ∀ (β : MulAut C) (hβE : β ∈ E) (hβ : ∀ x ∈ X, β x ∈ X)
        (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
        SpTraceRead r₀
          ((ε₀.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε₀)
          (fp ⟨β, hβE⟩)

@[expose] def SpLeviDataE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) (X : Subgroup C) :
    Prop :=
  ∃ (N₁ N₂ N₃ : Subgroup ↥X) (_ : N₁.Normal) (_ : N₂.Normal) (_ : N₃.Normal),
    IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃) ∧
    (∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤) ∧
    (∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      SpLeviSectionE E fp X N) ∧
    ∃ r : ℕ, 1 ≤ r ∧ Nonempty (↥X ⧸ N₁ ≃* StatedProj (StatedSp r K)) ∧
      ∀ (β : MulAut C), β ∈ E → ∀ (hβ : ∀ x ∈ X, β x ∈ X), ∀ m ∈ N₁,
        restrictAutOfMapsTo β X hβ m ∈ N₁

abbrev SpCoreReadE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) (X : Subgroup C) : Prop :=
  CoreReadE E fp X (SpTarget K) (SpRel K)

end Defs

section Core

variable {C : Type*} [Group C] [Finite C]

theorem spTraceRead_of_chartE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {X : Subgroup C} (N : Subgroup ↥X) [N.Normal] {r₀ : ℕ}
    (hr₀ : 1 ≤ r₀) (ε₀ : ↥X ⧸ N ≃* StatedProj (StatedSp r₀ K))
    (h₀ : ∀ (β : MulAut C) (hβE : β ∈ E) (hβ : ∀ x ∈ X, β x ∈ X)
      (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
      SpTraceRead r₀ ((ε₀.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε₀)
        (fp ⟨β, hβE⟩))
    {r : ℕ} (ε : ↥X ⧸ N ≃* StatedProj (StatedSp r K)) (β : MulAut C) (hβE : β ∈ E)
    (hβ : ∀ x ∈ X, β x ∈ X) (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N) :
    SpTraceRead r ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε)
      (fp ⟨β, hβE⟩) := by
  obtain rfl := rank_eq_of_mulEquiv (ε₀.symm.trans ε)
  have h := spTraceRead_conj_of_one_le hK hr₀ (ε₀.symm.trans ε) (h₀ β hβE hβ hN)
  convert h using 1
  ext y
  simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_def, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

theorem readsThroughE_section_of_spLeviSectionE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K))
    {f : ℕ} (hK : Nat.card K = 2 ^ f) {X : Subgroup C} {N : Subgroup ↥X} [N.Normal]
    (h : SpLeviSectionE E fp X N) (r : {r : ℕ // 1 ≤ r}) (ε : ↥X ⧸ N ≃* SpTarget K r)
    (β : MulAut C) (hβE : β ∈ E) (hβ : ∀ x ∈ X, β x ∈ X)
    (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N) :
    SpRel K r ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε)
      (fp ⟨β, hβE⟩) := by
  rcases h with hno | ⟨r₀, hr₀, ε₀, h₀⟩
  · exact ((hno r.1 r.2).false ε).elim
  · exact spTraceRead_of_chartE E fp hK N hr₀ ε₀ h₀ ε β hβE hβ hN

theorem spCoreReadE_of_spLeviDataE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K)) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {X : Subgroup C} (h : SpLeviDataE E fp X) :
    SpCoreReadE E fp X := by
  obtain ⟨N₁, N₂, N₃, hN₁, hN₂, hN₃, h123, hq', hs, r, hr, ⟨e⟩, hinv⟩ := h
  refine ⟨⟨⟨r, hr⟩, N₁, hN₁, ⟨e⟩, hinv⟩, fun r' => ?_⟩
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq r'.2
  exact readsThroughE_of_three E fp (exists_mul_ne_statedProj_statedSp hq r'.2) N₁ N₂ N₃ h123 hq'
    fun N _ hN => readsThroughE_section_of_spLeviSectionE E fp hK (hs N hN) r'

omit [Finite K] in
theorem fieldRigidInOfE_of_spCoreReadE (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K))
    {X₁ X₂ : Subgroup C} (h₁ : SpCoreReadE E fp X₁) (h₂ : SpCoreReadE E fp X₂) :
    FieldRigidInOfE E fp X₁ X₂ :=
  fieldRigidInOfE_of_coreReadE E fp spRel_unique h₁ h₂

end Core

section Sections

variable {C : Type*} [Group C] [Finite C] (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K))

omit [Finite K] in
theorem spLeviSectionE_of_isEmpty (X : Subgroup C) (N : Subgroup ↥X) [N.Normal]
    (h : ∀ r : ℕ, 1 ≤ r → IsEmpty (↥X ⧸ N ≃* StatedProj (StatedSp r K))) :
    SpLeviSectionE E fp X N :=
  Or.inl h

theorem spLeviSectionE_top (X : Subgroup C) : SpLeviSectionE E fp X ⊤ :=
  Or.inl fun _ hr => isEmpty_quotient_top_mulEquiv X hr

omit [Finite K] in
theorem spLeviSectionE_of_eq {X : Subgroup C} {N N' : Subgroup ↥X} [N.Normal] [N'.Normal]
    (h : N = N') (hs : SpLeviSectionE E fp X N) : SpLeviSectionE E fp X N' := by
  subst h
  exact hs

omit [Finite K] in
theorem spLeviSectionE_of_hom {X : Subgroup C} {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K)
    (hρ : Function.Surjective ρ)
    (htr : ∀ (β : MulAut C) (hβE : β ∈ E) (hβ : ∀ x ∈ X, β x ∈ X),
      (∀ m ∈ ρ.ker, restrictAutOfMapsTo β X hβ m ∈ ρ.ker) → ∀ x : ↥X,
        spMatTrace (ρ (restrictAutOfMapsTo β X hβ x)) = fp ⟨β, hβE⟩ (spMatTrace (ρ x))) :
    SpLeviSectionE E fp X ρ.ker := by
  set ε₀ : ↥X ⧸ ρ.ker ≃* StatedProj (StatedSp r K) :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).trans (spProjEquivCharTwo K r).symm
    with hε₀
  have hmk : ∀ x : ↥X, ε₀ (x : ↥X ⧸ ρ.ker) = (spProjEquivCharTwo K r).symm (ρ x) := fun x => rfl
  refine Or.inr ⟨r, hr, ε₀, fun β hβE hβ hN y => ?_⟩
  obtain ⟨z, rfl⟩ := ε₀.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [quotAutOfMapsTo_mk, hmk, hmk, spTrace_spProjEquivCharTwo_symm,
    spTrace_spProjEquivCharTwo_symm]
  exact htr β hβE hβ hN x

end Sections

section Data

variable {C : Type*} [Group C] [Finite C] (E : Subgroup (MulAut C)) (fp : E →* (K ≃+* K))

theorem spLeviDataE_of_isEmpty_mulEquiv (hq4 : 4 ≤ Nat.card K) {X : Subgroup C}
    (N₁ N₂ N₃ : Subgroup ↥X) [N₁.Normal] [N₂.Normal] [N₃.Normal]
    (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hs : ∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      SpLeviSectionE E fp X N)
    {r : ℕ} (hr : 1 ≤ r) (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K))
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K)))
    (h₃ : IsEmpty (↥X ⧸ N₃ ≃* StatedProj (StatedSp r K))) : SpLeviDataE E fp X := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  have : IsSimpleGroup (↥X ⧸ N₁) := MulEquiv.isSimpleGroup e
  have hnc : ∃ a b : ↥X ⧸ N₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_statedProj_statedSp hq4 hr
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact ⟨N₁, N₂, N₃, inferInstance, inferInstance, inferInstance, h123, hq, hs, r, hr, ⟨e⟩,
    fun β _ hβ => mem_of_isEmpty_mulEquiv N₁ N₂ N₃ h123 hq hnc
      ⟨fun e₂ => h₂.false (e₂.trans e)⟩ ⟨fun e₃ => h₃.false (e₃.trans e)⟩ _⟩

theorem spLeviDataE_two_of_isEmpty_mulEquiv (hq4 : 4 ≤ Nat.card K) {X : Subgroup C}
    (N₁ N₂ : Subgroup ↥X) [N₁.Normal] [N₂.Normal] (h12 : IsPGroup 2 ↥(N₁ ⊓ N₂))
    (hq₁ : ∀ M : Subgroup ↥X, M.Normal → N₁ ≤ M → M = N₁ ∨ M = ⊤)
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₁ : SpLeviSectionE E fp X N₁) (hs₂ : SpLeviSectionE E fp X N₂)
    {r : ℕ} (hr : 1 ≤ r) (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K))
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K))) : SpLeviDataE E fp X := by
  refine spLeviDataE_of_isEmpty_mulEquiv E fp hq4 N₁ N₂ ⊤ (by rwa [inf_top_eq]) ?_ ?_ hr e h₂
    (isEmpty_quotient_top_mulEquiv X hr)
  · intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₂ M hM hle
    · exact Or.inr (top_le_iff.mp hle)
  · intro N _ hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hs₁
    · exact hs₂
    · exact spLeviSectionE_top E fp X

theorem spLeviDataE_one (hq4 : 4 ≤ Nat.card K) {X : Subgroup C} (N₁ : Subgroup ↥X) [N₁.Normal]
    (h1 : IsPGroup 2 ↥N₁) (hs₁ : SpLeviSectionE E fp X N₁) {r : ℕ} (hr : 1 ≤ r)
    (e : ↥X ⧸ N₁ ≃* StatedProj (StatedSp r K)) : SpLeviDataE E fp X := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  have : IsSimpleGroup (↥X ⧸ N₁) := MulEquiv.isSimpleGroup e
  exact spLeviDataE_two_of_isEmpty_mulEquiv E fp hq4 N₁ ⊤ (by rwa [inf_top_eq])
    (eq_or_eq_top_of_simple_quotient (N := N₁))
    (fun M _ hle => Or.inr (top_le_iff.mp hle)) hs₁ (spLeviSectionE_top E fp X) hr e
    (isEmpty_quotient_top_mulEquiv X hr)

end Data

end CFSG.SeitzReduction.OmegaPilot
