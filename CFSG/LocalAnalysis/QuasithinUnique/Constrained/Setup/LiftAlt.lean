module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

section Transport

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem toUnits_sup (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) :
    toUnits (L₀ ⊔ A₀) = toUnits L₀ ⊔ toUnits A₀ := by
  unfold toUnits
  have hr : (unitsEquiv (ZMod 2) W).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (unitsEquiv (ZMod 2) W).surjective
  exact (Subgroup.comap_sup_eq_of_le_range (unitsEquiv (ZMod 2) W).toMonoidHom (H := L₀) (K := A₀)
    (by rw [hr]; exact le_top) (by rw [hr]; exact le_top)).symm

theorem toUnits_le_iff {L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)} :
    toUnits A₀ ≤ toUnits L₀ ↔ A₀ ≤ L₀ := by
  constructor
  · intro h a ha
    have : (unitsEquiv (ZMod 2) W).symm a ∈ toUnits A₀ := by
      show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm a) ∈ A₀
      rw [MulEquiv.apply_symm_apply]
      exact ha
    have h2 := h this
    have h3 : unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm a) ∈ L₀ := h2
    rwa [MulEquiv.apply_symm_apply] at h3
  · intro h u hu
    exact h hu

@[expose] noncomputable def supEquiv (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) :
    ↥(L₀ ⊔ A₀) ≃* ↥(toUnits L₀ ⊔ toUnits A₀) :=
  (toUnitsEquiv (L₀ ⊔ A₀)).symm.trans (MulEquiv.subgroupCongr (toUnits_sup L₀ A₀))

theorem supEquiv_val (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) (y : ↥(L₀ ⊔ A₀)) :
    ((supEquiv L₀ A₀ y : ↥(toUnits L₀ ⊔ toUnits A₀)) : (Module.End (ZMod 2) W)ˣ) =
      (unitsEquiv (ZMod 2) W).symm (y : W ≃ₗ[ZMod 2] W) := rfl

theorem isPerfect_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : Group.IsPerfect A) :
    Group.IsPerfect B := by
  rw [Group.isPerfect_def, _root_.commutator_def]
  have h1 : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
    rw [← _root_.commutator_def]; exact Group.isPerfect_def.1 h
  calc ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆
      = ⁅(⊤ : Subgroup A).map e.toMonoidHom, (⊤ : Subgroup A).map e.toMonoidHom⁆ := by
        rw [Subgroup.map_top_of_surjective _ e.surjective]
    _ = (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆).map e.toMonoidHom :=
        (Subgroup.map_commutator _ _ _).symm
    _ = ⊤ := by rw [h1, Subgroup.map_top_of_surjective _ e.surjective]

theorem center_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := Subgroup.mem_center_iff.mp (show a ∈ Subgroup.center A from ha)
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨x, rfl⟩ := e.surjective g
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [ha' x]
  · intro hb
    have hb' := Subgroup.mem_center_iff.mp hb
    refine ⟨e.symm b, ?_, by simp⟩
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hb' (e g)

theorem isIrreducible_iff_invariant {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) : ρ.IsIrreducible ↔ Nontrivial V ∧
    ∀ U : Submodule k V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun U hU => ?_⟩
    · by_contra hv
      rw [not_nontrivial_iff_subsingleton] at hv
      exact bot_ne_top (α := Subrepresentation ρ)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    · rcases h.eq_bot_or_eq_top (⟨U, fun g _ hv => hU g _ hv⟩ : Subrepresentation ρ) with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  · rintro ⟨hv, h⟩
    have hnt : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, fun h' => ?_⟩
      obtain ⟨x, y, hxy⟩ := hv
      have h1 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule h'
      have h2 : (⊥ : Submodule k V) = ⊤ := h1
      have h3 : x - y ∈ (⊥ : Submodule k V) := h2 ▸ Submodule.mem_top
      exact hxy (sub_eq_zero.mp ((Submodule.mem_bot k).mp h3))
    refine ⟨fun Z => ?_⟩
    rcases h Z.toSubmodule (fun g u hu => Z.apply_mem_toSubmodule g hu) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

theorem forall_toUnits_iff (A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) (w : W) :
    (∀ a ∈ toUnits A₀, a.val w = w) ↔ ∀ b ∈ A₀, b w = w := by
  constructor
  · intro h b hb
    have hmem : (unitsEquiv (ZMod 2) W).symm b ∈ toUnits A₀ := by
      show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm b) ∈ A₀
      rw [MulEquiv.apply_symm_apply]
      exact hb
    have := h _ hmem
    rwa [← unitsEquiv_apply, MulEquiv.apply_symm_apply] at this
  · intro h a ha
    exact h _ ha

theorem natCard_fixed_toUnits (A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Nat.card {w : W // ∀ a ∈ toUnits A₀, a.val w = w} =
      Nat.card ↥(fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) A₀) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun w => forall_toUnits_iff A₀ w)

theorem map_subgroupOf_toUnits (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W)) {G' : Type*} [Group G']
    (θU : ↥(toUnits L₀) ≃* G') :
    (A₀.subgroupOf L₀).map ((toUnitsEquiv L₀).symm.trans θU).toMonoidHom =
      ((toUnits A₀).subgroupOf (toUnits L₀)).map θU.toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(toUnitsEquiv L₀).symm x, ?_, rfl⟩
    show unitsEquiv (ZMod 2) W ((toUnitsEquiv L₀).symm x).1 ∈ A₀
    have h1 := toUnitsEquiv_apply L₀ ((toUnitsEquiv L₀).symm x)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact hx
  · rintro ⟨l, hl, rfl⟩
    refine ⟨toUnitsEquiv L₀ l, ?_, ?_⟩
    · show ((toUnitsEquiv L₀ l : ↥L₀) : W ≃ₗ[ZMod 2] W) ∈ A₀
      rw [toUnitsEquiv_apply]
      exact hl
    · simp

theorem map_sup_subgroupOf_toUnits (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W))
    (B : Subgroup (W ≃ₗ[ZMod 2] W)) {G' : Type*} [Group G']
    (ψU : ↥(toUnits L₀ ⊔ toUnits A₀) ≃* G') :
    (B.subgroupOf (L₀ ⊔ A₀)).map ((supEquiv L₀ A₀).trans ψU).toMonoidHom =
      ((toUnits B).subgroupOf (toUnits L₀ ⊔ toUnits A₀)).map ψU.toMonoidHom := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨supEquiv L₀ A₀ y, ?_, rfl⟩
    show unitsEquiv (ZMod 2) W ((supEquiv L₀ A₀ y : ↥(toUnits L₀ ⊔ toUnits A₀)) :
      (Module.End (ZMod 2) W)ˣ) ∈ B
    rw [supEquiv_val, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(supEquiv L₀ A₀).symm u, ?_, by simp⟩
    show ((supEquiv L₀ A₀).symm u : W ≃ₗ[ZMod 2] W) ∈ B
    have h1 := supEquiv_val L₀ A₀ ((supEquiv L₀ A₀).symm u)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : unitsEquiv (ZMod 2) W (u : (Module.End (ZMod 2) W)ˣ) ∈ B := hu
    rw [h1, MulEquiv.apply_symm_apply] at h2
    exact h2


theorem central_quotient_SL2_alternatives_GL
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    [Finite W] (L₀ A₀ : Subgroup (W ≃ₗ[ZMod 2] W))
    (hirr : Nontrivial W ∧ ∀ U : Submodule (ZMod 2) W,
      (∀ x ∈ L₀, ∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hLperf : Group.IsPerfect ↥L₀) (α₀ : (↥L₀ ⧸ Subgroup.center ↥L₀) ≃* SL(2, F))
    [CFSG.IsElementaryAbelian 2 ↥A₀] (hA1 : A₀ ≠ ⊥)
    (hAN : A₀ ≤ Subgroup.normalizer (L₀ : Set (W ≃ₗ[ZMod 2] W)))
    (hquad : ∀ a ∈ A₀, ∀ b ∈ A₀, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) A₀) :
    Subgroup.center ↥L₀ = ⊥ ∧
      ∃ θ : ↥L₀ ≃* SL(2, F), (∀ x : ↥L₀, θ x = α₀ (QuotientGroup.mk x)) ∧
        (NaturalAlt L₀ A₀ θ ∨ DeletedAlt n L₀ A₀ θ) ∧
        weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) A₀ = Nat.card W := by
  classical
  have hcenmap := center_map_equiv (toUnitsEquiv L₀)
  let αU : (↥(toUnits L₀) ⧸ Subgroup.center ↥(toUnits L₀)) ≃* SL(2, F) :=
    (QuotientGroup.congr (Subgroup.center ↥(toUnits L₀)) (Subgroup.center ↥L₀)
      (toUnitsEquiv L₀) hcenmap).trans α₀
  have : CFSG.IsElementaryAbelian 2 ↥(toUnits A₀) :=
    isElementaryAbelian_of_equiv (toUnitsEquiv A₀) inferInstance
  have hirrU : (repOfSubgroup (toUnits L₀)).IsIrreducible := by
    rw [isIrreducible_iff_invariant]
    refine ⟨hirr.1, fun U hU => hirr.2 U (fun x hx u hu => ?_)⟩
    have hmem : (unitsEquiv (ZMod 2) W).symm x ∈ toUnits L₀ := by
      show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm x) ∈ L₀
      rw [MulEquiv.apply_symm_apply]
      exact hx
    have := hU ⟨_, hmem⟩ u hu
    rwa [repOfSubgroup_apply, ← unitsEquiv_apply, MulEquiv.apply_symm_apply] at this
  have hLperfU : Group.IsPerfect ↥(toUnits L₀) := isPerfect_of_equiv (toUnitsEquiv L₀).symm hLperf
  have hA1U : toUnits A₀ ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have hmem : (unitsEquiv (ZMod 2) W).symm a ∈ toUnits A₀ := by
      show unitsEquiv (ZMod 2) W ((unitsEquiv (ZMod 2) W).symm a) ∈ A₀
      rw [MulEquiv.apply_symm_apply]
      exact ha
    rw [h, Subgroup.mem_bot] at hmem
    have : a = 1 := by
      have := congrArg (unitsEquiv (ZMod 2) W) hmem
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    rw [this]
    exact Subgroup.one_mem _
  have hoffU : Nat.card W ≤ Nat.card ↥(toUnits A₀) *
      Nat.card {w : W // ∀ a ∈ toUnits A₀, a.val w = w} := by
    rw [natCard_toUnits, natCard_fixed_toUnits]
    exact hoff
  obtain ⟨hcenU, θU, hθU, halt, hwU⟩ := central_quotient_SL2_quadratic_offender_alternatives hn hF
    (toUnits L₀) hirrU hLperfU αU (toUnits A₀) hA1U (toUnits_normalizer hAN)
    (fun a ha b hb w => hquad _ ha _ hb w) hoffU
  have hcenter : Subgroup.center ↥L₀ = ⊥ := by
    rw [← hcenmap, hcenU, Subgroup.map_bot]
  refine ⟨hcenter, (toUnitsEquiv L₀).symm.trans θU, ?_, ?_, ?_⟩
  · intro x
    show θU ((toUnitsEquiv L₀).symm x) = α₀ (QuotientGroup.mk x)
    rw [hθU]
    show α₀ (QuotientGroup.congr (Subgroup.center ↥(toUnits L₀)) (Subgroup.center ↥L₀)
      (toUnitsEquiv L₀) hcenmap (QuotientGroup.mk ((toUnitsEquiv L₀).symm x))) = _
    have h := QuotientGroup.congr_mk (Subgroup.center ↥(toUnits L₀)) (Subgroup.center ↥L₀)
      (toUnitsEquiv L₀) hcenmap ((toUnitsEquiv L₀).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact congrArg α₀ h
  · rcases halt with ⟨hAL, -, β, hβ, ℓ, hℓ, hAℓ, -, -, -⟩ |
      ⟨hnAL, hn2, -, -, hΩ5, ψ, β, hψ1, hψ2, hψ3, hψ4⟩
    · left
      refine ⟨toUnits_le_iff.1 hAL, β, fun x w => ?_, ℓ, hℓ, fun g => ?_⟩
      · have h := hβ ((toUnitsEquiv L₀).symm x) w
        rw [toUnitsEquiv_symm_val] at h
        exact h
      · rw [map_subgroupOf_toUnits L₀ A₀ θU]
        exact hAℓ g
    · right
      refine ⟨fun h => hnAL (toUnits_le_iff.2 h), hn2, hΩ5, (supEquiv L₀ A₀).trans ψ, β,
        ?_, ?_, ?_, ?_⟩
      · intro x h
        have key : (supEquiv L₀ A₀ ⟨x, h⟩ : ↥(toUnits L₀ ⊔ toUnits A₀)) =
            ⟨((toUnitsEquiv L₀).symm x).1,
              Subgroup.mem_sup_left ((toUnitsEquiv L₀).symm x).2⟩ := Subtype.ext rfl
        show ψ (supEquiv L₀ A₀ ⟨x, h⟩) = _
        rw [key]
        exact hψ1 _ _
      · intro y w
        have h := hψ2 (supEquiv L₀ A₀ y) w
        rw [supEquiv_val, ← unitsEquiv_apply, MulEquiv.apply_symm_apply] at h
        exact h
      · rw [map_sup_subgroupOf_toUnits L₀ A₀ L₀ ψ]
        exact hψ3
      · rw [map_sup_subgroupOf_toUnits L₀ A₀ A₀ ψ]
        exact hψ4
  · unfold CFSG.QuasithinUnique.Setup.Offender.weight
    rw [← natCard_toUnits, ← natCard_fixed_toUnits]
    exact hwU

end Transport

end CFSG.QuasithinUnique.Setup.Lift
