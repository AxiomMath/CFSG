module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerStruct

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Del

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {F : Type} [Field F] [Fintype F]
  [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]

@[expose] def DelData (n : ℕ) (L A : Subgroup (V ≃ₗ[ZMod 2] V))
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) : Prop :=
  n = 2 ∧ commGL L ⊤ ⊓ fixGL L = ⊥ ∧ ¬ A ≤ L ∧
    ∃ (β : ↥(commGL L ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))
      (ψ : ↥(L ⊔ A) →* Equiv.Perm (ℙ F (Fin 2 → F))),
      (∀ (x : ↥(L ⊔ A)) (u u' : ↥(commGL L ⊤)),
        (u' : V) = (x : V ≃ₗ[ZMod 2] V) (u : V) →
          ((β u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
            SL2Modules.permAct (ψ x)
              ((β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2)) ∧
      (∀ l : ↥L, ψ ⟨l, Subgroup.mem_sup_left l.2⟩ = MulAction.toPerm (thetaL L α l)) ∧
      ((L.subgroupOf (L ⊔ A)).map ψ = alternatingGroup (ℙ F (Fin 2 → F))) ∧
      ((∃ x y, x ≠ y ∧ (A.subgroupOf (L ⊔ A)).map ψ = Subgroup.closure {Equiv.swap x y}) ∨
        (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
          (A.subgroupOf (L ⊔ A)).map ψ = Subgroup.closure {Equiv.swap x y, Equiv.swap z t}))

omit [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem actW_mem_sup {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) (x : ↥(L ⊔ A)) :
    actW L A I hAn hI x ∈ Lbar L A I hAn hI ⊔ Abar L A I hAn hI := by
  have hx : x ∈ (L.subgroupOf (L ⊔ A)) ⊔ (A.subgroupOf (L ⊔ A)) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    trivial
  have h1 := Subgroup.mem_map_of_mem (actW L A I hAn hI) hx
  rw [Subgroup.map_sup] at h1
  have hLle : (L.subgroupOf (L ⊔ A)).map (actW L A I hAn hI) ≤ Lbar L A I hAn hI := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, hy⟩, rfl⟩
  have hAle : (A.subgroupOf (L ⊔ A)).map (actW L A I hAn hI) ≤ Abar L A I hAn hI := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, hy⟩, rfl⟩
  exact (sup_le_sup hLle hAle) h1

omit [Fintype F] in
theorem delData_of_deleted {n : ℕ} {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (hIdef : I = commGL L ⊤) (hZ : I ⊓ fixGL L = ⊥)
    (θ : ↥(Lbar L A I hAn hI) ≃* SL(2, F))
    (hθ : ∀ l : ↥L, θ ⟨actOn L A I hAn hI L le_sup_left l, ⟨l, rfl⟩⟩ = α (QuotientGroup.mk l))
    (hdel : DeletedAlt n (Lbar L A I hAn hI) (Abar L A I hAn hI) θ) : DelData n L A α := by
  classical
  obtain ⟨hnle, hn2, -, ψ', β', hψθ, hβψ, hψL, hψA⟩ := hdel
  have hnA : ¬ A ≤ L := by
    intro hAL
    apply hnle
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a.1, hAL a.2⟩, rfl⟩
  have hbot : fixIn L I = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 : (w : V) ∈ I ⊓ fixGL L := ⟨w.2, hw⟩
    rw [hZ] at h1
    exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 h1))
  let ι : ↥(L ⊔ A) →* ↥(Lbar L A I hAn hI ⊔ Abar L A I hAn hI) :=
    (actW L A I hAn hI).codRestrict _ (actW_mem_sup hAn hI)
  let ψ : ↥(L ⊔ A) →* Equiv.Perm (ℙ F (Fin 2 → F)) := ψ'.toMonoidHom.comp ι
  have hLmap : (L.subgroupOf (L ⊔ A)).map ι =
      (Lbar L A I hAn hI).subgroupOf (Lbar L A I hAn hI ⊔ Abar L A I hAn hI) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · intro hy
      obtain ⟨l, hl⟩ := hy
      refine ⟨⟨l.1, Subgroup.mem_sup_left l.2⟩, l.2, ?_⟩
      apply Subtype.ext
      exact hl
  have hAmap : (A.subgroupOf (L ⊔ A)).map ι =
      (Abar L A I hAn hI).subgroupOf (Lbar L A I hAn hI ⊔ Abar L A I hAn hI) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · intro hy
      obtain ⟨a, ha⟩ := hy
      refine ⟨⟨a.1, Subgroup.mem_sup_right a.2⟩, a.2, ?_⟩
      apply Subtype.ext
      exact ha
  refine ⟨hn2, hIdef ▸ hZ, hnA, ?_⟩
  subst hIdef
  refine ⟨(Submodule.quotEquivOfEqBot _ hbot).symm.trans β', ψ, ?_, ?_, ?_, ?_⟩
  · intro x u u' hu'
    have e1 : (Submodule.Quotient.mk u' : ↥(commGL L ⊤) ⧸ fixIn L (commGL L ⊤)) =
        actW L A (commGL L ⊤) hAn hI x (Submodule.Quotient.mk u) := by
      rw [actW_mk]
      congr 1
      apply Subtype.ext
      rw [resSub_apply]
      exact hu'
    have e2 : ((Submodule.quotEquivOfEqBot _ hbot).symm u' : _) = Submodule.Quotient.mk u' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    have e3 : ((Submodule.quotEquivOfEqBot _ hbot).symm u : _) = Submodule.Quotient.mk u := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    show ((β' ((Submodule.quotEquivOfEqBot _ hbot).symm u') : _) : ℙ F (Fin 2 → F) → ZMod 2) =
      SL2Modules.permAct (ψ' (ι x)) ((β' ((Submodule.quotEquivOfEqBot _ hbot).symm u) : _) :
        ℙ F (Fin 2 → F) → ZMod 2)
    rw [e2, e3, e1]
    exact hβψ (ι x) (Submodule.Quotient.mk u)
  · intro l
    have := hψθ ⟨actOn L A (commGL L ⊤) hAn hI L le_sup_left l, ⟨l, rfl⟩⟩
      (actW_mem_sup hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩)
    show ψ' (ι ⟨l, Subgroup.mem_sup_left l.2⟩) = _
    rw [thetaL_apply, ← hθ l, ← this]
    rfl
  · have h1 : (L.subgroupOf (L ⊔ A)).map ψ = ((Lbar L A (commGL L ⊤) hAn hI).subgroupOf
        (Lbar L A (commGL L ⊤) hAn hI ⊔ Abar L A (commGL L ⊤) hAn hI)).map ψ'.toMonoidHom := by
      rw [show ψ = ψ'.toMonoidHom.comp ι from rfl, ← Subgroup.map_map, hLmap]
    rw [h1]
    exact hψL
  · have h1 : (A.subgroupOf (L ⊔ A)).map ψ = ((Abar L A (commGL L ⊤) hAn hI).subgroupOf
        (Lbar L A (commGL L ⊤) hAn hI ⊔ Abar L A (commGL L ⊤) hAn hI)).map ψ'.toMonoidHom := by
      rw [show ψ = ψ'.toMonoidHom.comp ι from rfl, ← Subgroup.map_map, hAmap]
    rw [h1]
    exact hψA

end Del

section Dichotomy

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem eq_one_of_centralizes (ctx : FamilyCtx H T n F r Lc) (i : Fin r) {x : V ≃ₗ[ZMod 2] V}
    (hxH : x ∈ H) (h1 : ∀ y ∈ Lc i, x * y = y * x)
    (h2 : ∀ y ∈ (⨆ j, ⨆ (_ : j ≠ i), Lc j), x * y = y * x) : x = 1 := by
  have hxc : ∀ j, Lc j ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) := by
    intro j y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hji : j = i
    · subst hji
      exact (h1 y hy).symm
    · exact (h2 y (Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hji hy))).symm
  have hK : oddGen H ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [ctx.layer.K_eq]
    exact iSup_le hxc
  have : x ∈ H ⊓ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) := by
    refine ⟨hxH, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
  rw [ctx.layer.centralizer_trivial] at this
  exact Subgroup.mem_bot.1 this

theorem alt_dichotomy (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (i : Fin r) (hmove : ⁅Lc i, A⁆ ≠ ⊥) :
    NatData (Lc i) A (ctx.α i) ∨ DelData n (Lc i) A (ctx.α i) := by
  obtain ⟨hd, hd2⟩ := ctx.offd A hA i hmove
  have hI := isInvariant_sup_subgroup hd.inv_L hd.inv_A
  obtain ⟨θ, hθ, hnat | ⟨hdel, hZ⟩⟩ := hd.alternatives
  · left
    have hker : (actOn (Lc i) A (commGL (Lc i) ⊤) hd.A_norm hI (Lc i) le_sup_left).ker = ⊥ := by
      rw [hd.kernel_L, ctx.layer.center_trivial i]
    have hAL : A ≤ Lc i := by
      refine le_of_abar_le_lbar (H := H) (Mo := ⨆ j, ⨆ (_ : j ≠ i), Lc j) hd.A_norm hI hker
        hnat.1 (ctx.hLc.isComp i).1 hA.1 ?_ ?_ fun x hxH h1 h2 => ?_
      · intro y hy l hl
        refine (iSup₂_le (fun j hji => ?_) : (⨆ j, ⨆ (_ : j ≠ i), Lc j) ≤
          Subgroup.centralizer (Lc i : Set (V ≃ₗ[ZMod 2] V)))  hy l hl
        intro z hz
        exact Subgroup.mem_centralizer_iff.2 fun l hl =>
          ctx.hLc.elem_commute (Ne.symm hji) l hl z hz
      · intro y hy a ha
        refine (iSup₂_le (fun j hji => ?_) : (⨆ j, ⨆ (_ : j ≠ i), Lc j) ≤
          Subgroup.centralizer (A : Set (V ≃ₗ[ZMod 2] V)))  hy a ha |>.symm
        intro z hz
        exact Subgroup.mem_centralizer_iff.2 fun a ha =>
          ((hd2 (Lc j) (ctx.hLc.isComp j) (fun h => hji (ctx.hLc.injective h))).2 z hz a ha).symm
      · exact eq_one_of_centralizes ctx i hxH h1 h2
    exact natData_of_natural (ctx.α i) hd.A_norm hI hd.kernel_L (ctx.layer.center_trivial i) hAL rfl θ
      hθ hnat
  · right
    exact delData_of_deleted (ctx.α i) hd.A_norm hI rfl hZ θ hθ hdel

end Dichotomy

end CFSG.QuasithinUnique.Setup.Lift
