module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect4

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

structure PerfectSection (H A : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V) : Prop where
  A_norm : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V))
  H_perf : ⁅H, A⁆ = H
  inv_H : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H I
  inv_A : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I
  comm : commGL H I = I
  irr : IsIrrQuot (MonoidHom.id (V ≃ₗ[k] V)) H I
  inj : ∀ x : ↥(H ⊔ A),
    actW H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) x = 1 →
      resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I (isInvariant_sup_subgroup inv_H inv_A) x = 1
  Hbar_ne : (actOn H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) H le_sup_left).range ≠ ⊥
  Abar_ne : (actOn H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) A le_sup_right).range ≠ ⊥
  Abar_elem : CFSG.IsElementaryAbelian 2
    ↥(actOn H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) A le_sup_right).range
  Abar_off : Nat.card (↥I ⧸ fixIn H I) ≤ weight (MonoidHom.id ((↥I ⧸ fixIn H I) ≃ₗ[k] _))
    (actOn H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) A le_sup_right).range
  Abar_quad : QuadAct (MonoidHom.id ((↥I ⧸ fixIn H I) ≃ₗ[k] _))
    (actOn H A I A_norm (isInvariant_sup_subgroup inv_H inv_A) A le_sup_right).range

variable [CharP k 2] [Finite V]

theorem perfect_section {H A : Subgroup (V ≃ₗ[k] V)}
    (hAn : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hHA : ⁅H, A⁆ = H) (hperf : Group.IsPerfect ↥H)
    (hno : NoPQuotient 2 ↥H) (hch : CentralPChief 2 ↥H)
    (hHne : ¬ (⊤ : Submodule k V) ≤ fixGL H)
    (hquad : QuadAct (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hmax : ∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A) :
    ∃ I : Submodule k V, PerfectSection H A I := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨I, hgood⟩ := exists_good_perfect (MonoidHom.id (V ≃ₗ[k] V)) H hperf hHne
  have hinvA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I := fun a ha u hu =>
    bestOffender_invariance (MonoidHom.id (V ≃ₗ[k] V)) H A hAn hAel hHA hno hch hmax ha
      (fun b hb v => hquad a ha b hb v) hgood.inv hgood.comm hgood.irr u hu
  have hHA' : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I :=
    isInvariant_sup_subgroup hgood.inv hinvA
  have hX : H ⊔ A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)) :=
    sup_le Subgroup.le_normalizer hAn
  have hinj : ∀ x : ↥(H ⊔ A), actW H A I hAn hHA' x = 1 →
      resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I hHA' x = 1 := by
    intro x hx
    have key := detect_of_trivial_mod (MonoidHom.id (V ≃ₗ[k] V)) H (H ⊔ A) hX hno hch I
      hgood.inv hHA' hgood.comm x.2 (disp_mem_fix_of_actW_eq_one hAn hHA' hx)
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [resSub_apply]
    exact key w w.2
  have hHbar_ne : (actOn H A I hAn hHA' H le_sup_left).range ≠ ⊥ := by
    intro h
    have h1 : actOn H A I hAn hHA' H le_sup_left = 1 := MonoidHom.range_eq_bot_iff.1 h
    apply hgood.irr.1
    calc I = commSub (MonoidHom.id (V ≃ₗ[k] V)) H I := hgood.comm.symm
      _ ≤ fixSub (MonoidHom.id (V ≃ₗ[k] V)) H := by
        rw [commSub_le_iff]
        intro l hl u hu
        have h2 : actW H A I hAn hHA' ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by
          have := congrArg (fun φ => φ ⟨l, hl⟩) h1
          exact this
        exact disp_mem_fix_of_actW_eq_one hAn hHA' h2 u hu
  have hAbar_ne : (actOn H A I hAn hHA' A le_sup_right).range ≠ ⊥ := by
    intro h
    have h1 : actOn H A I hAn hHA' A le_sup_right = 1 := MonoidHom.range_eq_bot_iff.1 h
    apply hHbar_ne
    rw [MonoidHom.range_eq_bot_iff]
    have hHle' : ⁅H, A⁆ ≤ (actW H A I hAn hHA').ker.map (H ⊔ A).subtype := by
      refine Subgroup.commutator_le.2 fun l hl a ha => ?_
      have h2 : actW H A I hAn hHA' ⟨a, Subgroup.mem_sup_right ha⟩ = 1 := by
        have := congrArg (fun φ => φ ⟨a, ha⟩) h1
        exact this
      have hmem : ⁅(⟨l, Subgroup.mem_sup_left hl⟩ : ↥(H ⊔ A)), ⟨a, Subgroup.mem_sup_right ha⟩⁆ ∈
          (actW H A I hAn hHA').ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, h2, commutatorElement_one_right]
      exact ⟨_, hmem, rfl⟩
    have hHle : H ≤ (actW H A I hAn hHA').ker.map (H ⊔ A).subtype :=
      (le_of_eq hHA.symm).trans hHle'
    refine MonoidHom.ext fun ⟨l, hl⟩ => ?_
    obtain ⟨y, hy, hyl⟩ := hHle hl
    have : y = ⟨l, Subgroup.mem_sup_left hl⟩ := Subtype.ext hyl
    rw [this] at hy
    exact MonoidHom.mem_ker.1 hy
  have hAbar_elem : CFSG.IsElementaryAbelian 2
      ↥(actOn H A I hAn hHA' A le_sup_right).range := isElementaryAbelian_range _ hAel
  have hAbar_quad : QuadAct (MonoidHom.id ((↥I ⧸ fixIn H I) ≃ₗ[k] _))
      (actOn H A I hAn hHA' A le_sup_right).range := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    show actOn H A I hAn hHA' A le_sup_right a'
        (actOn H A I hAn hHA' A le_sup_right a (Submodule.Quotient.mk u) - Submodule.Quotient.mk u) =
      actOn H A I hAn hHA' A le_sup_right a (Submodule.Quotient.mk u) - Submodule.Quotient.mk u
    have hq : resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a'
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u - u) =
        resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u - u := by
      apply Subtype.ext
      rw [resSub_apply, Submodule.coe_sub, resSub_apply]
      exact hquad a a.2 a' a'.2 (u : V)
    have hq' := congrArg (Submodule.Quotient.mk (p := fixIn H I)) hq
    rw [map_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub] at hq'
    rw [map_sub, actOn_A_mk hAn hgood.inv hinvA a u, actOn_A_mk hAn hgood.inv hinvA a' u,
      actOn_A_mk hAn hgood.inv hinvA a' _]
    exact hq'
  have hAbar_off : Nat.card (↥I ⧸ fixIn H I) ≤
      weight (MonoidHom.id ((↥I ⧸ fixIn H I) ≃ₗ[k] _))
        (actOn H A I hAn hHA' A le_sup_right).range := by
    let AI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA).range
    have h1 : Nat.card ↥I ≤ weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) AI :=
      natCard_le_weight_res (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA hmax
    let ρ' : ↥AI →* (↥I ≃ₗ[k] ↥I) := (MonoidHom.id (↥I ≃ₗ[k] ↥I)).comp AI.subtype
    have hρ'w : weight ρ' ⊤ = weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) AI := by
      show weight ((MonoidHom.id (↥I ≃ₗ[k] ↥I)).comp AI.subtype) ⊤ = _
      rw [weight_comp_subtype, map_subtype_top]
    have hZ' : ∀ x : ↥AI, ∀ z ∈ fixIn H I, ρ' x z ∈ fixIn H I := by
      rintro ⟨_, a, rfl⟩ z hz
      exact fixIn_invariant hAn hinvA a z hz
    have h2 := natCard_quotient_le_weight ρ' (fixIn H I) hZ' (by rw [hρ'w]; exact h1)
    let π := quotHom ρ' (fixIn H I) hZ'
    let s : ↥A →* ↥AI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA).rangeRestrict
    have hs : Function.Surjective s := MonoidHom.rangeRestrict_surjective _
    have hcomp : π.comp s = actOn H A I hAn hHA' A le_sup_right := by
      refine MonoidHom.ext fun a => LinearEquiv.ext fun w => ?_
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      rw [MonoidHom.comp_apply, quotHom_mk, actOn_A_mk hAn hgood.inv hinvA a u]
      rfl
    have hπinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro y hy
      obtain ⟨a, rfl⟩ := hs y
      have h3 : actW H A I hAn hHA' ⟨a, Subgroup.mem_sup_right a.2⟩ = 1 := by
        have h4 : (π.comp s) a = 1 := hy
        rw [hcomp] at h4
        exact h4
      have h5 := hinj _ h3
      rw [resSub_sup_A hgood.inv hinvA] at h5
      exact Subtype.ext h5
    have hrange : π.range = (actOn H A I hAn hHA' A le_sup_right).range := by
      rw [← hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs]
      exact MonoidHom.range_eq_map π
    calc Nat.card (↥I ⧸ fixIn H I) ≤ weight π ⊤ := h2
      _ = weight (MonoidHom.id ((↥I ⧸ fixIn H I) ≃ₗ[k] _)) π.range :=
        (weight_range_of_injective π hπinj).symm
      _ = _ := by rw [hrange]
  exact ⟨I,
    { A_norm := hAn
      H_perf := hHA
      inv_H := hgood.inv
      inv_A := hinvA
      comm := hgood.comm
      irr := hgood.irr
      inj := hinj
      Hbar_ne := hHbar_ne
      Abar_ne := hAbar_ne
      Abar_elem := hAbar_elem
      Abar_off := hAbar_off
      Abar_quad := hAbar_quad }⟩

end CFSG.QuasithinUnique.Setup.Layer
