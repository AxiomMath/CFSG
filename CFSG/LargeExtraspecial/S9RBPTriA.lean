module

public import CFSG.LargeExtraspecial.S9RBPData
public import CFSG.LargeExtraspecial.S9RBTriB
public import CFSG.LargeExtraspecial.S9RBTriC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] def fixMod (X : Subgroup S.O) (V : Submodule (ZMod 2) S.Qt) :
    Submodule (ZMod 2) S.Qt where
  carrier := {x | ∀ l ∈ X, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ V}
  add_mem' := fun {x y} hx hy l hl => by
    rw [map_add, show (l : S.Qt ≃ₗ[ZMod 2] S.Qt) x + (l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - (x + y) =
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) by abel]
    exact add_mem (hx l hl) (hy l hl)
  zero_mem' := fun l _ => by rw [map_zero, sub_zero]; exact zero_mem _
  smul_mem' := fun c x hx l hl => by
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ c (hx l hl)

structure TriHyp (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (τ₁ τ₂ : S.O) : Prop where
  data : Step5Data H C ht ht1 hVQ
  hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t
  h₁ : IsConjCent S t τ₁
  h₂ : IsConjCent S t τ₂
  h₃ : IsConjCent S t (t * τ₁ * τ₂)

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem inf₁ : Vt S g t ⊓ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ :=
  T.h₁.inf_eq_bot H C ht ht1 hVQ T.data.transitive T.hR

theorem inf₂ : Vt S g t ⊓ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ :=
  T.h₂.inf_eq_bot H C ht ht1 hVQ T.data.transitive T.hR

theorem fix₁ : ∀ v ∈ Vt S g t, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  T.h₁.fix_Vt H C ht ht1 hVQ T.data.transitive T.hR

theorem fix₂ : ∀ v ∈ Vt S g t, (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  T.h₂.fix_Vt H C ht ht1 hVQ T.data.transitive T.hR

theorem le_Wt₁ : commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t :=
  commSpace_le_Wt_of_fix T.fix₁

theorem comm₁ {r : S.O} (hr : r ∈ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t :=
  T.data.apply_sub_mem_Vt_of_fix (T.h₁.mem_Mbar ht) T.h₁.comm T.fix₁ hr hw

theorem comm₂ {r : S.O} (hr : r ∈ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vt S g t :=
  T.data.apply_sub_mem_Vt_of_fix (T.h₂.mem_Mbar ht) T.h₂.comm T.fix₂ hr hw

theorem transfer {k : S.O} (hk : k ∈ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t)
    (h : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t := by
  obtain ⟨-, -, hf₂, -, -⟩ := T.data.tri_setup T.hR T.h₁ T.h₂ T.h₃
  exact apply_sub_mem_of_transfer (fun w hw => apply_mem_Wt H hk hw) (fun w hw => T.comm₁ hk hw)
    (fun w hw => T.comm₂ hk hw) T.inf₁ (fun w hw => (hf₂ w hw).mp) hw h

theorem sup_eq : Vt S g t ⊔ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
    Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (T.data.tri_setup T.hR T.h₁ T.h₂ T.h₃).1

theorem sub_mem_U₂ (w : S.Qt) : (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
    Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  rw [← T.sup_eq]; exact Submodule.mem_sup_right (sub_mem_commSpace _ _)

theorem U_le_Wt : Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t :=
  sup_le (Vt_le_Wt H ht1) T.le_Wt₁

theorem finrank_U : finrank (ZMod 2) ↥(Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
    finrank (ZMod 2) (Vt S g t) + 4 := by
  have f₁ := T.h₁.finrank_commSpace H C ht ht1 hVQ
  rw [finrank_sup_of_inf_eq_bot T.inf₁, f₁, T.data.finrank_eq]

theorem apply_mem_U {r : S.O} (hr : r ∈ Rbar S g t) {x : S.Qt}
    (hx : x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨v, hv, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨w, hw, rfl⟩ := exists_apply_sub_eq_of_mem T.inf₁ ha
  rw [map_add, map_sub]
  have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v + ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v - ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) +
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by abel
  rw [e]
  exact add_mem (Submodule.mem_sup_left (sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem hr hv)
    (T.comm₁ hr hw))) (Submodule.mem_sup_right (sub_mem_commSpace _ _))

theorem not_mem {w : S.Qt} (hw : w ∈ Wt S g t)
    (h0 : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0) :
    (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∉ Vt S g t ∧
      (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∉ Vt S g t ∧
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∉
        Vt S g t := by
  obtain ⟨-, -, hf₂, hf₃, hD⟩ := T.data.tri_setup T.hR T.h₁ T.h₂ T.h₃
  have i₃ := T.h₃.inf_eq_bot H C ht ht1 hVQ T.data.transitive T.hR
  have hτw : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := fun e => h0 (by rw [e, sub_self])
  refine ⟨fun hv => h0 ?_, fun hv => hτw ?_, fun hv => hτw ?_⟩
  · have : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        Vt S g t ⊓ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv, sub_mem_commSpace _ _⟩
    rwa [T.inf₁, Submodule.mem_bot] at this
  · have : (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        Vt S g t ⊓ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv, sub_mem_commSpace _ _⟩
    rw [T.inf₂, Submodule.mem_bot, sub_eq_zero] at this
    exact (hf₂ w hw).mpr this
  · rw [← hD w hw] at hv
    have : ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        Vt S g t ⊓ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      ⟨hv, sub_mem_commSpace _ _⟩
    rw [i₃, Submodule.mem_bot, sub_eq_zero] at this
    exact (hf₃ w hw).mpr this

theorem plane {X : Subgroup S.O} (hX : X ≤ Rbar S g t) {w : S.Qt} (hw : w ∈ Wt S g t)
    (h0 : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ 0)
    (hfix : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ fixMod S X (Vt S g t)) :
    finrank (ZMod 2) ↥(Vt S g t ⊔ (ZMod 2) ∙ ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ⊔
        (ZMod 2) ∙ ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) = finrank (ZMod 2) (Vt S g t) + 2 ∧
      Vt S g t ⊔ (ZMod 2) ∙ ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ⊔
        (ZMod 2) ∙ ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ≤
        (Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⊓ fixMod S X (Vt S g t) := by
  obtain ⟨n₁, n₂, n₃⟩ := T.not_mem hw h0
  refine ⟨finrank_sup_span_pair n₁ n₂ n₃, sup_le (sup_le ?_ ?_) ?_⟩
  · exact le_inf le_sup_left fun v hv l hl =>
      sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem (hX hl) hv) hv
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, hfix⟩
    exact Submodule.mem_sup_right (sub_mem_commSpace _ _)
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      ⟨T.sub_mem_U₂ w, fun l hl => T.transfer (hX hl) hw (hfix l hl)⟩

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
