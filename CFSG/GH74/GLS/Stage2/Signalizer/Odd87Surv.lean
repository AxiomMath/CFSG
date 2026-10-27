module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)

@[expose] def GenericKill (Y : Type) [Group Y] (α : MulAut Y) : Prop :=
  (∃ Q : Subgroup Y, Group.IsPerfect ↥Q ∧ (∀ s ∈ Q, α s = s) ∧
      ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T) (c : ↥Q →* T),
        Function.Surjective c ∧ ¬ Group.IsSolvable T ∧ ∀ k : Kind, ¬ KindFactor k T) ∨
    ((∀ s : Y, α ≠ MulAut.conj s) ∧ ∃ E : Subgroup Y, (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) ∧
      (∀ e ∈ E, e * e = 1) ∧ 2 ^ 4 ≤ Nat.card ↥E ∧ ∀ e ∈ E, α e = e)

@[expose] def Cell87Surv (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  Prop4_1a → Prop4_1b →
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (p : ℕ)
      (X : Subgroup (Sec H₀ H₁)), Sig4B G z H₀ H₁ hz p X → Hyp42 (zSec z H₀ hz H₁) X →
      center ↥(layer (Sec H₀ H₁)) = ⊥ →
      F (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) →
      ¬ GenericKill (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁)))
        (onCenterQuotient (layerAut (zSec z H₀ hz H₁))) →
      Concl42 k (zSec z H₀ hz H₁) p X

theorem cell87Simple_of_surv {F : (Y : Type) → [Group Y] → Prop}
    (h : Cell87Surv F) : Cell87Simple F := by
  intro h1 h2 G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hZ hF
  by_cases hGK : GenericKill _ (onCenterQuotient (layerAut (zSec z H₀ hz H₁)))
  · exfalso
    have hd := CellData.of_ctx hctx hsig hyp
    set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
    have hπ : Function.Surjective (QuotientGroup.mk' (center ↥(layer (Sec H₀ H₁)))) :=
      QuotientGroup.mk'_surjective _
    have hker : (QuotientGroup.mk' (center ↥(layer (Sec H₀ H₁)))).ker =
        center ↥(layer (Sec H₀ H₁)) := QuotientGroup.ker_mk' _
    have hcomm : ∀ x, QuotientGroup.mk' (center ↥(layer (Sec H₀ H₁))) (layerAut zb x) =
        onCenterQuotient (layerAut zb) (QuotientGroup.mk' (center ↥(layer (Sec H₀ H₁))) x) :=
      fun x => (onCenterQuotient_apply_mk _ _).symm
    rcases hGK with ⟨Q, hQp, hQ, T, _, hTs, c, hc, hns, hbad⟩ |
      ⟨hnotinn, E, hEc, hE2, hEcard, hEfix⟩
    · have := hQp
      have hCS := centSection_of_fixed_perfect hπ hker.le hcomm Q hQ c hc
      exact hbad k (kindFactor_of_section_sec hctx hsig hns hCS.isSection)
    · have hzK : zb ∉ layer (Sec H₀ H₁) := by
        intro hzbK
        apply hnotinn (QuotientGroup.mk' (center ↥(layer (Sec H₀ H₁))) ⟨zb, hzbK⟩)
        ext s
        obtain ⟨x, rfl⟩ := hπ s
        rw [← hcomm, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [coe_layerAut]
        simp
      exact gen4_kill (gen4_sec hctx.std.gen4 H₀ H₁) hd.z2 hzK hπ hker hcomm E hEc hE2 hEcard hEfix
  · exact h h1 h2 G z k S hctx H₀ H₁ hz p X hsig hyp hZ hF hGK

theorem cell87_of_surv (hInv : InvSec) {F : (Y : Type) → [Group Y] → Prop}
    (hbad : ∀ (k : Kind) (Y : Type) [Group Y], F Y → ¬ KindFactorAll k Y)
    (h : Cell87Surv F) : Cell87 F :=
  cell87_of_simple hInv hbad (cell87Simple_of_surv h)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
