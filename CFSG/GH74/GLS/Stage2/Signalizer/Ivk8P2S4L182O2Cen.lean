module

public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182O2

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

theorem le_of_centralizes_component {L₁ L₂ T : Subgroup Y} (hK₁ : IsComponent L₁)
    (hTn : T.Normal) (hTp : IsPGroup 2 ↥T) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ : Nat.card ↥(center ↥L₁) = 2) (hI : Nat.card ↥(L₁ ⊓ L₂) = 2) (hT : T ≤ L₁ ⊔ L₂) :
    T ≤ L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : L₁ ≤ centralizer (T : Set Y) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_le_centralizer_of_isPGroup hK₁ hTn hTp
  intro t ht
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm (hT ht)
  subst hab
  have hca : ∀ c ∈ L₁, c * a = a * c := by
    intro c hc1
    have h1 : (a * b) * c = c * (a * b) := mem_centralizer_iff.1 (hc hc1) _ ht
    have h2 : c * a * b = a * c * b := by
      calc c * a * b = c * (a * b) := by rw [mul_assoc]
        _ = a * b * c := h1.symm
        _ = a * (b * c) := by rw [mul_assoc]
        _ = a * (c * b) := by rw [hcomm c hc1 b hb]
        _ = a * c * b := by rw [mul_assoc]
    exact mul_right_cancel h2
  exact L₂.mul_mem (central_mem_of_card_inf hcomm hZ hI ha hca) hb

theorem le_center_of_quasisimple {T : Subgroup Y} (hq : IsQuasisimple Y) (hTn : T.Normal)
    (hTp : IsPGroup 2 ↥T) : T ≤ center Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : IsComponent (⊤ : Subgroup Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩
  have hc := CFSG.LocalAnalysis.ComponentInitial.isComponent_le_centralizer_of_isPGroup htop hTn
    hTp
  intro t ht
  rw [Subgroup.mem_center_iff]
  intro g
  exact (mem_centralizer_iff.1 (hc (Subgroup.mem_top g)) t ht).symm

end Abstract

section Involutions

variable {Y : Type} [Group Y]

theorem unique_involution_of_card_two {H : Subgroup Y} (hH : Nat.card ↥H = 2) :
    ∀ x ∈ H, ∀ y ∈ H, orderOf x = 2 → orderOf y = 2 → x = y := by
  intro x hx y hy hxo hyo
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).1 hH
  have hne : ∀ {w : Y} (hw : w ∈ H), orderOf w = 2 → (⟨w, hw⟩ : ↥H) ≠ 1 := by
    intro w hw how h
    have h1 : w = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at how
    exact absurd how (by norm_num)
  exact congrArg Subtype.val ((hu _ (hne hx hxo)).trans (hu _ (hne hy hyo)).symm)

end Involutions

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182O2
