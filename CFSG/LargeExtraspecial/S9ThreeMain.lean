module

public import CFSG.LargeExtraspecial.S9IIb
public import CFSG.LargeExtraspecial.S9Three
public import CFSG.LargeExtraspecial.S9FourD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

@[expose] def Timmesfeld93Residual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
      (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), SpCase H C ht ht1 hVQ →
      finrank (ZMod 2) (Vt S g t) = 4 → S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) →
      ∀ {h : S.M}, S.ρ h ∈ Rbar S g t → (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
        (∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) →
        ∀ w ∈ Wone S g t g ((h : G) * g),
          ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vone S g t g ((h : G) * g)

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_9_3 (hRes : Timmesfeld93Residual.{u}) (hCorB : S8.TimmesfeldCorBInput)
    (hFacts : S8.CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    ∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  refine false_of_forall_mem_Abar_conj hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hSp hA ?_
  intro x hxM hτt
  by_contra hβ
  push Not at hβ
  exact not_forall_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hcon hxM hτt hβ
    (hRes hCE hIrr H hNo C ht ht1 hVQ hSp h4 hA hcon hh hb x hxM hτt hβ)

theorem false_of_sp_four (hRes : Timmesfeld93Residual.{u}) (hCorB : S8.TimmesfeldCorBInput)
    (hFacts : S8.CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : False := by
  obtain ⟨x, -, hxL, hxN⟩ :=
    timmesfeld_9_3 hRes hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hSp h4 hA
  rcases timmesfeld_9_4_count hCE H hNo C ht ht1 hVQ hSp hA hxL hxN with
    ⟨-, h7⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
  · exact false_of_sp_four_seven hCE H hNo C ht ht1 hVQ hSp h4 h7
  · omega
  · omega

theorem timmesfeld_9_4_sp (hRes : Timmesfeld93Residual.{u}) (hCorB : S8.TimmesfeldCorBInput)
    (hFacts : S8.CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    (finrank (ZMod 2) (Vt S g t) = 6 ∧ S.width = 11 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
      (finrank (ZMod 2) (Vt S g t) = 8 ∧ S.width = 17 ∧
        Nat.card (Nbar S g t) = 2 ^ 17) := by
  by_cases h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)
  · exact timmesfeld_9_4_of_six hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hSp hA h6
  · have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
    exact (false_of_sp_four hRes hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hSp (by omega)
      hA).elim

end CFSG.LargeExtraspecial.S9
