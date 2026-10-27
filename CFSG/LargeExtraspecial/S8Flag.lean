module

public import CFSG.LargeExtraspecial.S8Std
public import CFSG.LargeExtraspecial.S8CorBApply
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem Abar_eq_of_flag (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g) (hn : 4 < S.width)
    (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    {X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hXR : X ≤ RmodN S g t)
    (hsimp : IsSimpleGroup X) (hnab : S5.NonabelianSylowTwo X)
    (hflag : ∀ τ ∈ conjCentM S t, (∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    S.Lbar g ⊓ Nbar S g t = zpowers t := by
  have hW : closure (conjCentM S t) ≤ flagGroup S (Vt S g t) (Wt S g t) :=
    (closure_le _).mpr fun τ hτ => mem_flagGroup_of_fix (hflag τ hτ).1 (hflag τ hτ).2
  have h2 : ∀ τ ∈ conjCentM S t, τ ≠ t → ∃ y ∈ S.Mbar, y * τ * y⁻¹ = τ * t := by
    intro τ hτ hne
    have hfl := hflag τ hτ
    obtain ⟨-, hτt, x, hxM, hxτ⟩ := hτ
    obtain ⟨n, hnN, hnτ⟩ := fusion_claim H C ht ht1 hVQ D.hQ D.hpol D.hE D.hQa D.hsing hfus
      D.hA D.hN D.hh D.hb D.hPab D.hNc D.hNsq D.hgen D.hN0 D.three_le_finrank hxM hxτ hτt hne
      hfl.1 hfl.2
    exact ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hnN), hnτ⟩
  have hle := Nbar_le_zpowers_of_corB hCorB hFacts hCE hIrr H hNo C hn ht ht1 D.isPGroup_Nbar
    hXR hsimp hnab (isPGroup_of_le_flagGroup hW)
    (commutator_commutator_eq_bot_of_le_flagGroup (Vt_le_Wt H ht1) hW) h2
  refine le_antisymm (inf_le_right.trans hle) ?_
  rw [zpowers_le]
  exact ⟨ht, self_mem_Nbar H ht⟩

end CFSG.LargeExtraspecial.S8
