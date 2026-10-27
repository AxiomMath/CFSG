module

public import CFSG.LieType.ChevTwo.InversionLinear
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding (IsClassicalTwoOrG2)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)

@[expose] def OuterKleinFour {S : Type} [Group S] (A : Subgroup (MulAut S)) : Prop :=
  IsElemAbelian 2 A ∧ Nat.card A = 4 ∧ A ⊓ inner S = ⊥

@[expose] def InvertsOddElt {S : Type} [Group S] (A : Subgroup (MulAut S)) : Prop :=
  ∃ a ∈ A, a ≠ 1 ∧ ∃ x : S, Odd (orderOf x) ∧ 5 < orderOf x ∧ a x = x⁻¹

@[expose] def IsLinearTwoFamily (S : Type) [Group S] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (N : ℕ), CharP K 2 ∧ 3 ≤ N ∧
    Nonempty (S ≃* LinearFlag.projectiveSL N K)

@[expose] def IsOrthPlusTwoFamily (S : Type) [Group S] : Prop :=
  ∃ n f : ℕ, StatedClassicalModel S .POmegaPlus n 2 f

@[expose] def IsOrthMinusTwoFamily (S : Type) [Group S] : Prop :=
  ∃ n f : ℕ, StatedClassicalModel S .POmegaMinus n 2 f

@[expose] def IsE6TwoFamily (S : Type) [Group S] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid), q.p = 2 ∧
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)

theorem inverts_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {A : Subgroup (MulAut S)} (hA : OuterKleinFour A)
    (h : ∀ A' : Subgroup (MulAut T), OuterKleinFour A' → InvertsOddElt A') :
    InvertsOddElt A := by
  obtain ⟨hAe, hcard, hAI⟩ := hA
  haveI := hAe.1
  set φ : MulAut S ≃* MulAut T := MulAut.congr e with hφ
  have hinj : Function.Injective (φ.toMonoidHom : MulAut S →* MulAut T) := φ.injective
  have hmap : (inner S).map φ.toMonoidHom = inner T := inner_map_congr e
  obtain ⟨a, ⟨a₀, ha₀, rfl⟩, ha1, x, hx1, hx2, hx3⟩ := h (A.map φ.toMonoidHom)
    ⟨⟨inferInstance, by
        rintro _ ⟨y, hy, rfl⟩
        rw [← map_pow, hAe.2 y hy, map_one]⟩,
      by rw [Subgroup.card_map_of_injective hinj, hcard],
      by
        rw [← hmap, ← Subgroup.map_inf _ _ _ hinj, hAI, Subgroup.map_bot]⟩
  refine ⟨a₀, ha₀, fun h1 => ha1 (by rw [h1]; exact map_one _), e.symm x, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hx1
  · rw [MulEquiv.orderOf_eq]; exact hx2
  · have h1 : e (a₀ (e.symm x)) = x⁻¹ := hx3
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply, map_inv] at h2
    exact h2

theorem linear_family_inverts {S : Type} [Group S] (hlin : IsLinearTwoFamily S)
    {A : Subgroup (MulAut S)} (hA : OuterKleinFour A) : InvertsOddElt A := by
  obtain ⟨K, _, hfin, N, hchar, hN, ⟨e⟩⟩ := hlin
  haveI := hchar
  exact inverts_of_mulEquiv e hA fun A' hA' =>
    linear_klein_inverts (K := K) hN A' hA'.1 hA'.2.1 hA'.2.2

@[expose] def OrthPlusInverts : Prop :=
  ∀ (S : Type) [Group S], IsOrthPlusTwoFamily S → ∀ A : Subgroup (MulAut S), OuterKleinFour A →
    InvertsOddElt A

@[expose] def OrthMinusInverts : Prop :=
  ∀ (S : Type) [Group S], IsOrthMinusTwoFamily S → ∀ A : Subgroup (MulAut S), OuterKleinFour A →
    InvertsOddElt A

@[expose] def E6Inverts : Prop :=
  ∀ (S : Type) [Group S], IsE6TwoFamily S → ∀ A : Subgroup (MulAut S), OuterKleinFour A →
    InvertsOddElt A

end CFSG.LieType.ChevTwo
