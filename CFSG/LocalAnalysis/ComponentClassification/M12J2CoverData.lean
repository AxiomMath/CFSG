module

public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverIndex

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup CFSG.Assembly

@[expose] def CoverSetting (s : TauCeti.SporadicName) (H : Type) [Group H] (L : Subgroup H)
    (t : H) : Prop :=
  L.Normal ∧ Assembly.IsQuasisimple L ∧ orderOf t = 2 ∧ (center L).map L.subtype = zpowers t ∧
    Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s ∧
    centralizer (L : Set H) = zpowers t ∧ L.index ≤ 2

@[expose] def InternalSylowData (s : TauCeti.SporadicName) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) (t : H), CoverSetting s H L t →
    ∃ T : Sylow 2 H,
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ center (T : Subgroup H), (z : H) = k⁻¹ * u * k

@[expose] def ExternalInvolutionData (s : TauCeti.SporadicName) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H) (t : H), CoverSetting s H L t →
    (∀ x y : H, x ∉ L → orderOf x = 2 → y ∉ L → orderOf y = 2 → ∃ h : H, h⁻¹ * x * h = y) ∧
    ∀ p : H, p ∉ L → orderOf p = 2 → ∃ A : Subgroup H, A ≤ L ∧
      zpowers t ⊔ A = L ⊓ centralizer ({p} : Set H) ∧ zpowers t ⊓ A = ⊥ ∧
      (∀ a ∈ A, a * t = t * a) ∧ _root_.commutator A = ⊤ ∧ Even (Nat.card A) ∧
      ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer A)

@[expose] def LocalKernel (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
    (∀ x : G, orderOf x = 2 → Assembly.oddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    ∀ t : G, orderOf t = 2 → (center L).map L.subtype = zpowers t →
    Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t

theorem m12J2LocalKernel_of (hM : LocalKernel .M12) (hJ : LocalKernel .J2) :
    M12J2LocalKernel := by
  intro G _ _ _ hnonab hK L hL hcore S hS t ht hZ hQ
  rcases hQ with h | h
  · exact hM G hnonab hK L hL hcore S hS t ht hZ h
  · exact hJ G hnonab hK L hL hcore S hS t ht hZ h

theorem m12J2LocalInvolutionData_of
    (hJ2 : Nat.card (MulAut Blueprint.NativeSporadic.J2) ≤
      2 * Nat.card Blueprint.NativeSporadic.J2)
    (hIM : InternalSylowData .M12) (hIJ : InternalSylowData .J2)
    (hEM : ExternalInvolutionData .M12) (hEJ : ExternalInvolutionData .J2) :
    M12J2LocalInvolutionData := by
  intro H _ _ L t hLn hLq ht hZ hQ hCL
  have hCL' : centralizer (L : Set H) = (center L).map L.subtype := hCL.trans hZ.symm
  have hidx : L.index ≤ 2 :=
    (CentralCover.quasisimple_faithful_overgroup_index_le_two hJ2 hLq hQ hCL').2
  refine ⟨hidx, ?_⟩
  rcases hQ with h | h
  · obtain ⟨T, hT⟩ := hIM H L t ⟨hLn, hLq, ht, hZ, h, hCL, hidx⟩
    exact ⟨⟨T, hT⟩, hEM H L t ⟨hLn, hLq, ht, hZ, h, hCL, hidx⟩⟩
  · obtain ⟨T, hT⟩ := hIJ H L t ⟨hLn, hLq, ht, hZ, h, hCL, hidx⟩
    exact ⟨⟨T, hT⟩, hEJ H L t ⟨hLn, hLq, ht, hZ, h, hCL, hidx⟩⟩

theorem m12J2LocalInvolutionData_of_data (hIM : InternalSylowData .M12)
    (hIJ : InternalSylowData .J2) (hEM : ExternalInvolutionData .M12)
    (hEJ : ExternalInvolutionData .J2) : M12J2LocalInvolutionData :=
  m12J2LocalInvolutionData_of J2Cover.j2_mulAut_card.le hIM hIJ hEM hEJ

end CFSG.ComponentClassification.StandardRecognition
