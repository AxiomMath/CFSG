module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.FactsVStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Hex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

theorem mem_aSet_twin_of_omegaStar_of_subset (hΦ : TypeRHyp Φ) {L P : Subgroup Y} (hL : L ∈ Φ)
    (hA : ¬ AEmpty Φ L)
    (h95 : ∀ (J : Subgroup Y) (zL zJ : Y), AViol Φ L J zL zJ →
      omegaOfSet Φ (twinSet Φ J) ⊆ omegaOfSet Φ (twinSet Φ L))
    (hP : P ∈ omegaStarNbr Φ L) (hPn : P ∉ omegaNbr Φ L) :
    ∃ L' ∈ twinSet Φ L, P ∈ aSet Φ L' := by
  have hΦg := hΦ.hyp
  by_contra hcon
  push Not at hcon
  have hPΦ : P ∈ Φ := hP.1
  obtain ⟨J₀, zL, zJ₀, hv⟩ := not_aEmpty_iff.mp hA
  have hLt : L ∈ twinSet Φ L := ⟨hL, zL, hv.hzK, hv.hzK⟩
  have hzne : ∀ M ∈ insert L (aSet Φ L), ∀ w : Y, IsUniqueInvolution M w →
      ¬ IsUniqueInvolution P w := by
    rintro M (rfl | ⟨zM, zJ, hvJ⟩) w hw hwP
    · exact hPn (Q3CL.T3.twin_mem_omegaNbr hΦg hL hPΦ hP.2.1 hw hwP)
    · have hPM : P ≠ M := fun e => hcon L hLt (by rw [e]; exact ⟨zM, zJ, hvJ⟩)
      obtain ⟨L'', hL''t, hPA⟩ := exists_twin_mem_aSet hΦ hL hvJ ⟨hPΦ, w, hw, hwP⟩ hPM
      exact hcon L'' hL''t hPA
  have hstep0 : ∀ M ∈ insert L (aSet Φ L), P ∉ omegaNbr Φ M := by
    rintro M (rfl | ⟨zM, zJ, hvJ⟩) hPM
    · exact hPn hPM
    · have hPt : P ∉ twinSet Φ M := by
        rintro ⟨-, w, hwM, hwP⟩
        exact hzne M (Set.mem_insert_of_mem _ ⟨zM, zJ, hvJ⟩) w hwM hwP
      have h1 := h95 M zM zJ hvJ (mem_omegaOfSet_of_mem_omegaNbr hΦg hvJ.hzJ hPM hPt)
      exact hPn (h1.2 L ⟨hL, zM, hvJ.hzK, hvJ.hzK⟩)
  exact false_of_hexagon hΦ hL hP hv hstep0 hzne

namespace QFam

variable (h : QFam Φ Q)
include h

theorem mem_aSet_twin_of_omegaStar {L P : Subgroup Y} (hL : L ∈ Φ)
    (hP : P ∈ omegaStarNbr Φ L) (hPn : P ∉ omegaNbr Φ L) :
    ∃ L' ∈ twinSet Φ L, P ∈ aSet Φ L' :=
  mem_aSet_twin_of_omegaStar_of_subset h.hyp hL (h.notEmpty L hL)
    (fun _ _ _ hv => (h.omegaOfSet_eq_of_aViol hL hv).ge) hP hPn

theorem mem_omegaNbr_of_omegaStar {L P : Subgroup Y} (hL : L ∈ Φ)
    (hP : P ∈ omegaStarNbr Φ L) (hPA : P ∉ aStar Φ L) : P ∈ omegaNbr Φ L := by
  by_contra hPn
  obtain ⟨L', hL't, zL', zP, hv⟩ := h.mem_aSet_twin_of_omegaStar hL hP hPn
  obtain ⟨hL'Φ, w, hwL, hwL'⟩ := hL't
  have hL'A : L' ∈ aStar Φ L := mem_aStar_of_twin Relation.ReflTransGen.refl hL'Φ hwL hwL'
  exact hPA (hL'A.tail ⟨hv.mem, Or.inl ⟨zL', zP, hv⟩⟩)

end QFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
