module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GVertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GRows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3At
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf24Desc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77.T3Core
open scoped commutatorElement


theorem thm3RConclG_oddQuot_of_quotViol {n : ℕ} (hB : Thm3A.Thm3RBelowG n) {Y : Type} [Group Y]
    [Finite Y] (hY : Nat.card Y < n) {Φ : Set (Subgroup Y)} (hΦ : TypeRHyp Φ) {K : Subgroup Y}
    (hK : K ∈ Φ)
    (hnA : ¬ AEmpty (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))) :
    Thm3A.Thm3RConclG (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) := by
  set N := classicalInvolutionOddCore Y with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΦ' : TypeRHyp (oddQuotientFamily Φ) := typeRHyp_oddQuot hΦ hN
  have hK' : K.map (QuotientGroup.mk' N) ∈ oddQuotientFamily Φ := map_mem_quotFamily hK
  have hlt : Nat.card (Y ⧸ N) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N)) hY
  have hO : classicalInvolutionOddCore (Y ⧸ N) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  exact hB (Nat.card (Y ⧸ N)) hlt (Y ⧸ N) rfl hO _ hΦ' _ hK' hnA

section Vertex

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
  {a c : G} {d : Std20Frame K K' J S R R' W V z t}

theorem hyp51At_of_quotViolG_aux (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hd : Frame205Data d a) (hv : Vertex205 d a c) (hB : Thm3A.Thm3RBelowG (Nat.card G))
    {M₀ : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    (hM₀ : M₀ = frameKa K c ∨ M₀ = frameKa K' c)
    (hA : ¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G)))))) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  have hTR := typeRHyp_omegaAFam (std20Frame_typeRHyp d) (Subgroup.centralizer ({c} : Set G))
  have hz2 : (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨z, hv.z_cent⟩ = 1 :=
    Subtype.ext d.viol.hzK.sq
  have hz1' : (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ≠ 1 := fun e =>
    d.viol.hzK.ne_one (congrArg Subtype.val e)
  have hMmem : M₀ ∈ omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) := by
    rcases hM₀ with rfl | rfl
    · exact frameKa_mem_omegaAFam_of_vertex hv
    · exact frameKa'_mem_omegaAFam_of_vertex hv
  have hzM : (⟨z, hv.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ M₀ := by
    rcases hM₀ with rfl | rfl
    · exact z_mem_frameKa_of_vertex hv
    · exact z_mem_frameKa'_of_vertex hv
  have hconcl := thm3RConclG_oddQuot_of_quotViol hB hv.card_lt hTR hMmem hA
  obtain ⟨hUq, hAOq⟩ :=
    hyp51_of_thm3BarG hU hM12 hM12fin hM12nab hG2 hTR hMmem hconcl hzM hz2 hz1'
  obtain ⟨hK₁, hK₂⟩ := frameKa_map_mem_aStar hv hM₀
  have hMT := le_omegaGen (self_mem_aStar (Ω := oddQuotientFamily (omegaAFam
    (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G))))
    (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G))))))
  exact hyp51At_of_moved_vertexG hd hv (hMT (Subgroup.mem_map_of_mem _ hzM))
    (oddQuotMk_t_mem hv (le_omegaGen hK₁) (le_omegaGen hK₂)) hUq hAOq

theorem hyp51At_of_quotViolG (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hd : Frame205Data d a) (hv : Vertex205 d a c) (hB : Thm3A.Thm3RBelowG (Nat.card G))
    (hA : (¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G)))))) ∨
      (¬ AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
            ↥(Subgroup.centralizer ({c} : Set G))))))) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c :=
  hA.elim
    (fun h => hyp51At_of_quotViolG_aux hU hM12 hM12fin hM12nab hG2 hd hv hB (Or.inl rfl) h)
    (fun h => hyp51At_of_quotViolG_aux hU hM12 hM12fin hM12nab hG2 hd hv hB (Or.inr rfl) h)

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
