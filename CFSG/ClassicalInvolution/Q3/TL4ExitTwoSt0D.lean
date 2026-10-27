module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FOSec
public import CFSG.ClassicalInvolution.Q3.TL4Res2FCore

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem exitShape_of_exitSec (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W)
    (hex : PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz) :
    PhilipHall.Frame.TwinE4 ↥W ∨ ∃ S : Sylow 2 ↥(K.subgroupOf W),
      TightDatum (K.subgroupOf W) S ⟨z, hKW hz.mem⟩ ∧
        TightCls ↥W (K.subgroupOf W) S ⟨z, hKW hz.mem⟩ ∧ ¬ TightInO2 (⟨z, hKW hz.mem⟩ : ↥W) ∧
          ((TightEdgeless (K.subgroupOf W) ∧ ¬ TightActs3 (K.subgroupOf W) ⟨z, hKW hz.mem⟩) ∨
            Nonempty (↥W ⧸ Subgroup.center ↥W ≃* NativeSporadic.Carrier .M12) ∨
            (Subgroup.center ↥W ≠ ⊥ ∧ (LieModel (↥W ⧸ Subgroup.center ↥W) .PSp 3 2 1 ∨
              LieModel (↥W ⧸ Subgroup.center ↥W) .POmegaPlus 4 2 1))) := by
  rcases hex with h4 | ⟨S, hE2, hex⟩
  · exact Or.inl h4
  obtain ⟨h, -⟩ := hc
  have hO : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree h.odd W hWs
  set R : Subgroup ↥W := K.subgroupOf W with hR
  set t : ↥W := ⟨z, hKW hz.mem⟩ with ht
  obtain ⟨hd, hSq⟩ := q8TwinDatum_subgroupOf h hK hz hKW S
  have hKK := tightCore_eq_self_of_twinT4Hyp h hK
  have htc : tightCore R = R := by
    rw [hR, PhilipHall.Frame.tightCore_subgroupOf (hKK.symm ▸ hKW), hKK]
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [htc]
    exact PhilipHall.Frame.hypOmegaGen_conjClass_section h.hyp hK hKW
  have hconj : ∀ g : ↥W, (conjSub g R).map W.subtype = conjSub (g : G) K := by
    intro g
    have hle : conjSub (g : G) K ≤ W := by
      have := conjSub_mono (n := (g : G)) hKW
      rwa [conjSub_eq_self_of_mem g.2] at this
    rw [hR, conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hle
  have hgenW : (⨆ g : ↥W, conjSub g R) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [hconj]
    exact hWg
  have hgen : TightSelfGen R := by
    show (⨆ g : ↥W, conjSub g (tightCore R)) = ⊤
    rw [htc]
    exact hgenW
  have hzK : IsUniqueInvolution (tightCore R) t :=
    PhilipHall.Frame.Q8Datum.isUniqueInvolution_core hd
  have hcls : TightCls ↥W R S t := ⟨hSq, hgen, hO⟩
  by_cases htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R
  · left
    obtain ⟨K', ⟨hK'Ω, u, huK, huK'⟩, hne⟩ := htw
    have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
      CoreAssembly.mem_conjClass_self _
    have hedge : ¬ TightEdgeless R := fun hE =>
      hE _ hK₀ _ hK'Ω (Or.inl (Q3CL.T3.twin_mem_omegaNbr hΩR hK₀ hK'Ω hne huK huK'))
    rcases hex with h' | h' | ⟨he, -⟩ | ⟨Q, _, f, hfs, hf2, -, hQ⟩
    · exact absurd h' hE2
    · exact absurd h'.1 hedge
    · exact absurd he hedge
    · exact ⟨Q, inferInstance, f, hfs, hf2, hQ⟩
  · right
    have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
        {tightCore R} := by
      ext K'
      constructor
      · intro hK'
        by_contra hne
        exact htw ⟨K', hK', hne⟩
      · intro hK'
        rw [Set.mem_singleton_iff] at hK'
        subst hK'
        exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
    have hnormal := (PhilipHall.Frame.twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
      (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
    rw [htc] at hnormal
    have hdt : TightDatum R S t := hd.toTightDatum hnormal
    refine ⟨S, hdt, hcls, hE2, ?_⟩
    rcases TightEx.reduce hdt hcls hex hE2 with h' | ⟨-, h'⟩ | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
