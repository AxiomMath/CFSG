module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.RootCentExc

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

theorem isMaxHeight_highRoot : IsMaxHeight τ (highRoot τ) :=
  ⟨isRoot_highRoot τ, fun _ hα => height_le_height_highRoot hα⟩

theorem mem_parabolicWeylGroup_of_smul_highRoot {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ) :
    w ∈ parabolicWeylGroup τ (Jθ τ) :=
  mem_parabolicWeylGroup_of_smul_eq (i₀ := iθ τ) (cθ_ne_zero τ) (iform_highRoot_apply τ) hw

theorem Pθ_le_normalizer_Uθ :
    Pθ τ K ≤ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) := by
  refine sup_le (borelGroup_le_normalizer_rootSubgroup (isMaxHeight_highRoot τ))
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  refine mem_normalizer_of_map_eq ?_
  rw [map_conj_weylElt_rootSubgroup K j (isRoot_highRoot τ),
    reflect_highRoot_of_ne τ j hj]

theorem mem_Pθ_of_conj_le {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hc : conjSub g (Uθ τ K) ≤ Uθ τ K) : g ∈ Pθ τ K := by
  have hθ := isMaxHeight_highRoot τ
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  have hB := borelGroup_le_normalizer_rootSubgroup (K := K) hθ
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1
    (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX τ K (highRoot τ) (1 : K) = 1 := by
      calc pinnedX τ K (highRoot τ) (1 : K)
          = b'⁻¹ * (b' * pinnedX τ K (highRoot τ) 1 * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact one_ne_zero (pinnedX_injective τ K (highRoot τ) (h1.trans (pinnedX_zero τ K _).symm))
  have hmem : (b * canonicalRep (coxeterSystem τ) K w * b') * pinnedX τ K (highRoot τ) 1 *
      (b * canonicalRep (coxeterSystem τ) K w * b')⁻¹ ∈ Uθ τ K :=
    hc ⟨pinnedX τ K (highRoot τ) 1, mem_rootSubgroup.2 ⟨1, rfl⟩, rfl⟩
  obtain ⟨c, hc'⟩ := mem_rootSubgroup.1 hmem
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1
    (mem_rootSubgroup.2 ⟨c, rfl⟩))
  obtain ⟨ε, hε, hn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hθ.1
  have hε0 : ε ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hε
    exact zero_ne_one hε
  have hkey : pinnedX τ K (w • highRoot τ) (ε * d) = pinnedX τ K (highRoot τ) e := by
    rw [← hn, he, hd, hc']
    group
  have hwθ := eq_of_pinnedX_eq hθ.1 (height_highRoot_pos τ) (IsRoot.smul hθ.1 w)
    (mul_ne_zero hε0 hd0) hkey
  have hP := (standard_parabolic_cells τ K).1 (Jθ τ)
  have hmem2 : b * canonicalRep (coxeterSystem τ) K w * b' ∈
      (parabolicSubgroup τ K (Jθ τ) : Set (ModGL τ K)) := by
    rw [hP]
    exact Set.mem_biUnion (mem_parabolicWeylGroup_of_smul_highRoot τ hwθ) hw
  exact hmem2

theorem normalizer_Uθ_le_Pθ {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hn : g ∈ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K))) : g ∈ Pθ τ K := by
  refine mem_Pθ_of_conj_le τ K hg ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hn x).1 hx

theorem centralizer_Uθ_le_Pθ {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hc : ∀ x ∈ Uθ τ K, g * x = x * g) : g ∈ Pθ τ K := by
  refine mem_Pθ_of_conj_le τ K hg ?_
  rintro _ ⟨x, hx, rfl⟩
  have : g * x * g⁻¹ = x := by rw [hc x hx]; group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, this]
  exact hx

theorem Pθ_eq_inf_normalizer :
    Pθ τ K = adjointGroup τ K ⊓ Subgroup.normalizer (Uθ τ K : Set (ModGL τ K)) :=
  le_antisymm (le_inf (parabolicSubgroup_le_adjointGroup τ K _) (Pθ_le_normalizer_Uθ τ K))
    fun _ hg => normalizer_Uθ_le_Pθ τ K hg.1 hg.2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
