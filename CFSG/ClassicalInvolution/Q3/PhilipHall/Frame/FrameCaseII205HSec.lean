module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Q3.OddCentralizerFree
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3 CFSG.Open

theorem exists_sectionQuot_hom {C : Type} [Group C] [Finite C] (P : Subgroup C) :
    ∃ F : ↥(P.map (QuotientGroup.mk' (componentClassificationOddCore C))) →*
        (↥P ⧸ classicalInvolutionOddCore ↥P),
      Function.Surjective F ∧ Odd (Nat.card F.ker) ∧
        ∀ x : ↥P, ∀ hx : QuotientGroup.mk' (componentClassificationOddCore C) (x : C) ∈
          P.map (QuotientGroup.mk' (componentClassificationOddCore C)),
          F ⟨QuotientGroup.mk' (componentClassificationOddCore C) (x : C), hx⟩ =
            QuotientGroup.mk' (classicalInvolutionOddCore ↥P) x := by
  set N := componentClassificationOddCore C with hN
  set T := P.map (QuotientGroup.mk' N) with hT
  let gP : ↥P →* ↥T :=
    ((QuotientGroup.mk' N).comp P.subtype).codRestrict T
      (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hgP : Function.Surjective gP := by
    intro t
    obtain ⟨c, hc, hct⟩ := t.2
    exact ⟨⟨c, hc⟩, Subtype.ext hct⟩
  let πP : ↥P →* (↥P ⧸ classicalInvolutionOddCore ↥P) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥P)
  have hNP : (N.subgroupOf P) ≤ classicalInvolutionOddCore ↥P := by
    have hnorm : (N.subgroupOf P).Normal := inferInstance
    have hcard : Odd (Nat.card (N.subgroupOf P)) := by
      have hinj : Function.Injective (N.subgroupOf P).subtype := Subtype.val_injective
      have h1 : Nat.card (N.subgroupOf P) = Nat.card ((N.subgroupOf P).map P.subtype) := by
        rw [Subgroup.card_map_of_injective P.subtype_injective]
      rw [h1, Subgroup.subgroupOf_map_subtype]
      exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card C)
        (Subgroup.card_dvd_of_le inf_le_left)
    exact CFSG.ComponentClassification.OddCore.maximal ↥P (N.subgroupOf P) hnorm hcard
  have hle : gP.ker ≤ πP.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : QuotientGroup.mk' N (x : C) = 1 := by
      have := congrArg Subtype.val hx
      simpa [gP] using this
    have hxN : (x : C) ∈ N := (QuotientGroup.eq_one_iff (x : C)).mp hx'
    have hxO : x ∈ classicalInvolutionOddCore ↥P :=
      hNP (show x ∈ N.subgroupOf P from (Subgroup.mem_subgroupOf).mpr hxN)
    exact (QuotientGroup.eq_one_iff x).mpr hxO
  let e : (↥P ⧸ gP.ker) ≃* ↥T := QuotientGroup.quotientKerEquivOfSurjective gP hgP
  let F : ↥T →* (↥P ⧸ classicalInvolutionOddCore ↥P) :=
    (QuotientGroup.lift gP.ker πP hle).comp e.symm.toMonoidHom
  have hF : ∀ x : ↥P, F (gP x) = πP x := by
    intro x
    have hmk : e (QuotientGroup.mk x) = gP x := rfl
    simp only [F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← hmk, MulEquiv.symm_apply_apply]
    rfl
  have hFsurj : Function.Surjective F := by
    intro s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨gP x, hF x⟩
  have hker : F.ker ≤ (classicalInvolutionOddCore ↥P).map gP := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    obtain ⟨x, rfl⟩ := hgP t
    rw [hF x] at ht
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp ht, rfl⟩
  have hodd : Odd (Nat.card F.ker) := by
    have h1 : Nat.card F.ker ∣ Nat.card ((classicalInvolutionOddCore ↥P).map gP) :=
      Subgroup.card_dvd_of_le hker
    have h2 : Nat.card ((classicalInvolutionOddCore ↥P).map gP) ∣
        Nat.card (classicalInvolutionOddCore ↥P) := Subgroup.card_map_dvd _ _
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥P)
      (h1.trans h2)
  refine ⟨F, hFsurj, hodd, ?_⟩
  intro x hx
  have hx' : (⟨QuotientGroup.mk' N (x : C), hx⟩ : ↥T) = gP x := rfl
  rw [hx', hF x]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
