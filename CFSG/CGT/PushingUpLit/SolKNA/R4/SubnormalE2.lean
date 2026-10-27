module

public import CFSG.ClassicalInvolution.Q3.TL4OddKey
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Sec

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.Open CFSG.ClassicalInvolution.Q3

theorem tightInO2_oddQuot_of_subnormal {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsSubnormal H ⊤) {τ : G} (hτ : τ ∈ H)
    (h2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H))) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore G) τ) := by
  obtain ⟨χ, hχinj, hχmk, hχrange⟩ := CFSG.ClassicalInvolution.Q3.TL4.exists_oddQuot_embedding hH
  have hWsub : IsSubnormal χ.range ⊤ := by
    have h1 := hH.map (QuotientGroup.mk' (componentClassificationOddCore G))
    rw [Subgroup.map_top_of_surjective (QuotientGroup.mk' (componentClassificationOddCore G))
      (QuotientGroup.mk'_surjective _)] at h1
    rw [hχrange]
    exact h1
  obtain ⟨P, hPn, hP2, hm⟩ := h2
  have hχτ : χ (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)) =
      QuotientGroup.mk' (componentClassificationOddCore G) τ :=
    hχmk ⟨τ, hτ⟩
  have hzW : QuotientGroup.mk' (componentClassificationOddCore G) τ ∈ χ.range :=
    MonoidHom.mem_range.mpr ⟨_, hχτ⟩
  let f : (↥H ⧸ classicalInvolutionOddCore ↥H) →* χ.range := χ.rangeRestrict
  have hf : Function.Injective f := fun a b hab => hχinj (congrArg Subtype.val hab)
  have hfs : Function.Surjective f := χ.rangeRestrict_surjective
  have hPn' : (P.map f).Normal := hPn.map f hfs
  have hP2' : IsPGroup 2 (P.map f) := hP2.of_equiv (P.equivMapOfInjective f hf)
  have hmem : (⟨QuotientGroup.mk' (componentClassificationOddCore G) τ, hzW⟩ : χ.range) ∈
      P.map f :=
    Subgroup.mem_map.mpr ⟨_, hm, Subtype.ext hχτ⟩
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin.F2.tightInO2_of_subnormal hWsub hzW
    ⟨P.map f, hPn', hP2', hmem⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
