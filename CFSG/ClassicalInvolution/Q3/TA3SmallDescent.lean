module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTools
public import CFSG.ClassicalInvolution.Q3.TL3CentStep

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem fstarCenter_le_center (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) : fstarCenter Y ≤ Subgroup.center Y :=
  hd.center_genFittingFStar_le hc hE2

theorem isPGroup_fstarCenter (hc : TightCls Y R S t) : IsPGroup 2 ↥(fstarCenter Y) :=
  (isPGroup_two_genFittingFitting hc.2.2).to_le (fstarCenter_le_fitting Y)

theorem not_mem_fstarCenter (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) :
    t ∉ fstarCenter Y :=
  fun h => hE2 ⟨fstarCenter Y, inferInstance, isPGroup_fstarCenter hc, h⟩

theorem tightExOrGood_of_quotient (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) (hnt : ∀ y : Y, ∀ n ∈ fstarCenter Y, y * t * y⁻¹ = t * n → n = 1)
    (h : TightEx (Y ⧸ fstarCenter Y) (R.map (QuotientGroup.mk' (fstarCenter Y)))
        (TwistQ.sylowMap (fstarCenter Y) S) (QuotientGroup.mk' (fstarCenter Y) t) ∨
      GoodThreeElement (R.map (QuotientGroup.mk' (fstarCenter Y)))
        (QuotientGroup.mk' (fstarCenter Y) t)) :
    TightEx Y R S t ∨ GoodThreeElement R t := by
  have hNc := fstarCenter_le_center hd hc hE2
  have hN2 := isPGroup_fstarCenter hc
  have htN := not_mem_fstarCenter hc hE2
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  rcases h with (h2 | ⟨hedgeless, hnot3⟩ | ⟨hedgeless, f, hfs, hfk⟩ | h4) | hgood
  · exact absurd (TwistQ.inO2_of hN2 h2) hE2
  · refine Or.inl (Or.inr (Or.inl ⟨?_, fun h3 => hnot3 (TwistQ.acts3_map hd hRN h3)⟩))
    by_contra hne
    exact TwistQ.not_edgeless_map hd hNc hN2 htN hnt hne hedgeless
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, f.comp (QuotientGroup.mk' (fstarCenter Y)),
      hfs.comp (QuotientGroup.mk'_surjective _), ?_⟩)))
    · by_contra hne
      exact TwistQ.not_edgeless_map hd hNc hN2 htN hnt hne hedgeless
    · rw [← MonoidHom.comap_ker]
      exact hfk.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (h4.of_surjective (QuotientGroup.mk' (fstarCenter Y))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hN2)))))
  · exact Or.inr (TwistQ.good_of hd hNc hN2 htN hnt hgood)

end CFSG.ClassicalInvolution.Q3.TA3
