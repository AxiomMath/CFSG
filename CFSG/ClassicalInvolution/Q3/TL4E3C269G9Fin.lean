module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9B
public import CFSG.ClassicalInvolution.Q3.TL4E3C269G2A
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.QuasithinUnique

namespace E3C269G9

variable {X : Type} [Group X] [Finite X]

theorem e3C269L2_nine (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hidx : (genFittingFStar X).index ≤ 2) {p f : ℕ} (hL : LieModel (FStarQuot X) .PSL 2 p f)
    (h9 : p ^ f = 9) {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι) {t s : X}
    (hιt : ι (QuaternionGroup.a 2) = t) (htN : t ∈ genFittingFStar X) (hts : t * s = s * t)
    (hst : s ≠ t) (hconj : ∃ g : X, s = g * t * g⁻¹) :
    Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  let _ : Fintype F := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF, h9]
  obtain ⟨e6⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      F hF9
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  subst hιt
  obtain ⟨Θ⟩ := nonempty_mulEquiv_m10_of_quat (genFittingFStar X)
    (CFSG.Adapters.generalized_fitting_self_centralizing X) hidx ((e.trans e6).trans ψ.symm) hι
    htN
  refine E3C269G.sup_centralizer_eq_top_of_equiv Θ ?_
  have ht2 : ι (QuaternionGroup.a 2) * ι (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) by
      decide, map_one]
  have ht1 : ι (QuaternionGroup.a 2) ≠ 1 := fun h => absurd (hι (h.trans (map_one ι).symm))
    (by decide)
  obtain ⟨g, rfl⟩ := hconj
  refine sup_centralizer_m10 (by rw [← map_mul, ht2, map_one])
    (fun h => ht1 (Θ.injective (h.trans (map_one Θ).symm))) (by rw [← map_mul, ← map_mul, hts])
    (fun h => hst (Θ.injective h)) ⟨Θ g, by rw [map_mul, map_mul, map_inv]⟩

end E3C269G9

theorem e3C269L2_proved : E3C269L2 := by
  intro X _ _ hs hidx p f hp hp2 hf hL ι hι t s hιt htN hts hst hconj
  by_cases h9 : p ^ f = 9
  · exact E3C269G9.e3C269L2_nine hs hidx hL h9 hι hιt htN hts hst hconj
  · exact E3C269G2.e3C269L2_large hs hp hp2 hf hL hι hιt htN hst hconj h9

end CFSG.ClassicalInvolution.Q3.TL4
