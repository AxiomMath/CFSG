module

public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.Stage1.Thm6.Glue

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B810

theorem hasL2Model_gt_three' {K : Type} [Group K] (h : HasL2Model K Odd) :
    HasL2Model K (fun q => Odd q ∧ 3 < q) := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  refine ⟨p, f, hp, hf, ⟨hq, ?_⟩, hL⟩
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hq
    omega
  all_goals exact absurd h0 (by norm_num)

theorem shape_of_center_ne_bot
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) {X : Type} [Group X] [Finite X]
    (hgen : Gen4 X) {K : Subgroup X} (hcomp : InC2 ↥K ∨ InU2 ↥K) (hcen : center ↥K ≠ ⊥) :
    Shape2M12 ↥K ∨ Shape2Sz8 ↥K := by
  rcases hcomp with hC | hU
  · rcases c2ShapeG_of_inC2 hG hF hC (Gen4.subgroup K hgen) with h | h | h
    · exact absurd h hcen
    · exact Or.inl h
    · exact Or.inr h
  · exfalso
    obtain ⟨hq, hmod⟩ := hU
    rcases hmod with hL2 | hA7 | ⟨hL34, hel, -⟩
    · exact hcen (center_eq_bot_of_isL2Model (isL2Model_of_hasL2Model (hasL2Model_gt_three' hL2)))
    · exact hcen (center_eq_bot_of_isA7Model hA7)
    · have hexp : Monoid.exponent ↥(center ↥K) ≠ 4 := by
        intro h
        have := IsElementaryAbelian.exponent_dvd_p 2 ↥(center ↥K)
        rw [h] at this
        omega
      exact hF.l34_cover ↥K hq (IsElementaryAbelian.isPGroup 2 _) hL34 hcen hexp
        (Gen4.subgroup K hgen)

end CFSG.GH74.GLS.C3.Layer1.Bk.B810
