module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18Alt2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.TL4.SecIdE2 Matrix

section E8

theorem exists_conj_of_e8 {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y} (hE : E8Struct ⊤ E)
    {a b : Y} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ y : Y, y * b * y⁻¹ = a := by
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  have haE : e8Coord e (e8Inv he a) = a := e8Coord_e8Inv he ha
  have hbE : e8Coord e (e8Inv he b) = b := e8Coord_e8Inv he hb
  have ha0 : e8Inv he a ≠ 0 := fun h => ha1 (by rw [← haE, h, e8Coord_zero])
  have hb0 : e8Inv he b ≠ 0 := fun h => hb1 (by rw [← hbE, h, e8Coord_zero])
  obtain ⟨M, hM⟩ := sl3Two_transitive _ _ ha0 hb0
  obtain ⟨y, hy⟩ := e8Hom_surjective hE he M
  refine ⟨(y : Y), ?_⟩
  rw [← hbE, conj_e8Coord_e8Hom hE he y, hy, hM, haE]

theorem e189_e8_alt2 {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) {E : Subgroup Y} (hE : E8Struct ⊤ E)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hzE : z ∈ E := TwinDisc.ExitO2.fam_mem_of_e8 F hE hK hz
  have htE : t ∈ E := TwinDisc.ExitO2.fam_mem_of_e8 F hE hJ ht
  have htz : t ≠ z := by
    rintro rfl
    exact hne (conjSub_eq_self_of_mem hz.mem)
  have hztE : z * t ∈ E := E.mul_mem hzE htE
  have hzt1 : z * t ≠ 1 := by
    intro h
    apply htz
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hz.sq
  obtain ⟨x, hx⟩ := exists_conj_of_e8 hE hztE hzE hzt1 hz.ne_one
  exact alt2_of_fusion F.hyp F.two hK hz hzt hne hx

end E8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
