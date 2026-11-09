module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

namespace RD

@[expose] def okE8 (s : ℕ) : Bool := s == 6 || s == 72 || s == 84 || s == 126 || s == 240

private theorem rdE8_all_take_join {α : Type*} {f : α → Bool} {L : List α} {a b c : ℕ}
    (h₁ : ((L.drop a).take b).all f = true) (h₂ : ((L.drop (a + b)).take c).all f = true) :
    ((L.drop a).take (b + c)).all f = true := by
  rw [List.take_add, List.all_append, h₁, List.drop_drop, h₂, Bool.and_self]

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p0 :
    (((allVecs Tag.E8.rank).drop 0).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p1 :
    (((allVecs Tag.E8.rank).drop 205).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p2 :
    (((allVecs Tag.E8.rank).drop 410).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p3 :
    (((allVecs Tag.E8.rank).drop 615).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p4 :
    (((allVecs Tag.E8.rank).drop 820).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p5 :
    (((allVecs Tag.E8.rank).drop 1025).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p6 :
    (((allVecs Tag.E8.rank).drop 1230).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p7 :
    (((allVecs Tag.E8.rank).drop 1435).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p8 :
    (((allVecs Tag.E8.rank).drop 1640).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p9 :
    (((allVecs Tag.E8.rank).drop 1845).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p10 :
    (((allVecs Tag.E8.rank).drop 2050).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p11 :
    (((allVecs Tag.E8.rank).drop 2255).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p12 :
    (((allVecs Tag.E8.rank).drop 2460).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p13 :
    (((allVecs Tag.E8.rank).drop 2665).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p14 :
    (((allVecs Tag.E8.rank).drop 2870).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p15 :
    (((allVecs Tag.E8.rank).drop 3075).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p16 :
    (((allVecs Tag.E8.rank).drop 3280).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p17 :
    (((allVecs Tag.E8.rank).drop 3485).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p18 :
    (((allVecs Tag.E8.rank).drop 3690).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p19 :
    (((allVecs Tag.E8.rank).drop 3895).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p20 :
    (((allVecs Tag.E8.rank).drop 4100).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p21 :
    (((allVecs Tag.E8.rank).drop 4305).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p22 :
    (((allVecs Tag.E8.rank).drop 4510).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p23 :
    (((allVecs Tag.E8.rank).drop 4715).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p24 :
    (((allVecs Tag.E8.rank).drop 4920).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p25 :
    (((allVecs Tag.E8.rank).drop 5125).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p26 :
    (((allVecs Tag.E8.rank).drop 5330).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p27 :
    (((allVecs Tag.E8.rank).drop 5535).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p28 :
    (((allVecs Tag.E8.rank).drop 5740).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p29 :
    (((allVecs Tag.E8.rank).drop 5945).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p30 :
    (((allVecs Tag.E8.rank).drop 6150).take 205).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rdCheck2_E8_p31 :
    (((allVecs Tag.E8.rank).drop 6355).take 206).all (eCheck2 .E8 241 okE8) = true := by
  decide +kernel

theorem rdCheck2_E8_length : (allVecs Tag.E8.rank).length = 6561 := by
  decide +kernel

theorem rdCheck2_E8 : rdCheck2 .E8 241 okE8 = true := by
  have h : (((allVecs Tag.E8.rank).drop 0).take 6561).all (eCheck2 .E8 241 okE8) = true :=
    (rdE8_all_take_join (a := 0) (b := 6355) (c := 206) (rdE8_all_take_join (a := 0) (b := 6150) (c := 205) (rdE8_all_take_join (a := 0) (b := 5945) (c := 205) (rdE8_all_take_join (a := 0) (b := 5740) (c := 205) (rdE8_all_take_join (a := 0) (b := 5535) (c := 205) (rdE8_all_take_join (a := 0) (b := 5330) (c := 205) (rdE8_all_take_join (a := 0) (b := 5125) (c := 205) (rdE8_all_take_join (a := 0) (b := 4920) (c := 205) (rdE8_all_take_join (a := 0) (b := 4715) (c := 205) (rdE8_all_take_join (a := 0) (b := 4510) (c := 205) (rdE8_all_take_join (a := 0) (b := 4305) (c := 205) (rdE8_all_take_join (a := 0) (b := 4100) (c := 205) (rdE8_all_take_join (a := 0) (b := 3895) (c := 205) (rdE8_all_take_join (a := 0) (b := 3690) (c := 205) (rdE8_all_take_join (a := 0) (b := 3485) (c := 205) (rdE8_all_take_join (a := 0) (b := 3280) (c := 205) (rdE8_all_take_join (a := 0) (b := 3075) (c := 205) (rdE8_all_take_join (a := 0) (b := 2870) (c := 205) (rdE8_all_take_join (a := 0) (b := 2665) (c := 205) (rdE8_all_take_join (a := 0) (b := 2460) (c := 205) (rdE8_all_take_join (a := 0) (b := 2255) (c := 205) (rdE8_all_take_join (a := 0) (b := 2050) (c := 205) (rdE8_all_take_join (a := 0) (b := 1845) (c := 205) (rdE8_all_take_join (a := 0) (b := 1640) (c := 205) (rdE8_all_take_join (a := 0) (b := 1435) (c := 205) (rdE8_all_take_join (a := 0) (b := 1230) (c := 205) (rdE8_all_take_join (a := 0) (b := 1025) (c := 205) (rdE8_all_take_join (a := 0) (b := 820) (c := 205) (rdE8_all_take_join (a := 0) (b := 615) (c := 205) (rdE8_all_take_join (a := 0) (b := 410) (c := 205) (rdE8_all_take_join (a := 0) (b := 205) (c := 205) rdCheck2_E8_p0 rdCheck2_E8_p1) rdCheck2_E8_p2) rdCheck2_E8_p3) rdCheck2_E8_p4) rdCheck2_E8_p5) rdCheck2_E8_p6) rdCheck2_E8_p7) rdCheck2_E8_p8) rdCheck2_E8_p9) rdCheck2_E8_p10) rdCheck2_E8_p11) rdCheck2_E8_p12) rdCheck2_E8_p13) rdCheck2_E8_p14) rdCheck2_E8_p15) rdCheck2_E8_p16) rdCheck2_E8_p17) rdCheck2_E8_p18) rdCheck2_E8_p19) rdCheck2_E8_p20) rdCheck2_E8_p21) rdCheck2_E8_p22) rdCheck2_E8_p23) rdCheck2_E8_p24) rdCheck2_E8_p25) rdCheck2_E8_p26) rdCheck2_E8_p27) rdCheck2_E8_p28) rdCheck2_E8_p29) rdCheck2_E8_p30) rdCheck2_E8_p31)
  rw [List.drop_zero, List.take_of_length_le (le_of_eq rdCheck2_E8_length)] at h
  exact h

end RD


theorem rdValues_E8 : ∀ (L : Type) [Field L] [CharP L 2] (a : Fin Tag.E8.rank → Lˣ),
    (∀ j, a j ^ 3 = 1) → ∀ i : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) i).ncard = 6 ∨ (componentRoots (rootCharHom a) i).ncard = 72 ∨
        (componentRoots (rootCharHom a) i).ncard = 84 ∨
        (componentRoots (rootCharHom a) i).ncard = 126 ∨
        (componentRoots (rootCharHom a) i).ncard = 240 := by
  intro L _ _ a ha i
  obtain ⟨s, hs, h | h⟩ := RD.size_of_check2 CFSG.LieType.Steinberg.Adjoint.noG2_E8 241 RD.okE8 RD.rdCheck2_E8 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [RD.okE8, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [RD.okE8] at hs

theorem rdSize_E8 : RDSize .E8 := by
  intro L _ _ a ha i
  have := rdValues_E8 L a ha i
  omega

theorem rdGlue_E8 : RDGlue .E8 := by
  intro L _ _ a ha i hi
  exact RD.glue_of_check2 CFSG.LieType.Steinberg.Adjoint.noG2_E8 241 RD.okE8 (by norm_num) RD.rdCheck2_E8 a ha i hi

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
