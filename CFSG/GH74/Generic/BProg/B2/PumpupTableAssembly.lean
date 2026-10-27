module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableRee
public import CFSG.GH74.Generic.BProg.B2.PumpupTableEven
public import CFSG.GH74.Generic.BProg.B2.PumpupTableExc
public import CFSG.GH74.Generic.BProg.B2.PumpupTableThree
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
public import CFSG.GH74.Generic.BProg.B2.PumpupTableSp4
public import CFSG.GH74.Generic.BProg.B2.ShapeSporadic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

structure PumpupOpen : Prop where
  sp4out : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    PumpupEmptyOut (fun X _ => LieModel X .PSp 2 p f)
  g2out : ∀ p f : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    PumpupEmptyOut (fun X _ => LieModel X .G2 0 p f)
  d4out : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    PumpupEmptyOut (fun X _ => LieModel X .trialityD4 0 p f)

theorem pow_le_three_of_lt_five {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : ¬ 5 ≤ p ^ f) :
    p ^ f ≤ 3 := by
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  omega

section Assembly



theorem pumpupLeaves_of_open (h : PumpupOpen) : PumpupLeaves where
  alt := fun n _ hn N _ _ H t L hs he => not_alt_of_shapeInCent hs n hn he
  m11 := fun N _ _ H t L hs hm => not_M11_of_shapeInCent hs hm
  m12 := fun N _ _ H t L hs hm => not_M12_of_shapeInCent hs hm
  m22 := fun N _ _ H t L hs hm => not_M22_of_shapeInCent hs hm
  m23 := fun N _ _ H t L hs hm => not_M23_of_shapeInCent hs hm
  j1 := fun N _ _ H t L hs hm => not_J1_of_shapeInCent hs hm
  j2 := fun N _ _ H t L hs hm => not_J2_of_shapeInCent hs hm
  j3 := fun N _ _ H t L hs hm => not_J3_of_shapeInCent hs hm
  mcl := fun N _ _ H t L hs hm => not_McL_of_shapeInCent hs hm
  ly := fun N _ _ H t L hs hm => not_Ly_of_shapeInCent hs hm
  l2 := fun p f hp hp2 hf => PumpupTableL2.pumpup_l2 p f hp hp2 hf
  l3 := fun p f hp hp2 hf hodd => by
    by_cases h5 : 5 ≤ p ^ f
    · exact PumpupEmpty.of_in_out (PumpupTableL3.pumpupIn_l3 hp hp2 h5 hodd)
        (PumpupTableOutL3.pumpupOut_l3 hp hp2 h5 hodd)
    · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf
        (pow_le_three_of_lt_five hp hp2 h5)
      exact PumpupTableThree.pumpup_l3three
  u3 := fun p f hp hp2 hf => by
    by_cases h5 : 5 ≤ p ^ f
    · exact PumpupEmpty.of_in_out (PumpupTableL3.pumpupIn_u3 hp hp2 h5)
        (PumpupTableOutU3.pumpupOut_u3 hp hp2 h5)
    · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf
        (pow_le_three_of_lt_five hp hp2 h5)
      exact PumpupTableThree.pumpup_u3three
  sp4 := fun p f hp hp2 hf => PumpupEmpty.of_in_out (PumpupTableSp4.pumpupIn_sp4 hp hp2 hf)
    (h.sp4out p f hp hp2 hf)
  g2 := fun p f hp hp2 hp3 hf => PumpupEmpty.of_in_out
    (PumpupTableExc.pumpupIn_g2 p f hp hp2 hf) (h.g2out p f hp hp2 hp3 hf)
  g2three := PumpupTableThree.pumpup_g2three
  d4 := fun p f hp hp2 hf => PumpupEmpty.of_in_out
    (PumpupTableExc.pumpupIn_d4 p f hp hp2 hf) (h.d4out p f hp hp2 hf)
  l4three := PumpupTableThree.pumpup_l4three
  u4three := PumpupTableThree.pumpup_u4three
  ree := fun f => PumpupTableRee.pumpup_ree f
  l28 := PumpupTableEven.pumpup_l28
  l216 := PumpupTableEven.pumpup_l216
  l34 := PumpupTableEven.pumpup_l34
  u34 := PumpupTableEven.pumpup_u34
  sz8 := PumpupTableEven.pumpup_sz8

theorem pumpupTableU_of_open (h : PumpupOpen) : PumpupTableU :=
  pumpupTableU_of_leaves (pumpupLeaves_of_open h)

end Assembly

end CFSG.GH74.Generic.BProg.B2
