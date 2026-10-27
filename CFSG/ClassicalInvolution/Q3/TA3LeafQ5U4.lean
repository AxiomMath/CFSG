module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Cls
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Pairc
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsL4U4 StabU

theorem noQ8Datum_u4Ne3 : ∀ (F : Type) [Group F], SmallU4Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC _ R S t hD _
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let e : ↥N ≃* StatedProj (StatedSU 4 (p ^ f) K) := eN.trans e₀
  obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  have htN : t ∈ N := TightDatum.mem_of_noQ8Outer hD hC
    (noQ8Outer_of_mulEquiv e (Q5U4.noQ8Outer_statedPSU h hp2))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hD.order
  rcases Q5U4.inv_split h hp2 h8 hz with ⟨X, hX, hXX, h1, hm1⟩ | ⟨hq, X, hX, hXX⟩
  · obtain ⟨Rf, s, hs0, -, hR, hXR⟩ := Q5U4.exists_frame_t2 h hp2 X hXX h1 hm1
    let H₀ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
      ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range
    have : Group.IsPerfect H₀ := Q5U4.isPerfect_range_bdHomU h hR (by omega)
    exact TightDatum.false_of_model hD hC e htN hX.symm H₀
      (Q5U4.range_bdHomU_le_centralizer h hR hXR)
      (fun M hM hMp => Q5U4.le_range_bdHomU_of_perfect h hR hp2 hs0 hXR hM hMp)
      (Q5U4.noOddNormal_range_bdHomU h hR hp2) (Q5U4.noQ8Fix_t2 h hp2 hs0 hR)
  · obtain ⟨P, l, hP, hl, -, hXP⟩ := Q5U4.exists_pair_frame h hp2 hq X hXX
    have hl0 : l ≠ 0 := by
      rintro rfl
      norm_num at hl
    let H₀ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
      ((QuotientGroup.mk' (scal p f K)).comp (Q5U4.pairHom h hP)).range
    have : Group.IsPerfect H₀ := Q5U4.isPerfect_range_pairHom h hP
    exact TightDatum.false_of_model hD hC e htN hX.symm H₀
      (Q5U4.range_pairHom_le_centralizer h hP hXP)
      (fun M hM hMp => Q5U4.le_range_pairHom_of_perfect h hP hp2 hl0 hXP hM hMp)
      (Q5U4.noOddNormal_range_pairHom h hP) (Q5U4.noQ8Fix_pair h hP hp2)

theorem smallSimpleLeaf_u4Ne3 : SmallSimpleLeaf SmallU4Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_u4Ne3

end CFSG.ClassicalInvolution.Q3.TA3
