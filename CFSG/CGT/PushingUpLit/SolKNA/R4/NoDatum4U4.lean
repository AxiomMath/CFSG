module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4T2c
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Pairc

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsL4U4 StabU

theorem noDatum4_u4Ne3 : ∀ (F : Type) [Group F], SmallU4Ne3 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h8, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC _ R S t hD
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

theorem smallLeafR_u4Ne3 {r : ℕ} : SmallLeafR r SmallU4Ne3 :=
  SmallLeafR.of_noDatum4 noDatum4_u4Ne3

theorem noDatum4_u43 : ∀ (F : Type) [Group F], LieModel F .PSU 4 3 1 → NoDatum4 F := by
  intro F _ hm G _ _ N _ ⟨eN⟩ hC _ R S t hD
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  let e : ↥N ≃* StatedProj (StatedSU 4 (3 ^ 1) K) := eN.trans e₀
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have htN : t ∈ N := TightDatum.mem_of_noQ8Outer hD hC
    (noQ8Outer_of_mulEquiv e (Q5U4.noQ8Outer_statedPSU h hp2))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hD.order
  rcases Q5U4.inv_split h hp2 (by decide) hz with ⟨X, hX, hXX, h1, hm1⟩ | ⟨hq, -⟩
  · obtain ⟨Rf, s, hs0, -, hR, hXR⟩ := Q5U4.exists_frame_t2 h hp2 X hXX h1 hm1
    exact Q3U4.false_t2_U43 h hR hXR (by norm_num) hp2 hs0 hXX hD hC e htN hX.symm
  · exact absurd hq (by decide)

theorem smallLeafR_u43 {r : ℕ} : SmallLeafR r (fun F _ => LieModel F .PSU 4 3 1) :=
  SmallLeafR.of_noDatum4 noDatum4_u43

end CFSG.CGT.PushingUpLit.SolKNA.R4
