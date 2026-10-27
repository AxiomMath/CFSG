module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4T2c
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Out
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsL4U4 StabU

theorem noQ8Datum_u43 : ∀ (F : Type) [Group F], LieModel F .PSU 4 3 1 → NoQ8Datum F := by
  intro F _ hm G _ _ N _ ⟨eN⟩ hC _ R S t hD _
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

theorem smallSimpleLeaf_u43 : SmallSimpleLeaf fun F _ => LieModel F .PSU 4 3 1 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_u43

end CFSG.ClassicalInvolution.Q3.TA3
