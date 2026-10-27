module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Fin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Base
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClassTriQuad
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

set_option linter.unusedSectionVars false

section Chi

variable {L : Type} [Field L]

@[expose] def torV5 (ζ : Lˣ) (x : Fin 8 → ZMod 5) : Fin Tag.E8.rank → Lˣ :=
  fun i => ζ ^ (x i).val

@[expose] def chiZ (ζ : Lˣ) (a : ZMod 5) : Lˣ := ζ ^ a.val

theorem pow_val_add5 {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (a b : ZMod 5) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have key : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 5) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 5]
    rw [pow_add, pow_mul, h5, one_pow, mul_one]
  rw [← pow_add, ZMod.val_add, ← key]

theorem chiZ_add {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (a b : ZMod 5) :
    chiZ ζ (a + b) = chiZ ζ a * chiZ ζ b :=
  pow_val_add5 h5 a b

theorem chiZ_zero (ζ : Lˣ) : chiZ ζ 0 = 1 := by
  simp [chiZ]

theorem chiZ_injective {ζ : Lˣ} (hζ : orderOf ζ = 5) : Function.Injective (chiZ ζ) := by
  intro a b h
  have h2 : ζ ^ a.val = ζ ^ b.val := h
  rw [pow_eq_pow_iff_modEq, hζ] at h2
  have hx := ZMod.val_lt a
  have hy := ZMod.val_lt b
  have : a.val = b.val := by
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact ZMod.val_injective _ this

theorem zpow_eq_chiZ {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (z : ℤ) : ζ ^ z = chiZ ζ (z : ZMod 5) := by
  have h1 : (((z : ZMod 5).val : ℕ) : ℤ) = z % 5 := ZMod.val_intCast z
  have h5z : ζ ^ (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast, h5]
  rw [chiZ, ← zpow_natCast, h1]
  conv_lhs => rw [← Int.emod_add_mul_ediv z 5]
  rw [zpow_add, zpow_mul, h5z, one_zpow, mul_one]

theorem rootChar_torV5 {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (x : Fin 8 → ZMod 5)
    (v : Fin Tag.E8.rank → ℤ) : rootChar (torV5 ζ x) v = chiZ ζ (pairZ x v) := by
  have h1 : rootChar (torV5 ζ x) v = ζ ^ (∑ i, (((x i).val : ℕ) : ℤ) * v i) := by
    rw [rootChar, ← SmallQ3.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [torV5, ← zpow_natCast, ← zpow_mul]
  rw [h1, zpow_eq_chiZ h5]
  congr 1
  simp [pairZ]

theorem torV5_add {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (x y : Fin 8 → ZMod 5) :
    torV5 ζ (x + y) = torV5 ζ x * torV5 ζ y :=
  funext fun i => pow_val_add5 h5 _ _

theorem torV5_zero (ζ : Lˣ) : torV5 ζ (0 : Fin 8 → ZMod 5) = 1 := by
  funext i
  show ζ ^ ((0 : ZMod 5)).val = 1
  simp

theorem exists_eq_torV5 {ζ : Lˣ} (hζ : orderOf ζ = 5) (a : Fin Tag.E8.rank → Lˣ)
    (ha : ∀ i, a i ^ 5 = 1) : ∃ x : Fin 8 → ZMod 5, a = torV5 ζ x := by
  have hprim : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.iff_orderOf.2 hζ
  have hprimL : IsPrimitiveRoot (ζ : L) 5 := IsPrimitiveRoot.coe_units_iff.2 hprim
  have : ∀ i, ∃ k : ℕ, k < 5 ∧ ζ ^ k = a i := fun i => by
    have h1 : ((a i : Lˣ) : L) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
    obtain ⟨k, hk, hk'⟩ := hprimL.eq_pow_of_pow_eq_one h1
    exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk')⟩
  choose k hk hka using this
  refine ⟨fun i => (k i : ZMod 5), funext fun i => ?_⟩
  rw [torV5, ZMod.val_natCast_of_lt (hk i), hka i]

end Chi

section Eig

@[expose] def IsEig (x : Fin 8 → ZMod 5) : Prop :=
  ∀ j : Fin 8, ∑ k, x k * ((e8M k j : ℤ) : ZMod 5) = 2 * x j

theorem isEig_E5_aux : ∀ (i : Fin 4) (j : Fin 8),
    ∑ k, E5 i k * ((e8M k j : ℤ) : ZMod 5) = 2 * E5 i j := by
  decide +kernel

theorem isEig_xc (c : Fin 4 → ZMod 5) : IsEig (xc c) := by
  intro j
  have key : ∀ i : Fin 4, ∑ k, E5 i k * ((e8M k j : ℤ) : ZMod 5) = 2 * E5 i j :=
    fun i => isEig_E5_aux i j
  calc ∑ k, xc c k * ((e8M k j : ℤ) : ZMod 5)
      = ∑ k, ∑ i, c i * (E5 i k * ((e8M k j : ℤ) : ZMod 5)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [xc, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, c i * ∑ k, E5 i k * ((e8M k j : ℤ) : ZMod 5) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ i, c i * (2 * E5 i j) := by simp only [key]
    _ = 2 * xc c j := by
        simp only [xc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem e8M_eq_tab : ∀ k j : Fin 8, e8M k j = e8MTab k j := by
  intro k j
  fin_cases k <;> fin_cases j <;> rfl

theorem eig_eq_xc {x : Fin 8 → ZMod 5} (hx : IsEig x) : x = xc ![x 4, x 2, x 1, x 0] :=
  eig_eq_xc_aux fun j => by simpa only [e8M_eq_tab] using hx j

end Eig

section Sq

theorem e8PhiFourWeyl_sq_smul5 (δ : Fin Tag.E8.rank → ℤ) :
    e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, Matrix.mulVec_mulVec,
    CFSG.HardMathSupport.Timmesfeld.LangTorus.e8FourMat_rel, Matrix.neg_mulVec,
    Matrix.one_mulVec]

end Sq

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
