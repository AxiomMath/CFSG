module

public import CFSG.GH74.GLS.C3.Layer1.Th2L627Q
public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

theorem autD8_of_hasL2Model_five {K : Type} [Group K] [Finite K]
    (h : HasL2Model K (fun q => q = 5)) :
    Nat.card (MulAut K) = 120 ∧ ∀ X : Subgroup (MulAut K), Nat.card ↥X = 8 → IsD8 X := by
  have hfive : IsFM9 5 := Th2Tstar.isFM9_five
  obtain ⟨F, _, _, e, hF, hFq⟩ := exists_l2Field_of_hasL2Model hfive h
  have hD : ∀ x : MulAut K, x ∈ innDiagSub e := Th2.L625.mem_innDiagSub_of_card_five hF e hFq
  have hMul : Nat.card (MulAut K) = 120 := by
    rw [card_mulAut_eq e, card_innDiagSub_q e hF, hFq,
      (ivk_1_2e F hF K e).2.2 5 1 (by norm_num) (by rw [hFq]; norm_num)]
    norm_num
  refine ⟨hMul, fun X hX => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h120 : (Nat.factorization 120) 2 = 3 := by
    refine le_antisymm ?_ ((Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).1
      (by norm_num : 2 ^ 3 ∣ 120))
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 4 ∣ 120 := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).2 hlt
    omega
  have hcard : Nat.card ↥X = 2 ^ (Nat.card (MulAut K)).factorization 2 := by
    rw [hX, hMul, h120]
    norm_num
  let T : Sylow 2 (MulAut K) := Sylow.ofCard X hcard
  obtain ⟨m, hm, ⟨d⟩⟩ := dihedral_of_sylow_inf_innDiag e hF T
  have hTX : (T : Subgroup (MulAut K)) = X := Sylow.coe_ofCard X hcard
  have hXinf : X = X ⊓ innDiagSub e := (inf_eq_left.2 (fun x _ => hD x)).symm
  have dX : ↥X ≃* DihedralGroup (2 ^ m) :=
    (MulEquiv.subgroupCongr hXinf).trans ((MulEquiv.subgroupCongr (by rw [hTX]) :
      ↥(X ⊓ innDiagSub e) ≃* ↥((T : Subgroup (MulAut K)) ⊓ innDiagSub e)).trans d)
  have hm2 : m = 2 := by
    have h1 : Nat.card ↥X = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr dX.toEquiv
    rw [hX, Nat.card_eq_fintype_card, DihedralGroup.card] at h1
    have h2 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hm2
  exact ⟨dX⟩

end CFSG.GH74.GLS.Th2.L627
