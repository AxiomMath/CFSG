module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair

@[expose] def stabilizerEquivSz :
    ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ≃
      ↥(MulAction.stabilizer ↥(img11 AutPerm) z0) :=
  { toFun := fun y => ⟨⟨y, y.2.1⟩, mem_centSub_zpowers.1 y.2.2⟩
    invFun := fun y => ⟨y.1, y.1.2, mem_centSub_zpowers.2 y.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem card_Sz :
    Nat.card ↥(img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) = 138240 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(img11 AutPerm) z0)
  rw [MulAction.index_stabilizer, orbit_eq, ncard_nonDuad, card_img11_autPerm,
    ← Nat.card_congr stabilizerEquivSz] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1771)
    (h1.trans (by norm_num : 244823040 = 138240 * 1771))

theorem card_stab_t0_Sz_eq :
    Nat.card ↥((img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) ⊓
      centSub (Subgroup.zpowers t0)) = 3840 :=
  card_stab_t0_Sz card_Sz

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelSz
