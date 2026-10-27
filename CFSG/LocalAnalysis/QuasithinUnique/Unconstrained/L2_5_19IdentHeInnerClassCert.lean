module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheckInputs
public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public import CFSG.Sporadic.HeldB.ClassCount

public section

namespace CFSG.QuasithinUnique.Id2519.HeInner

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def heDClassPerm : Fin 10 ≃ Fin 10 where
  toFun := ![6, 7, 2, 8, 9, 3, 4, 5, 1, 0]
  invFun := ![9, 8, 2, 5, 6, 7, 0, 1, 3, 4]
  left_inv := by decide
  right_inv := by decide

theorem heDp_classes_equiv_of (hv : ValidSchreier heDp)
    (hcard : Nat.card heDp.originalSubgroup = 20160)
    (ha : ∀ j < 5, heDp.sift (permOrId 105 heDGens[j]!) 0 = true)
    (hc : ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes heDOrbits)
    (hd : ∀ j < heDGens.size, TabRep heDGens[j]! (permOrId 105 heDGens[j]!))
    (he : heDEnum.tabs.size = 20160) :
    ∃ e : Fin 10 ≃ ConjClasses heDp.originalSubgroup, ∀ i, (e i).carrier.ncard =
      (![2880, 2880, 1260, 4032, 4032, 1260, 1260, 2240, 315, 1] : Fin 10 → ℕ) i := by
  have hsz : heDGens.size = 5 := by simp [heDGens]
  have hle : genGroup 105 heDGens (fun j => permOrId 105 heDGens[j]!) ≤
      heDp.originalSubgroup := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (heDp.sift_eq_true_iff_mem_original hv _).1 (ha j (hsz ▸ hj))
  have hG : Nat.card (genGroup 105 heDGens (fun j => permOrId 105 heDGens[j]!)) = 20160 := by
    rw [(genGroup_enumerates (f := fun j => permOrId 105 heDGens[j]!) hd hc).card,
      Array.length_toList, he]
  obtain ⟨e2, he2⟩ := conjClasses_equiv_of_mulEquiv
    (MulEquiv.subgroupCongr (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hG])))
  refine ⟨heDClassPerm.trans
    ((classEquivS (f := fun j => permOrId 105 heDGens[j]!) hd hc).trans e2), fun i => ?_⟩
  rw [Equiv.trans_apply, Equiv.trans_apply, he2, ← Nat.card_coe_set_eq, card_classS hd hc]
  revert i
  decide

end CFSG.QuasithinUnique.Id2519.HeInner

end
