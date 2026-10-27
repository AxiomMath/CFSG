module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.QuasithinUnique

theorem sumMap_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective
      (AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i)
        (fun _ _ => Finset.sum_add_distrib)) := by
  intro a
  refine ⟨Pi.single ⟨0, hm⟩ a, ?_⟩
  simp [Finset.sum_pi_single']

theorem card_evenWeight (m : ℕ) (hm : 1 ≤ m) :
    Nat.card ↥(evenWeight m) = 2 ^ (m - 1) := by
  let f : (Fin m → ZMod 2) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i) (fun _ _ => Finset.sum_add_distrib)
  have hev : evenWeight m = f.ker := rfl
  have hidx : (evenWeight m).index = 2 := by
    rw [hev, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (sumMap_surjective m hm),
      AddSubgroup.card_top, Nat.card_zmod]
  have htot : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
    simp
  have hcard := AddSubgroup.card_mul_index (evenWeight m)
  rw [hidx, htot] at hcard
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (hcard.trans hpow)

end CFSG.HardMathSupport.Cooperstein.Proving

end
