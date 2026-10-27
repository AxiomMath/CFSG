module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.F4Transvection
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule binRep_injective binRep_apply)

section Aut

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

theorem card_range_binRep_sub_one (t : MulAut W) [Finite W] :
    Nat.card (LinearMap.range (binRep W t - 1)) = (fixV (Subgroup.zpowers t)).index := by
  have hker : (LinearMap.ker (binRep W t - 1)).toAddSubgroup =
      (fixV (Subgroup.zpowers t)).toAddSubgroup := by
    ext v
    simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero, binRep_apply]
    show _ ↔ Additive.toMul v ∈ fixV (Subgroup.zpowers t)
    rw [mem_fixV_zpowers_iff]
    exact ⟨fun h => h, fun h => h⟩
  rw [← Subgroup.index_toAddSubgroup, ← hker]
  exact (Nat.card_congr (LinearMap.quotKerEquivRange (binRep W t - 1)).toEquiv).symm

end Aut

theorem orderOf_mul_le_five_of_index_four {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {z t t' : MulAut W}
    (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) (htz : t * z = z * t)
    (ht'z : t' * z = z * t') (ht2 : t * t = 1) (ht'2 : t' * t' = 1)
    (hA : (fixV (Subgroup.zpowers t)).index = 4) (hA' : (fixV (Subgroup.zpowers t')).index = 4) :
    orderOf (t * t') ≤ 5 := by
  let _ : Module (ZMod 2) (Additive W) := binModule (fun v => by rw [pow_two]; exact hW v)
  have key := f4_transvection_order (V := Additive W) (z := binRep W z) (t := binRep W t)
    (t' := binRep W t')
    (by rw [← map_pow, hz3, map_one])
    (fun v h => by
      have := hfpf (Additive.toMul v) (by simpa [binRep_apply] using congrArg Additive.toMul h)
      exact Additive.toMul.injective (by simpa using this))
    (by rw [← map_mul, ← map_mul, htz]) (by rw [← map_mul, ← map_mul, ht'z])
    (by rw [← map_mul, ht2, map_one]) (by rw [← map_mul, ht'2, map_one])
    (by rw [card_range_binRep_sub_one]; exact hA) (by rw [card_range_binRep_sub_one]; exact hA')
  obtain ⟨n, hn1, hn5, hn⟩ := key
  have hpow : (t * t') ^ n = 1 := by
    apply binRep_injective (M := W)
    rw [map_pow, map_mul, hn, map_one]
  exact (Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)).trans hn5


end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
