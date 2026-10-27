module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.CGT.PushingUpLit.CGT6M.J2Five
public import CFSG.Sporadic.J2

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint

theorem linesData_J2 {Q : Type} [Group Q]
    (hQ : NativeSporadic.IsSporadic Q .J2) : LinesData Q := by
  obtain ⟨e⟩ := hQ
  obtain ⟨a, b, g, ha1, ha5, hab, hga, hgb⟩ := exists_five_data_seedGroup
  let f : CFSG.Sporadic.Bridge.J2.seedGroup ≃* Q :=
    (CFSG.Sporadic.Bridge.J2.nativeEquiv.symm).trans e.symm
  refine ⟨f a, f b, f g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => ha1 (f.injective (by rw [h, map_one]))
  · rw [← map_pow, ha5, map_one]
  · exact hab.map f
  · rw [← map_mul, ← map_inv, ← map_mul, hga]
  · rw [← map_mul, ← map_inv, ← map_mul, hgb, map_inv, map_mul]
  · have hcard : Nat.card Q = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    rw [hcard]
    norm_num

end CFSG.CGT.PushingUpLit.CGT6M
