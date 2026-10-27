module

public import CFSG.Certificates.Kernel.VecKOrbit

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native

theorem andB_eq_and (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem pw2_eq_pow (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

theorem vOrbit_tables_proved (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) :
    ∀ i < D.n, ap (D.orbit ()).alpha i = lk AT (nat_lit 32) i ∧
      ap (D.orbit ()).beta i = lk BT (nat_lit 32) i := by
  have hO := orbit_eq D hA hB hseed hn hP0 horb hbfs hsort
  simp only [andB_eq_and, Bool.and_eq_true, Nat.blt_eq, pw2_eq_pow] at hn
  have hap : ∀ (f : Nat → Nat), (∀ i < D.n, f i < D.n) → ∀ i < D.n,
      ap ((List.range D.n).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
    intro f hf i hi
    unfold ap
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by have := hf i hi; omega)
  intro i hi
  rw [hO]
  exact ⟨hap (fun h => lk AT 32 h) (fun j hj => (orbAt_iff.1 (horb j hj)).2.1) i hi,
    hap (fun h => lk BT 32 h) (fun j hj => (orbAt_iff.1 (horb j hj)).2.2.1) i hi⟩

end CFSG.KC.VecK

end
