
module

public import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.Certificates.Kernel.HexaKGlue

public section

namespace CFSG.KC.HeFixKSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.KC.HeFixK
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore
open CFSG.KLie.CT (fget)

theorem closK_spec {n w nb N SA SB SM q t j : Nat} (h : closK n w nb N SA SB SM q t j = true) :
    ∀ i < N, ∃ m < N,
      (List.range 32).map (pg 6 (mask 6) (fget SA m 192)) =
        ((List.range 32).map (pg 6 (mask 6) (fget SA i 192))).map
          (fun x => (unpack 32 6 q)[x]!) ∧
      (List.range nb).map (pg w (mask w) (fget SB m (nb * w))) =
        ((List.range nb).map (pg w (mask w) (fget SB i (nb * w)))).map
          (fun x => (unpack n w t)[x]!) := by
  intro i hi
  unfold closK at h
  simp only [CFSG.KC.HexaK.strictB_eq', CFSG.KC.HexaK.andB_eq, Bool.and_eq_true,
    Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨-, hall⟩ := h
  have hi' := CFSG.KS.allN_spec hall i hi
  simp only [CFSG.KC.HexaK.strictB_eq', CFSG.KC.HexaK.andB_eq, Bool.and_eq_true,
    Nat.blt_eq] at hi'
  obtain ⟨hm, ha, hb, hall2⟩ := hi'
  have hbeq := Nat.eq_of_beq_eq_true hb
  refine ⟨_, hm, ?_, ?_⟩
  · rw [List.map_map, hbeq]
    apply List.map_congr_left
    intro x hx
    have hx' : x < 32 := List.mem_range.1 hx
    simp only [Function.comp]
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hx',
      CFSG.KC.HeFixK.unpack_getElem! (CFSG.KC.HeFixK.pg_lt_of_canonK ha hx')]
  · rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk' : k < nb := List.mem_range.1 hk
    have hk2 := CFSG.KS.allN_spec hall2 k hk'
    simp only [CFSG.KC.HexaK.strictB_eq', CFSG.KC.HexaK.andB_eq, Bool.and_eq_true,
      Nat.blt_eq] at hk2
    obtain ⟨hxn, hxeq⟩ := hk2
    have hxeq' := Nat.eq_of_beq_eq_true hxeq
    simp only [Function.comp]
    rw [CFSG.KC.HeFixK.unpack_getElem! hxn]
    exact hxeq'.symm

end CFSG.KC.HeFixKSnd

end
