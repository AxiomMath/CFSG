module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.HNLocal.Mat

public section

namespace CFSG.KS.HNLocal.MatPf

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord CFSG.KS.HNLocal Matrix

theorem addL_sound {L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hX : Canon 5 133 13 X) (hY : Canon 5 133 13 Y) :
    Canon 5 133 13 (redP 13 L H 5 9 (X + Y)) ∧ OM (redP 13 L H 5 9 (X + Y)) = OM X + OM Y := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, -, -⟩ := consts_facts hc
  clear hc
  have hXe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hX.1
  have hYe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hY.1
  have ha : ∀ t < 133 * 133, lane 13 X t < 5 := hX.2
  have hb : ∀ t < 133 * 133, lane 13 Y t < 5 := hY.2
  rw [hL, hH, hXe, hYe]
  generalize lane 13 X = a at ha ⊢
  generalize lane 13 Y = b at hb ⊢
  have h12 : (2 : Nat) ^ (13 - 1) = 4096 := by norm_num
  have e : redP 13 (pk 13 (133 * 133) fun _ => 1) (pk 13 (133 * 133) fun _ => 2 ^ (13 - 1)) 5 9
      (pk 13 (133 * 133) a + pk 13 (133 * 133) b) =
      pk 13 (133 * 133) (fun t => (a t + b t) % 5) := by
    rw [pk_add]
    refine redP_pk (by norm_num) hT (fun t ht => ?_) (fun t ht => ?_)
    · have := ha t ht
      have := hb t ht
      rw [h12]
      omega
    · have := ha t ht
      have := hb t ht
      have h10 : (5 : Nat) * 2 ^ (9 + 1) = 5120 := by norm_num
      rw [h10]
      omega
  rw [e]
  refine ⟨canon_pk (fun t _ => Nat.mod_lt _ (by norm_num)) (by norm_num), ?_⟩
  funext i j
  rw [OM_pk (fun t _ => lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)), Matrix.add_apply,
    OM_pk (fun t ht => lt_trans (ha t ht) (by norm_num)),
    OM_pk (fun t ht => lt_trans (hb t ht) (by norm_num)), ZMod.natCast_mod, Nat.cast_add]

end CFSG.KS.HNLocal.MatPf

end
