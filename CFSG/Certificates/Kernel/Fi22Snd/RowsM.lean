module

public import Certificates.Data.Kernel.Fi22Nbr3153M
public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153

theorem imgOK_of_M {n d g x : Nat} {R M S : Nat → Nat}
    (hrow : ∀ x < n, rowOK n d R M S x = true) (hinj : CFSG.KS.PinvS.InjK n 12 g) (hx : x < n)
    (h : imgOKM n d g R M x = true) : imgOK n d g R M x = true := by
  unfold imgOKM at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h2
  have hy : pg (nat_lit 12) (nat_lit 4095) g x < n := Nat.le_of_ble_eq_true h1
  have hrx := hrow x hx
  have hry := hrow _ hy
  have hsub : (decodeRow d (R x)).map (pg (nat_lit 12) (nat_lit 4095) g) ⊆
      decodeRow d (R (pg (nat_lit 12) (nat_lit 4095) g x)) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    rw [decodeRow_eq] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have hb := CFSG.KC.Pack.allN_spec h2 i (List.mem_range.1 hi)
    rw [beq_bit, row_mask hry] at hb
    exact of_decide_eq_true hb
  have hnd : ((decodeRow d (R x)).map (pg (nat_lit 12) (nat_lit 4095) g)).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hinj.2 a (row_entry_lt hrx ha) b (row_entry_lt hrx hb) e)
      (row_pairwise hrx).nodup
  have hperm := (hnd.subperm hsub).perm_of_length_le (by
    rw [List.length_map, row_length, row_length])
  unfold imgOK
  rw [CFSG.KC.Pack.strictB_eq]
  refine CFSG.KC.Pack.band_iff.2 ⟨h1, ?_⟩
  rw [CFSG.KC.Pack.strictB_eq]
  refine Nat.beq_eq.mpr (Nat.eq_of_testBit_eq fun q => ?_)
  rw [imgMaskK_testBit (row_d_lt hrx), row_mask hry]
  refine decide_eq_decide.2 ⟨?_, fun hq => ?_⟩
  · rintro ⟨i, hi, rfl⟩
    refine hsub (List.mem_map_of_mem ?_)
    rw [decodeRow_eq]
    exact List.mem_map_of_mem (List.mem_range.2 hi)
  · obtain ⟨p, hp, hpq⟩ := List.mem_map.1 (hperm.symm.subset hq)
    rw [decodeRow_eq] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    exact ⟨i, List.mem_range.1 hi, hpq⟩

end CFSG.KC.Fi22Snd

end
