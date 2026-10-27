module

public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

private theorem fld_packL {w : Nat} : ∀ l : List Nat, (packL w l).2 = true →
    (∀ x ∈ l, x < 2 ^ w) ∧ PackFld.Fld w (packL w l).1 (fun i => l[i]?.getD 0)
  | [], _ => ⟨by simp, PackFld.fld_congr (PackFld.fld_zero w) (fun i => by simp)⟩
  | x :: xs, h => by
    change ((packL w xs).2 && Nat.blt x (Nat.shiftLeft (nat_lit 1) w)) = true at h
    rw [Bool.and_eq_true] at h
    have hx : x < 2 ^ w := by
      have := Nat.blt_eq.mp h.2
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    obtain ⟨ha, hf⟩ := fld_packL xs h.1
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy
    · have hs := PackFld.fld_shl 1 hf
      rw [Nat.mul_one] at hs
      refine PackFld.fld_congr (PackFld.fld_or (PackFld.fld_one hx) hs) (fun i => ?_)
      rcases i with _ | i
      · simp
      · simp

theorem arrBind_sound {a : Array Nat} {n w P : Nat} (h : arrBind a n w P = true) :
    a = unpack n w P := by
  unfold arrBind at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨ha, hf⟩ := fld_packL a.toList h2
  rw [← Nat.eq_of_beq_eq_true h3]
  have hs : a.size = n := by simpa using Nat.eq_of_beq_eq_true h1
  refine Array.ext (by simp [unpack, hs]) (fun i h1 h2 => ?_)
  simp only [unpack, Array.getElem_ofFn]
  rw [PackFld.pg_of_fld hf ?_]
  · simp [h1]
  · have := ha (a.toList[i]'(by simpa using h1)) (List.getElem_mem _)
    simpa [h1] using this

end CFSG.KC.Misc.ArrEnum

end
