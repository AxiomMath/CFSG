module

public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.Kernel.Misc.HexDrop
import all CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.HexText

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PackFld CFSG.KS.HexText
open CFSG.KS.Text (hexV)

theorem dropL_eq : ∀ (cs : List Char) (m : Nat), dropL m cs = cs.drop m
  | [], m => by cases m <;> rfl
  | _ :: _, 0 => rfl
  | c :: t, m + 1 => by
    change dropL m t = (c :: t).drop (m + 1)
    rw [dropL_eq t m, List.drop_succ_cons]

theorem getElem!_drop (cs : List Char) (m k : Nat) : (cs.drop m)[k]! = cs[m + k]! := by
  simp only [getElem!_def, List.getElem?_drop]

theorem numA_drop (cs : List Char) (m o : Nat) : ∀ c, numA (cs.drop m) o c = numA cs (m + o) c
  | 0 => rfl
  | c + 1 => by
    simp only [numA]
    rw [numA_drop cs m o c, getElem!_drop, Nat.add_assoc]

theorem hexTable_drop_sound {cs : List Char} {d n w N₀ N : Nat} {F₀ F : Nat → Nat}
    (h₀ : hexFlat cs d n w N₀ F₀ = true) (h : hexFlat (dropL (d * n * N₀) cs) d n w N F = true) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d n (n * (N₀ + j)) (String.ofList cs) =
      unpack n w (F j) := by
  have hd : 0 < d := by
    unfold hexFlat at h
    simp only [bAnd_iff] at h
    exact Nat.blt_eq.mp h.1
  rw [dropL_eq] at h
  obtain ⟨hasc₀, -⟩ := decode h₀
  obtain ⟨hasc₁, hF⟩ := decode h
  have hdig := digits_of h
  have hasc : ∀ k < d * n * N₀ + d * n * N, k < cs.length ∧ (cs[k]!).toNat < 128 := by
    intro k hk
    by_cases hk₀ : k < d * n * N₀
    · exact hasc₀ k hk₀
    · obtain ⟨a, b⟩ := hasc₁ (k - d * n * N₀) (by omega)
      rw [List.length_drop] at a
      rw [getElem!_drop, Nat.add_sub_cancel' (by omega)] at b
      exact ⟨by omega, b⟩
  intro j hj
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem_ofFn]
    obtain ⟨e1, e2⟩ := hF j hj i hi
    have ho : d * (n * (N₀ + j) + i) = d * n * N₀ + d * (n * j + i) := by
      rw [Nat.mul_add n, Nat.add_assoc, Nat.mul_add d, Nat.mul_assoc]
    rw [e1, numA_drop, ho]
    exact num_bytes (o := d * n * N₀ + d * (n * j + i)) hasc
      (fun c => CFSG.Monster.B.Co2.Native.hexAt (String.ofList cs).toUTF8
        (d * n * N₀ + d * (n * j + i)) c)
      rfl (fun c => rfl) d (by have := e2 (d - 1) (by omega); omega)
      (fun s hs => by
        have := hdig _ (e2 s hs)
        rwa [getElem!_drop, ← Nat.add_assoc] at this)

end CFSG.KC.Misc.HexFlat

end
