module

public import Certificates.Data.Kernel.B32
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

namespace CFSG.KS.B32

open CFSG.KC.B32 CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem foldl_loop {β : Type} (f : β → UInt8 → β) (b : ByteArray) :
    ∀ (i j : Nat) (acc : β), j + i = b.size →
      ByteArray.foldlM.loop (m := Id) (fun a x => pure (f a x)) b b.size (Nat.le_refl _) i j acc =
        (b.data.toList.drop j).foldl f acc
  | 0, j, acc, h => by
    have hd : b.data.toList.drop j = [] :=
      List.drop_eq_nil_of_le (by
        rw [Array.length_toList]
        have : b.data.size = b.size := rfl
        omega)
    rw [ByteArray.foldlM.loop, hd]
    split <;> rfl
  | i + 1, j, acc, h => by
    have hj : j < b.size := by omega
    have hj' : j < b.data.toList.length := by rw [Array.length_toList]; exact hj
    rw [ByteArray.foldlM.loop, dif_pos hj, List.drop_eq_getElem_cons hj', List.foldl_cons,
      ← foldl_loop f b i (j + 1) _ (by omega)]
    rfl

theorem byteArray_foldl_eq {β : Type} (f : β → UInt8 → β) (init : β) (b : ByteArray) :
    b.foldl f init = b.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  rw [dif_pos (Nat.le_refl _)]
  exact (foldl_loop f b b.size 0 init (by omega)).trans (by rw [List.drop_zero])

theorem toUTF8_toList {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    (String.ofList cs).toUTF8.data.toList = cs.map fun c => UInt8.ofNat c.toNat := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    CFSG.KS.Text.flatMap_ascii' cs h, List.data_toByteArray, List.toList_toArray]

theorem digit_eq (c : Nat) : digitOf c = digit c := rfl

theorem fold_map : ∀ (cs : List Char) (st : Array Nat × Nat), (∀ c ∈ cs, c.toNat < 128) →
    (cs.map fun c => UInt8.ofNat c.toNat).foldl (fun (st : Array Nat × Nat) b =>
      let d := digitOf b.toNat
      if d.2 then (st.1.push (st.2 * 32 + d.1), 0) else (st.1, st.2 * 32 + d.1)) st =
      cs.foldl step st
  | [], _, _ => rfl
  | c :: cs, st, h => by
    have hc : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      have := h c List.mem_cons_self
      have e : (UInt8.ofNat c.toNat).toNat = c.toNat % 256 := by simp
      rw [e]
      exact Nat.mod_eq_of_lt (by omega)
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hc]
    exact fold_map cs _ fun d hd => h d (List.mem_cons_of_mem c hd)

theorem decodeNats_ofList {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    decodeNats (String.ofList cs) = nats cs := by
  unfold decodeNats nats
  rw [byteArray_foldl_eq, toUTF8_toList h, fold_map cs _ h]

theorem decodePairs_ofList {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    decodePairs (String.ofList cs) = pairs cs := by
  unfold decodePairs pairs
  rw [decodeNats_ofList h]

end CFSG.KS.B32

end
