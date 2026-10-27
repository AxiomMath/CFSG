module

public import CFSG.Certificates.Kernel.SporSch.McLSylowSound
public import CFSG.Certificates.Kernel.SporSch.ChainKZTot
public import CFSG.Certificates.Kernel.SporSch.PairBTSound

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

theorem chainK_of_chainS (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) :
    ∃ bv : Vector (Fin n) nb, bv.toList.Nodup ∧
      ChainK n w [gA, gB] D bv PS PSI LR TR TRI kS BP NS CH ∧ strongArr n w kS PS = S ∧
        CFSG.KS.SporSch.MOC.baseArr w nb BP = base ∧
        bv.toList.map Fin.val = base.toList := by
  obtain ⟨hb, hh, hl, hNS, hs⟩ := hQ
  have hbl := Orb.base_lt_of_levels hb hl
  have hpt : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hb.2.2.2.2.2.2 t ht]
    exact hbl t ht
  have hbase : (List.range nb).map (pg w (mask w) BP) = base.toList := by
    apply List.ext_getElem (by simp [hb.2.2.2.2.2.1])
    intro i h1 h2
    have hi : i < nb := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [← hb.2.2.2.2.2.2 i hi, getElem!_pos base i (by rw [hb.2.2.2.2.2.1]; exact hi)]
  let bv : Vector (Fin n) nb := Vector.ofFn fun i => ⟨pg w (mask w) BP i, hpt i i.2⟩
  have hbvm : bv.toList.map Fin.val = (List.range nb).map (pg w (mask w) BP) := by
    apply List.ext_getElem (by simp [bv])
    intro i h1 h2
    simp [bv]
  refine ⟨bv, ?_, ⟨hb.1, hb.2.1, hb.2.2.1, fun j hj => ?_, hbvm, hh, hl, hNS, hs⟩, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map Fin.val
    rw [hbvm, hbase]
    exact hnd
  · have hj2 : j < 2 := hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact hA
    · exact hB
  · apply Array.ext
    · rw [hb.2.2.2.1]
      simp [strongArr]
    · intro j h1 h2
      have hj : j < kS := by simpa [strongArr] using h1
      rw [← getElem!_pos S j h2, hb.2.2.2.2.1 j hj]
      simp [strongArr]
  · apply Array.ext
    · rw [hb.2.2.2.2.2.1]
      simp [CFSG.KS.SporSch.MOC.baseArr]
    · intro t h1 h2
      have ht : t < nb := by simpa [CFSG.KS.SporSch.MOC.baseArr] using h1
      rw [← getElem!_pos base t h2, hb.2.2.2.2.2.2 t ht]
      simp [CFSG.KS.SporSch.MOC.baseArr]
  · rw [hbvm, hbase]

theorem chainS_card_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) :
    Nat.card (gen2 gA gB) = ordK LR nb := by
  obtain ⟨bv, hbv, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have hn : 1 ≤ n := hQ.1.1
  have h := chainK_check hn hbv hK
  rw [gen2, ← orig_pair hn hbv (words := D), ← RawSchreierDatum.orderCertificate_eq_card _ h.1, h.2]

theorem chainS_mem_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup)
    {g : Equiv.Perm (Fin n)} {X : Nat}
    (hX : imageList g = (unpack n w X).toList) (hc : canonK n w (mask w) (n * w) X = true)
    (hs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 X = true) :
    g ∈ gen2 gA gB := by
  obtain ⟨bv, hbv, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have hn : 1 ≤ n := hQ.1.1
  rw [gen2, ← orig_pair hn hbv (words := D)]
  exact ((certificate hn [gA, gB] D bv hbv).sift_eq_true_iff_mem_original
    (chainK_check hn hbv hK).1 g).1 (chainK_sift hn hbv hK hX hc hs)

theorem chainS_elem_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {X : Nat}
    (hc : canonK n w (mask w) (n * w) X = true)
    (hs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 X = true) :
    ∃ g : gen2 gA gB, imageList (g : Equiv.Perm (Fin n)) = (unpack n w X).toList := by
  obtain ⟨bv, hbv, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  obtain ⟨r, pr⟩ := prep_of_siftK hK nb 0 (Nat.zero_add nb) X
    (fun j hj => (PF.canon_facts hc).2.2.2 j hj) hs
  have hr := imageList_of_prep pr
  exact ⟨⟨r, chainS_mem_proved hQ hA hB hnd hr hc hs⟩, hr⟩

theorem chainS_card (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) :
    Nat.card (gen2 gA gB) = ordK LR nb :=
  chainS_card_proved hQ hA hB hnd

theorem chainS_mem (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup)
    {g : Equiv.Perm (Fin n)} {X : Nat}
    (hX : imageList g = (unpack n w X).toList) (hc : canonK n w (mask w) (n * w) X = true)
    (hs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 X = true) :
    g ∈ gen2 gA gB :=
  chainS_mem_proved hQ hA hB hnd hX hc hs

theorem chainS_elem (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {X : Nat}
    (hc : canonK n w (mask w) (n * w) X = true)
    (hs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 X = true) :
    ∃ g : gen2 gA gB, imageList (g : Equiv.Perm (Fin n)) = (unpack n w X).toList :=
  chainS_elem_proved hQ hA hB hnd hc hs

end CFSG.KS.SporSch.MBT

end
