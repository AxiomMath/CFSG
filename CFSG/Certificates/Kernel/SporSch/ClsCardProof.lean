module

public import CFSG.Certificates.Kernel.SporSch.ChainSProof

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem isConj_iff_mem (r x : gen2 gA gB) :
    IsConj r x ↔ (x : Equiv.Perm (Fin n)) ∈
      CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB) (r : Equiv.Perm (Fin n)) := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by simp⟩
  · rintro ⟨c, hc, e⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (by simp [e])⟩

theorem card_isConj_eq_ncard (r : gen2 gA gB) :
    #(univ.filter fun x : gen2 gA gB => IsConj r x) =
      (CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB) (r : Equiv.Perm (Fin n))).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext z
  simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (isConj_iff_mem r x).1 hx
  · intro hz
    obtain ⟨c, hc, rfl⟩ := hz
    refine ⟨⟨c * r * c⁻¹, (gen2 gA gB).mul_mem ((gen2 gA gB).mul_mem hc r.2)
      ((gen2 gA gB).inv_mem hc)⟩, (isConj_iff_mem _ _).2 ⟨c, hc, rfl⟩, rfl⟩

theorem clsCard_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {mx cap : Nat}
    {d : ClsD} (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList mx cap [d])
    (r : gen2 gA gB) (hR : imageList (r : Equiv.Perm (Fin n)) = (unpack n w d.R).toList) :
    #(univ.filter fun x : gen2 gA gB => IsConj r x) = d.c := by
  obtain ⟨bv, -, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have hc := datum_class hK hA.symm hB.symm hcls (j := 0) (by simp) (prep_of_imageList hR)
  rw [card_isConj_eq_ncard]
  exact hc.2.1

theorem clsCard_sound (_hsz : szOK n w = true) {tA tB : List Nat} (hA : imageList gA = tA)
    (hB : imageList gB = tB) (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (htA : tA = (unpack n w (PS 0)).toList) (htB : tB = (unpack n w (PS 1)).toList)
    (hnd : base.toList.Nodup) {mx cap : Nat} {d : ClsD} (hcls : ClsOK n w tA tB mx cap [d])
    (r : gen2 gA gB) (hR : imageList (r : Equiv.Perm (Fin n)) = (unpack n w d.R).toList) :
    #(univ.filter fun x : gen2 gA gB => IsConj r x) = d.c := by
  subst htA htB
  exact clsCard_proved hQ hA hB hnd hcls r hR

end CFSG.KS.SporSch.MBT

end
