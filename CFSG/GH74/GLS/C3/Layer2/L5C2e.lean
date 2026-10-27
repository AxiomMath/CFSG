module

public import CFSG.GH74.GLS.C3.Layer2.L5C2d

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

@[expose] def codeP16 (p : Perm (Fin 16)) : Nat :=
  (List.finRange 16).foldl (fun acc i => acc * 16 + (p i).val) 0

variable {M : Type} [Group M]

@[expose] def engOf
    (D : TabData M) (emb : ↥T5 →* M) : Eng D.n :=
  letI := D.grp
  mkEng (D.iso.toMonoidHom.comp emb)

theorem mem_engOf_invs
    (D : TabData M) (emb : ↥T5 →* M) (u : Idx D.n) :
    letI := D.grp
    u ∈ (engOf D emb).invs ↔ isInv u = true := by
  let _ := D.grp
  show u ∈ (elemsI D.n).filter isInv ↔ _
  simp [mem_elemsI]

theorem isInv_idx (D : TabData M) (a : M) :
    letI := D.grp
    isInv (D.idx a) = true ↔ a * a = 1 ∧ a ≠ 1 := by
  let _ := D.grp
  rw [isInv_iff]
  have h1 : D.idx a * D.idx a = D.idx (a * a) := (map_mul D.iso a a).symm
  have h2 : (1 : Idx D.n) = D.idx 1 := (map_one D.iso).symm
  rw [h1, h2]
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨D.iso.injective h3, fun h => h4 (by rw [h])⟩
  · rintro ⟨h3, h4⟩
    exact ⟨by rw [h3], fun h => h4 (D.iso.injective h)⟩

theorem fusion_blocks
    [Finite M] {E : M → M → Prop} {emb : ↥T5 →* M} (h : FusionHyp M emb E)
    (D : TabData M) (hok : letI := D.grp; engOK (engOf D emb) = true) :
    letI := D.grp
    ∃ ld ∈ survivors (engOf D emb), ∀ a b : M, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      (E a b ↔ blkOf (engOf D emb).ciA ld (D.idx a) = blkOf (engOf D emb).ciA ld (D.idx b)) := by
  let _ := D.grp
  have h' := h.transport D.iso
  obtain ⟨ld, hld, hfeas, hblk⟩ := fusion_core h' hok
  refine ⟨ld, List.mem_filter.2 ⟨hld, hfeas⟩, fun a b ha ha1 hb hb1 => ?_⟩
  have := hblk (D.idx a) (D.idx b) ((isInv_idx D a).2 ⟨ha, ha1⟩) ((isInv_idx D b).2 ⟨hb, hb1⟩)
  have e1 : D.iso.symm (D.idx a) = a := D.iso.symm_apply_apply a
  have e2 : D.iso.symm (D.idx b) = b := D.iso.symm_apply_apply b
  have this' : E (D.iso.symm (D.idx a)) (D.iso.symm (D.idx b)) ↔
      blkOf (mkEng (D.iso.toMonoidHom.comp emb)).ciA ld (D.idx a) =
        blkOf (mkEng (D.iso.toMonoidHom.comp emb)).ciA ld (D.idx b) := this
  rw [e1, e2] at this'
  exact this'

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
