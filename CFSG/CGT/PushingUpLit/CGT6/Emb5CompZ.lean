module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompY

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

variable {Γ : Type*} [Group Γ]

theorem le_or_commute_of_normal {L P : Subgroup Γ} [L.Normal] [P.Normal]
    (hL : CFSG.IsQuasisimple ↥L) {y : Γ} (hy : y ∈ P) :
    L ≤ P ∨ ∀ l ∈ L, l * y = y * l := by
  have hE : (P.comap L.subtype).Normal := Subgroup.Normal.comap inferInstance _
  rcases normal_le_center_or_eq_top hL (P.comap L.subtype) with hc | htop
  · right
    let α : ↥L →* ↥L :=
      MonoidHom.mk' (fun l => ⟨y * l * y⁻¹, (Subgroup.Normal.conj_mem ‹L.Normal› l l.2 y)⟩) (by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group)
    have hcentral : ∀ q : ↥L, q * (α q)⁻¹ ∈ Subgroup.center ↥L := by
      intro q
      apply hc
      show ((q * (α q)⁻¹ : ↥L) : Γ) ∈ P
      have e : ((q * (α q)⁻¹ : ↥L) : Γ) = (q * y * q⁻¹) * y⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        show (q : Γ) * (y * q * y⁻¹)⁻¹ = (q : Γ) * y * (q : Γ)⁻¹ * y⁻¹
        group
      rw [e]
      exact P.mul_mem (Subgroup.Normal.conj_mem ‹P.Normal› y hy q) (P.inv_mem hy)
    have hid := hom_apply_eq_of_central hL.1 α hcentral
    intro l hl
    have h2 : y * l * y⁻¹ = l := congrArg Subtype.val (hid ⟨l, hl⟩)
    calc l * y = (y * l * y⁻¹) * y := by rw [h2]
      _ = y * l := by group
  · left
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ P.comap L.subtype := by rw [htop]; exact Subgroup.mem_top _
    exact this

end CFSG.CGT.PushingUpLit.CGT6
