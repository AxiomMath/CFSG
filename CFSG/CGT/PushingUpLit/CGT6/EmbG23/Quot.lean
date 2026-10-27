module

public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Lift

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbG23

open scoped commutatorElement

variable {H : Type*} [Group H]

@[expose] def conjOn (L : Subgroup H) (t : H) (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L) : MulAut ↥L where
  toFun x := ⟨t * x * t⁻¹, (ht x).1 x.2⟩
  invFun x := ⟨t⁻¹ * x * t, by
    have h := (ht (t⁻¹ * x * t)).2 (by simp [mul_assoc])
    exact h⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjOn_coe (L : Subgroup H) (t : H) (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L) (x : ↥L) :
    ((conjOn L t ht x : ↥L) : H) = t * x * t⁻¹ := rfl

@[expose] def quotAut (L : Subgroup H) (t : H) (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L) :
    MulAut (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjOn L t ht)
    (Subgroup.map_center_eq (conjOn L t ht))

theorem quotAut_mk (L : Subgroup H) (t : H) (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L) (x : ↥L) :
    quotAut L t ht (QuotientGroup.mk x) = QuotientGroup.mk (conjOn L t ht x) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem quotAut_mul_self (L : Subgroup H) (t : H) (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L)
    (htt : t * t = 1) : quotAut L t ht * quotAut L t ht = 1 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    show quotAut L t ht (quotAut L t ht (QuotientGroup.mk x)) = QuotientGroup.mk x
    rw [quotAut_mk, quotAut_mk]
    congr 1
    apply Subtype.ext
    simp only [conjOn_coe, hti]
    calc t * (t * (x : H) * t) * t = (t * t) * x * (t * t) := by simp only [mul_assoc]
      _ = x := by rw [htt]; simp

theorem quotAut_not_inner (L : Subgroup H) [Group.IsPerfect ↥L] (t : H)
    (ht : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L) {G : Subgroup H} (hLG : L ≤ G) (htG : t ∈ G)
    (hC : ∀ c ∈ G, (∀ x ∈ L, c * x = x * c) → c ∈ L) (htL : t ∉ L) :
    quotAut L t ht ∉ (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →*
      MulAut (↥L ⧸ Subgroup.center ↥L)).range := by
  rintro ⟨q, hq⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hB : ∀ x : ↥L, ∃ z ∈ Subgroup.center ↥L,
      (l⁻¹ * conjOn L t ht x * l : ↥L) = x * z := by
    intro x
    have h1 := congrArg (fun γ => γ (QuotientGroup.mk x)) hq
    simp only [MulAut.conj_apply, quotAut_mk] at h1
    have h2 : (QuotientGroup.mk (l⁻¹ * conjOn L t ht x * l) : ↥L ⧸ Subgroup.center ↥L) =
        QuotientGroup.mk x := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← h1]
      group
    refine ⟨x⁻¹ * (l⁻¹ * conjOn L t ht x * l), QuotientGroup.eq.1 h2.symm, by group⟩
  let B : MulAut ↥L := (MulAut.conj l)⁻¹ * conjOn L t ht
  have hBx : ∀ x : ↥L, B x = l⁻¹ * conjOn L t ht x * l := by
    intro x
    simp [B, MulAut.mul_apply, MulAut.inv_apply]
  have hBcomm : ∀ x y : ↥L, B ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    obtain ⟨z, hz, hzx⟩ := hB x
    obtain ⟨w, hw, hwy⟩ := hB y
    rw [map_commutatorElement, hBx, hBx, hzx, hwy, commutator_mul_central hz hw]
  have hBfix : ∀ x : ↥L, B x = x := by
    have hle : commutator ↥L ≤ B.toMonoidHom.eqLocus (MonoidHom.id ↥L) := by
      rw [commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨g₁, -, g₂, -, rfl⟩
      exact hBcomm g₁ g₂
    intro x
    have hx : x ∈ commutator ↥L := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top x
    exact hle hx
  have hcomm : ∀ x ∈ L, ((l : H)⁻¹ * t) * x = x * ((l : H)⁻¹ * t) := by
    intro x hx
    have h := hBfix ⟨x, hx⟩
    rw [hBx] at h
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjOn_coe] at h'
    calc (l : H)⁻¹ * t * x = ((l : H)⁻¹ * (t * x * t⁻¹) * l) * ((l : H)⁻¹ * t) := by group
      _ = x * ((l : H)⁻¹ * t) := by rw [h']
  have hcL : (l : H)⁻¹ * t ∈ L :=
    hC _ (G.mul_mem (G.inv_mem (hLG l.2)) htG) hcomm
  apply htL
  have := L.mul_mem l.2 hcL
  simpa using this

end CFSG.CGT.PushingUpLit.CGT6.EmbG23
