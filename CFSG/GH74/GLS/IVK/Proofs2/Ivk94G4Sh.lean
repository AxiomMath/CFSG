module

public import CFSG.GH74.GLS.Stage4.T2F1LocShapeO

public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open Subgroup

section InY

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Shape.eq_one_or_eq_z_of_central₁ (S : Shape Y F₁ F₂) {a : Y} (ha : a ∈ S.I₁)
    (hc : ∀ x ∈ S.I₁, a * x = x * a) : a = 1 ∨ a = S.z := by
  have hcen : S.e₁ ⟨a, ha⟩ ∈ Subgroup.center SL(2, F₁) := by
    rw [Subgroup.mem_center_iff]
    intro X
    obtain ⟨x, rfl⟩ := S.e₁.surjective X
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc x x.2).symm
  rcases eq_one_or_neg_one_of_mem_center hcen with h | h
  · left
    have h1 : (⟨a, ha⟩ : ↥S.I₁) = 1 := S.e₁.injective (h.trans (map_one S.e₁).symm)
    exact congrArg Subtype.val h1
  · right
    have h1 : (⟨a, ha⟩ : ↥S.I₁) = ⟨S.z, S.z_mem₁⟩ := S.e₁.injective (h.trans S.e₁_z.symm)
    exact congrArg Subtype.val h1

theorem Shape.eq_one_or_eq_z_of_central₂ (S : Shape Y F₁ F₂) {b : Y} (hb : b ∈ S.I₂)
    (hc : ∀ x ∈ S.I₂, b * x = x * b) : b = 1 ∨ b = S.z := by
  have hcen : S.e₂ ⟨b, hb⟩ ∈ Subgroup.center SL(2, F₂) := by
    rw [Subgroup.mem_center_iff]
    intro X
    obtain ⟨x, rfl⟩ := S.e₂.surjective X
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc x x.2).symm
  rcases eq_one_or_neg_one_of_mem_center hcen with h | h
  · left
    have h1 : (⟨b, hb⟩ : ↥S.I₂) = 1 := S.e₂.injective (h.trans (map_one S.e₂).symm)
    exact congrArg Subtype.val h1
  · right
    have h1 : (⟨b, hb⟩ : ↥S.I₂) = ⟨S.z, S.z_mem₂⟩ := S.e₂.injective (h.trans S.e₂_z.symm)
    exact congrArg Subtype.val h1

theorem Shape.eq_one_or_eq_z_of_centralizes (S : Shape Y F₁ F₂) {c : Y}
    (hc₁ : ∀ x ∈ S.I₁, c * x = x * c) (hc₂ : ∀ x ∈ S.I₂, c * x = x * c) : c = 1 ∨ c = S.z := by
  have hI₁ : S.I₁.Normal := S.normal₁
  have hI₂ : S.I₂.Normal := S.normal₂
  have hnt : S.t ∉ S.I₁ ⊔ Subgroup.centralizer (S.I₁ : Set Y) :=
    S.act₁.t_not_mem_sup (L := Subgroup.centralizer (S.I₁ : Set Y))
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp hb) a ha) S.ns₁
  have hI₂L : S.I₂ ≤ Subgroup.centralizer (S.I₁ : Set Y) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => S.comm a ha b hb
  have hJ : (S.I₁ ⊔ S.I₂).Normal := inferInstance
  have hcJ : c ∈ S.I₁ ⊔ S.I₂ := by
    rcases mem_or_inv_mul_mem_of_sup_zpowers_eq_top (J := S.I₁ ⊔ S.I₂) S.t_sq S.gen c with h | h
    · exact h
    · exfalso
      apply hnt
      have hcL : c ∈ Subgroup.centralizer (S.I₁ : Set Y) :=
        Subgroup.mem_centralizer_iff.mpr fun a ha => (hc₁ a ha).symm
      have hJle : S.I₁ ⊔ S.I₂ ≤ S.I₁ ⊔ Subgroup.centralizer (S.I₁ : Set Y) :=
        sup_le le_sup_left (hI₂L.trans le_sup_right)
      have ht : S.t = c * (c⁻¹ * S.t) := by group
      rw [ht]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcL) (hJle h)
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hcJ
  have ha' : a = 1 ∨ a = S.z := by
    refine S.eq_one_or_eq_z_of_central₁ ha fun x hx => ?_
    have h2 : b * x = x * b := (S.comm x hx b hb).symm
    have h3 : a * x * b = x * a * b := by
      calc a * x * b = a * (x * b) := by rw [mul_assoc]
        _ = a * (b * x) := by rw [h2]
        _ = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := hc₁ x hx
        _ = x * a * b := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hb' : b = 1 ∨ b = S.z := by
    refine S.eq_one_or_eq_z_of_central₂ hb fun x hx => ?_
    have h2 : a * x = x * a := S.comm a ha x hx
    have h3 : a * (b * x) = a * (x * b) := by
      calc a * (b * x) = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := hc₂ x hx
        _ = x * a * b := by rw [mul_assoc]
        _ = a * x * b := by rw [h2]
        _ = a * (x * b) := by rw [mul_assoc]
    exact mul_left_cancel h3
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · left; exact mul_one 1
  · right; exact one_mul _
  · right; exact mul_one _
  · left; exact S.z_sq

end InY

section InAmbient

variable {H : Type} [Group H] {Y₀ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (S : Shape ↥Y₀ F₁ F₂)

@[expose] def Shape.J₁ : Subgroup H := S.I₁.map Y₀.subtype

@[expose] def Shape.J₂ : Subgroup H := S.I₂.map Y₀.subtype

theorem Shape.J₁_le : S.J₁ ≤ Y₀ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem Shape.J₂_le : S.J₂ ≤ Y₀ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem Shape.zH_mem_J₁ : (S.z : H) ∈ S.J₁ := ⟨S.z, S.z_mem₁, rfl⟩

theorem Shape.zH_ne_one : (S.z : H) ≠ 1 := fun h => S.z_ne (Subtype.ext h)

theorem Shape.J_comm : ∀ x ∈ S.J₁, ∀ y ∈ S.J₂, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (S.comm a ha b hb)

theorem Shape.J_inf : S.J₁ ⊓ S.J₂ = zpowers (S.z : H) := by
  unfold Shape.J₁ Shape.J₂
  rw [← Subgroup.map_inf_eq _ _ _ Y₀.subtype_injective, S.inter, MonoidHom.map_zpowers]
  rfl

@[expose] noncomputable def Shape.J₁Equiv : ↥S.J₁ ≃* SL(2, F₁) :=
  (Subgroup.equivMapOfInjective S.I₁ Y₀.subtype Y₀.subtype_injective).symm.trans S.e₁

@[expose] noncomputable def Shape.J₂Equiv : ↥S.J₂ ≃* SL(2, F₂) :=
  (Subgroup.equivMapOfInjective S.I₂ Y₀.subtype Y₀.subtype_injective).symm.trans S.e₂

theorem Shape.J₁_conj : ∀ y ∈ Y₀, ∀ x ∈ S.J₁, y * x * y⁻¹ ∈ S.J₁ := by
  intro y hy x hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹, S.normal₁.conj_mem a ha ⟨y, hy⟩, rfl⟩

theorem Shape.J₂_conj : ∀ y ∈ Y₀, ∀ x ∈ S.J₂, y * x * y⁻¹ ∈ S.J₂ := by
  intro y hy x hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹, S.normal₂.conj_mem a ha ⟨y, hy⟩, rfl⟩

theorem Shape.eq_one_or_eq_zH_of_centralizes {c : H} (hc : c ∈ Y₀)
    (h₁ : ∀ x ∈ S.J₁, c * x = x * c) (h₂ : ∀ x ∈ S.J₂, c * x = x * c) :
    c = 1 ∨ c = (S.z : H) := by
  rcases S.eq_one_or_eq_z_of_centralizes (c := (⟨c, hc⟩ : ↥Y₀))
      (fun x hx => Subtype.ext (h₁ x ⟨x, hx, rfl⟩))
      (fun x hx => Subtype.ext (h₂ x ⟨x, hx, rfl⟩)) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem Shape.J₁_quasisimple [Finite F₁] (h4 : 4 ≤ Nat.card F₁) : CFSG.IsQuasisimple ↥S.J₁ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv S.J₁Equiv.symm
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)

theorem Shape.J₂_quasisimple [Finite F₂] (h4 : 4 ≤ Nat.card F₂) : CFSG.IsQuasisimple ↥S.J₂ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv S.J₂Equiv.symm
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)

end InAmbient

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
