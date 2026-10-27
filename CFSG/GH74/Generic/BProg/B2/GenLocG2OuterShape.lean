module

import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups commutatorElement Pointwise

namespace GenLocG2OuterShape

section Helpers
variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := N ⊔ H)
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := H)
  rw [Subgroup.relIndex_sup_left] at h1
  rw [inf_eq_left.2 (le_sup_left : N ≤ N ⊔ H)] at h1
  rw [sup_comm] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem commutator_mul_of_commute {c₁ c₂ a₁ a₂ : G} (h₁ : Commute c₁ a₁) (h₂ : Commute c₁ a₂)
    (h₃ : Commute c₂ a₁) (h₄ : Commute c₂ a₂) (h₅ : Commute c₁ c₂) :
    ⁅c₁ * a₁, c₂ * a₂⁆ = ⁅a₁, a₂⁆ := by
  have k1 : c₁ * (a₁ * c₂ * a₂) * c₁⁻¹ = a₁ * c₂ * a₂ := by
    have hc : Commute c₁ (a₁ * c₂ * a₂) := (h₁.mul_right h₅).mul_right h₂
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have k2 : c₂ * (a₂ * a₁⁻¹) * c₂⁻¹ = a₂ * a₁⁻¹ := by
    have hc : Commute c₂ (a₂ * a₁⁻¹) := h₄.mul_right h₃.inv_right
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have i1 : (c₁ * a₁)⁻¹ = c₁⁻¹ * a₁⁻¹ := by rw [mul_inv_rev, (h₁.inv_inv).eq]
  have i2 : (c₂ * a₂)⁻¹ = c₂⁻¹ * a₂⁻¹ := by rw [mul_inv_rev, (h₄.inv_inv).eq]
  calc ⁅c₁ * a₁, c₂ * a₂⁆ = c₁ * (a₁ * c₂ * a₂) * c₁⁻¹ * (a₁⁻¹ * c₂⁻¹ * a₂⁻¹) := by
        rw [commutatorElement_def, i1, i2]; group
    _ = (a₁ * c₂ * a₂) * (a₁⁻¹ * c₂⁻¹ * a₂⁻¹) := by rw [k1]
    _ = a₁ * (c₂ * (a₂ * a₁⁻¹) * c₂⁻¹) * a₂⁻¹ := by group
    _ = ⁅a₁, a₂⁆ := by rw [k2, commutatorElement_def]; group

end Helpers

section ShapeLemmas
variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem mem_E_or (y : Y) : y ∈ S.I₁ ⊔ S.I₂ ∨ y * S.t ∈ S.I₁ ⊔ S.I₂ := by
  have := S.normal₁
  have := S.normal₂
  have hy : y ∈ S.I₁ ⊔ S.I₂ ⊔ zpowers S.t := by rw [S.gen]; trivial
  have h := Subgroup.normal_mul (S.I₁ ⊔ S.I₂) (zpowers S.t)
  have hy' : y ∈ ((S.I₁ ⊔ S.I₂ : Subgroup Y) : Set Y) * ((zpowers S.t : Subgroup Y) : Set Y) := by
    rw [← h]; exact hy
  obtain ⟨e, he, s, hs, rfl⟩ := hy'
  rcases mem_zpowers_of_sq S.t_sq hs with rfl | rfl
  · left; simpa using he
  · right
    have : e * S.t * S.t = e := by rw [mul_assoc, S.t_sq, mul_one]
    rw [this]; exact he

theorem t_comm_z : S.t * S.z = S.z * S.t := by
  obtain ⟨y, hy, hey⟩ := S.act₁ ⟨S.z, S.z_mem₁⟩
  rw [S.e₁_z] at hey
  have hy' : y = ⟨S.z, S.z_mem₁⟩ := by
    apply S.e₁.injective
    rw [S.e₁_z]
    apply Subtype.ext
    rw [hey]
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have : (y : Y) = S.z := congrArg Subtype.val hy'
  rw [this] at hy
  calc S.t * S.z = (S.t * S.z * S.t⁻¹) * S.t := by group
    _ = S.z * S.t := by rw [← hy]

theorem mem_zpowers_z_of_central₁ {a : Y} (ha : a ∈ S.I₁) (h : ∀ x ∈ S.I₁, a * x = x * a) :
    a ∈ zpowers S.z := by
  have hc : S.e₁ ⟨a, ha⟩ ∈ Subgroup.center SL(2, F₁) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨x, rfl⟩ := S.e₁.surjective B
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h x x.2).symm
  rcases eq_one_or_neg_one_of_mem_center hc with h1 | h1
  · have h2 : (⟨a, ha⟩ : ↥S.I₁) = 1 := S.e₁.injective (by rw [h1, map_one])
    have : a = 1 := congrArg Subtype.val h2
    rw [this]; exact one_mem _
  · have h2 : (⟨a, ha⟩ : ↥S.I₁) = ⟨S.z, S.z_mem₁⟩ := S.e₁.injective (by rw [h1, S.e₁_z])
    have : a = S.z := congrArg Subtype.val h2
    rw [this]; exact mem_zpowers _

theorem mem_zpowers_z_of_central₂ {a : Y} (ha : a ∈ S.I₂) (h : ∀ x ∈ S.I₂, a * x = x * a) :
    a ∈ zpowers S.z := by
  have hc : S.e₂ ⟨a, ha⟩ ∈ Subgroup.center SL(2, F₂) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨x, rfl⟩ := S.e₂.surjective B
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h x x.2).symm
  rcases eq_one_or_neg_one_of_mem_center hc with h1 | h1
  · have h2 : (⟨a, ha⟩ : ↥S.I₂) = 1 := S.e₂.injective (by rw [h1, map_one])
    have : a = 1 := congrArg Subtype.val h2
    rw [this]; exact one_mem _
  · have h2 : (⟨a, ha⟩ : ↥S.I₂) = ⟨S.z, S.z_mem₂⟩ := S.e₂.injective (by rw [h1, S.e₂_z])
    have : a = S.z := congrArg Subtype.val h2
    rw [this]; exact mem_zpowers _

theorem false_of_t_inner₁ {a : Y} (ha : a ∈ S.I₁) (h : ∀ x ∈ S.I₁, S.t * x * S.t⁻¹ = a * x * a⁻¹) :
    False := by
  apply S.ns₁
  refine isSquare_det_of_conjSLAut_eq S.g₁ (S.e₁ ⟨a, ha⟩) fun X => ?_
  obtain ⟨x, rfl⟩ := S.e₁.surjective X
  have h' := conjData_iff.1 S.act₁
  obtain ⟨y, hy, hey⟩ := h' x
  have hy2 : y = ⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹ := by
    apply Subtype.ext
    rw [hy, h x x.2]
    simp
  rw [← hey, hy2]
  simp [map_mul, map_inv]

theorem cent_E {w : Y} (hw : ∀ x ∈ S.I₁ ⊔ S.I₂, w * x = x * w) : w ∈ zpowers S.z := by
  have hw1 : ∀ x ∈ S.I₁, w * x = x * w := fun x hx => hw x (Subgroup.mem_sup_left hx)
  have hw2 : ∀ x ∈ S.I₂, w * x = x * w := fun x hx => hw x (Subgroup.mem_sup_right hx)
  rcases mem_E_or S w with hE | hE
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hE
    have ha' : ∀ x ∈ S.I₁, a * x = x * a := by
      intro x hx
      have h1 := hw1 x hx
      have hbx : b * x = x * b := (S.comm x hx b hb).symm
      refine mul_right_cancel (b := b) ?_
      calc a * x * b = a * (x * b) := by rw [mul_assoc]
        _ = a * (b * x) := by rw [hbx]
        _ = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := h1
        _ = x * a * b := by rw [mul_assoc]
    have hb' : ∀ x ∈ S.I₂, b * x = x * b := by
      intro x hx
      have h1 := hw2 x hx
      have hax : a * x = x * a := S.comm a ha x hx
      refine mul_left_cancel (a := a) ?_
      calc a * (b * x) = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := h1
        _ = x * a * b := by rw [mul_assoc]
        _ = a * x * b := by rw [hax]
        _ = a * (x * b) := by rw [mul_assoc]
    exact mul_mem (mem_zpowers_z_of_central₁ S ha ha') (mem_zpowers_z_of_central₂ S hb hb')
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute S.comm hE
    refine false_of_t_inner₁ S ha fun x hx => ?_
    have ht : S.t = w⁻¹ * (a * b) := by rw [hab]; group
    have hb1 : b * x = x * b := (S.comm x hx b hb).symm
    have hwx : ∀ y ∈ S.I₁, w⁻¹ * y * w = y := by
      intro y hy
      have := hw1 y hy
      calc w⁻¹ * y * w = w⁻¹ * (y * w) := by rw [mul_assoc]
        _ = w⁻¹ * (w * y) := by rw [this]
        _ = y := by group
    have hax : a * x * a⁻¹ ∈ S.I₁ := mul_mem (mul_mem ha hx) (inv_mem ha)
    have hbx : b * x * b⁻¹ = x := by rw [hb1]; group
    calc S.t * x * S.t⁻¹ = w⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * w := by rw [ht]; group
      _ = w⁻¹ * (a * x * a⁻¹) * w := by rw [hbx]
      _ = a * x * a⁻¹ := hwx _ hax

theorem orderOf_four_of_sq {G : Type*} [Group G] {A m : G} (hA : A * A = m) (hm : m * m = 1)
    (hm1 : m ≠ 1) : orderOf A = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : A ^ 2 = m := by rw [sq]; exact hA
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := A) (by rw [pow_one, h2]; exact hm1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, sq]; exact hm)
  simpa using h

include S in
theorem two_ne_zero₁ : (2 : F₁) ≠ 0 := by
  intro h2
  apply S.z_ne
  have h1 : S.e₁ ⟨S.z, S.z_mem₁⟩ = 1 := by
    rw [S.e₁_z]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    have : (-1 : Matrix (Fin 2) (Fin 2) F₁) = 1 := by
      have h : (1 : Matrix (Fin 2) (Fin 2) F₁) + 1 = 0 := by
        rw [← two_smul F₁ (1 : Matrix (Fin 2) (Fin 2) F₁), h2, zero_smul]
      exact neg_eq_of_add_eq_zero_left h
    exact this
  have := S.e₁.injective (h1.trans (map_one S.e₁).symm)
  exact congrArg Subtype.val this

include S in
theorem two_ne_zero₂ : (2 : F₂) ≠ 0 := by
  intro h2
  apply S.z_ne
  have h1 : S.e₂ ⟨S.z, S.z_mem₂⟩ = 1 := by
    rw [S.e₂_z]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    have : (-1 : Matrix (Fin 2) (Fin 2) F₂) = 1 := by
      have h : (1 : Matrix (Fin 2) (Fin 2) F₂) + 1 = 0 := by
        rw [← two_smul F₂ (1 : Matrix (Fin 2) (Fin 2) F₂), h2, zero_smul]
      exact neg_eq_of_add_eq_zero_left h
    exact this
  have := S.e₂.injective (h1.trans (map_one S.e₂).symm)
  exact congrArg Subtype.val this

theorem sq_cases₁ {a : Y} (ha : a ∈ S.I₁) (h : a * a = 1) : a ∈ zpowers S.z := by
  by_cases h1 : a = 1
  · rw [h1]; exact one_mem _
  · have h2 := two_ne_zero₁ S
    have hA : (S.e₁ ⟨a, ha⟩) ^ 2 = 1 := by
      rw [← map_pow, sq]
      have : (⟨a, ha⟩ : ↥S.I₁) * ⟨a, ha⟩ = 1 := Subtype.ext h
      rw [this, map_one]
    have hA1 : S.e₁ ⟨a, ha⟩ ≠ 1 := fun h' =>
      h1 (congrArg Subtype.val (S.e₁.injective (h'.trans (map_one _).symm)))
    have h4 := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (S.e₁ ⟨a, ha⟩) hA hA1
    have h3 : S.e₁ ⟨a, ha⟩ = S.e₁ ⟨S.z, S.z_mem₁⟩ := by
      rw [S.e₁_z]
      apply Subtype.ext
      rw [h4, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    have : a = S.z := congrArg Subtype.val (S.e₁.injective h3)
    rw [this]; exact mem_zpowers _

theorem sq_cases₂ {a : Y} (ha : a ∈ S.I₂) (h : a * a = 1) : a ∈ zpowers S.z := by
  by_cases h1 : a = 1
  · rw [h1]; exact one_mem _
  · have h2 := two_ne_zero₂ S
    have hA : (S.e₂ ⟨a, ha⟩) ^ 2 = 1 := by
      rw [← map_pow, sq]
      have : (⟨a, ha⟩ : ↥S.I₂) * ⟨a, ha⟩ = 1 := Subtype.ext h
      rw [this, map_one]
    have hA1 : S.e₂ ⟨a, ha⟩ ≠ 1 := fun h' =>
      h1 (congrArg Subtype.val (S.e₂.injective (h'.trans (map_one _).symm)))
    have h4 := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (S.e₂ ⟨a, ha⟩) hA hA1
    have h3 : S.e₂ ⟨a, ha⟩ = S.e₂ ⟨S.z, S.z_mem₂⟩ := by
      rw [S.e₂_z]
      apply Subtype.ext
      rw [h4, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    have : a = S.z := congrArg Subtype.val (S.e₂.injective h3)
    rw [this]; exact mem_zpowers _

include S in
theorem neg_one_ne_one₁ : (-1 : SL(2, F₁)) ≠ 1 := by
  intro h
  apply S.z_ne
  have h1 : S.e₁ ⟨S.z, S.z_mem₁⟩ = 1 := by rw [S.e₁_z]; exact h
  exact congrArg Subtype.val (S.e₁.injective (h1.trans (map_one S.e₁).symm))

include S in
theorem neg_one_ne_one₂ : (-1 : SL(2, F₂)) ≠ 1 := by
  intro h
  apply S.z_ne
  have h1 : S.e₂ ⟨S.z, S.z_mem₂⟩ = 1 := by rw [S.e₂_z]; exact h
  exact congrArg Subtype.val (S.e₂.injective (h1.trans (map_one S.e₂).symm))

theorem exists_cent_not_mem_E
    (hL3₁ : ∀ A B : SL(2, F₁), orderOf A = 4 → orderOf B = 4 → IsConj A B)
    (hL3₂ : ∀ A B : SL(2, F₂), orderOf A = 4 → orderOf B = 4 → IsConj A B)
    {w : Y} (hw2 : w * w = 1) (hwz : w ∉ zpowers S.z) :
    ∃ y : Y, w * y = y * w ∧ y ∉ S.I₁ ⊔ S.I₂ := by
  by_cases hwE : w ∈ S.I₁ ⊔ S.I₂
  swap
  · exact ⟨w, rfl, hwE⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hwE
  have hab : a * b = b * a := S.comm a ha b hb
  have hsq : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = a * b * (a * b) := by group
      _ = 1 := hw2
  have hbb : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have haa_mem : a * a ∈ S.I₁ ⊓ S.I₂ := by
    refine ⟨mul_mem ha ha, ?_⟩
    have : b * b ∈ S.I₂ := mul_mem hb hb
    rw [hbb] at this
    exact (Subgroup.inv_mem_iff _).1 this
  rw [S.inter] at haa_mem
  have hz2 : S.z * S.z = 1 := S.z_sq
  rcases mem_zpowers_of_sq hz2 haa_mem with h1 | h1
  · exfalso
    apply hwz
    have hb1 : b * b = 1 := by rw [hbb, h1]; simp
    exact mul_mem (sq_cases₁ S ha h1) (sq_cases₂ S hb hb1)
  ·
    have hbz : b * b = S.z := by rw [hbb, h1]; exact inv_eq_of_mul_eq_one_right hz2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hta : S.t * a * S.t⁻¹ ∈ S.I₁ := S.act₁.conj_mem ha
    have htb : S.t * b * S.t⁻¹ ∈ S.I₂ := S.act₂.conj_mem hb
    have hta2 : S.t * a * S.t⁻¹ * (S.t * a * S.t⁻¹) = S.z := by
      calc S.t * a * S.t⁻¹ * (S.t * a * S.t⁻¹) = S.t * (a * a) * S.t⁻¹ := by group
        _ = S.t * S.z * S.t⁻¹ := by rw [h1]
        _ = S.z := by rw [t_comm_z S]; group
    have htb2 : S.t * b * S.t⁻¹ * (S.t * b * S.t⁻¹) = S.z := by
      calc S.t * b * S.t⁻¹ * (S.t * b * S.t⁻¹) = S.t * (b * b) * S.t⁻¹ := by group
        _ = S.t * S.z * S.t⁻¹ := by rw [hbz]
        _ = S.z := by rw [t_comm_z S]; group
    have ord1 : ∀ {c : Y} (hc : c ∈ S.I₁), c * c = S.z → orderOf (S.e₁ ⟨c, hc⟩) = 4 := by
      intro c hc hcc
      refine orderOf_four_of_sq (m := -1) ?_ (by simp) (neg_one_ne_one₁ S)
      rw [← map_mul, ← S.e₁_z]
      congr 1
      exact Subtype.ext hcc
    have ord2 : ∀ {c : Y} (hc : c ∈ S.I₂), c * c = S.z → orderOf (S.e₂ ⟨c, hc⟩) = 4 := by
      intro c hc hcc
      refine orderOf_four_of_sq (m := -1) ?_ (by simp) (neg_one_ne_one₂ S)
      rw [← map_mul, ← S.e₂_z]
      congr 1
      exact Subtype.ext hcc
    obtain ⟨c, hc⟩ := isConj_iff.1 (hL3₁ _ _ (ord1 ha h1) (ord1 hta hta2))
    obtain ⟨d, hd⟩ := isConj_iff.1 (hL3₂ _ _ (ord2 hb hbz) (ord2 htb htb2))
    set c' : Y := ((S.e₁.symm c : ↥S.I₁) : Y) with hc'
    set d' : Y := ((S.e₂.symm d : ↥S.I₂) : Y) with hd'
    have hc'mem : c' ∈ S.I₁ := (S.e₁.symm c).2
    have hd'mem : d' ∈ S.I₂ := (S.e₂.symm d).2
    have hca : c' * a * c'⁻¹ = S.t * a * S.t⁻¹ := by
      have := congrArg (fun x => ((S.e₁.symm x : ↥S.I₁) : Y)) hc
      simpa [hc'] using this
    have hdb : d' * b * d'⁻¹ = S.t * b * S.t⁻¹ := by
      have := congrArg (fun x => ((S.e₂.symm x : ↥S.I₂) : Y)) hd
      simpa [hd'] using this
    have key1 : (c'⁻¹ * d'⁻¹ * S.t) * a * (c'⁻¹ * d'⁻¹ * S.t)⁻¹ = a := by
      have hcomm : d'⁻¹ * (S.t * a * S.t⁻¹) * d' = S.t * a * S.t⁻¹ := by
        have := S.comm _ hta d' hd'mem
        calc d'⁻¹ * (S.t * a * S.t⁻¹) * d' = d'⁻¹ * ((S.t * a * S.t⁻¹) * d') := by rw [mul_assoc]
          _ = d'⁻¹ * (d' * (S.t * a * S.t⁻¹)) := by rw [this]
          _ = _ := by group
      calc (c'⁻¹ * d'⁻¹ * S.t) * a * (c'⁻¹ * d'⁻¹ * S.t)⁻¹
          = c'⁻¹ * (d'⁻¹ * (S.t * a * S.t⁻¹) * d') * c' := by group
        _ = c'⁻¹ * (S.t * a * S.t⁻¹) * c' := by rw [hcomm]
        _ = c'⁻¹ * (c' * a * c'⁻¹) * c' := by rw [hca]
        _ = a := by group
    have key2 : (c'⁻¹ * d'⁻¹ * S.t) * b * (c'⁻¹ * d'⁻¹ * S.t)⁻¹ = b := by
      have hcomm : c'⁻¹ * b * c' = b := by
        have := S.comm c' hc'mem b hb
        calc c'⁻¹ * b * c' = c'⁻¹ * (b * c') := by rw [mul_assoc]
          _ = c'⁻¹ * (c' * b) := by rw [this]
          _ = b := by group
      calc (c'⁻¹ * d'⁻¹ * S.t) * b * (c'⁻¹ * d'⁻¹ * S.t)⁻¹
          = c'⁻¹ * (d'⁻¹ * (S.t * b * S.t⁻¹) * d') * c' := by group
        _ = c'⁻¹ * (d'⁻¹ * (d' * b * d'⁻¹) * d') * c' := by rw [hdb]
        _ = c'⁻¹ * b * c' := by group
        _ = b := hcomm
    refine ⟨c'⁻¹ * d'⁻¹ * S.t, ?_, ?_⟩
    · have e1 : (c'⁻¹ * d'⁻¹ * S.t) * a = a * (c'⁻¹ * d'⁻¹ * S.t) := by
        calc (c'⁻¹ * d'⁻¹ * S.t) * a = ((c'⁻¹ * d'⁻¹ * S.t) * a * (c'⁻¹ * d'⁻¹ * S.t)⁻¹) *
            (c'⁻¹ * d'⁻¹ * S.t) := by group
          _ = a * (c'⁻¹ * d'⁻¹ * S.t) := by rw [key1]
      have e2 : (c'⁻¹ * d'⁻¹ * S.t) * b = b * (c'⁻¹ * d'⁻¹ * S.t) := by
        calc (c'⁻¹ * d'⁻¹ * S.t) * b = ((c'⁻¹ * d'⁻¹ * S.t) * b * (c'⁻¹ * d'⁻¹ * S.t)⁻¹) *
            (c'⁻¹ * d'⁻¹ * S.t) := by group
          _ = b * (c'⁻¹ * d'⁻¹ * S.t) := by rw [key2]
      calc a * b * (c'⁻¹ * d'⁻¹ * S.t) = a * (b * (c'⁻¹ * d'⁻¹ * S.t)) := mul_assoc _ _ _
        _ = a * ((c'⁻¹ * d'⁻¹ * S.t) * b) := by rw [e2]
        _ = (a * (c'⁻¹ * d'⁻¹ * S.t)) * b := (mul_assoc _ _ _).symm
        _ = ((c'⁻¹ * d'⁻¹ * S.t) * a) * b := by rw [e1]
        _ = (c'⁻¹ * d'⁻¹ * S.t) * (a * b) := mul_assoc _ _ _
    · intro hy
      apply S.t_not_mem
      have h3 : S.t = d' * c' * (c'⁻¹ * d'⁻¹ * S.t) := by group
      rw [h3]
      refine mul_mem (mul_mem (Subgroup.mem_sup_right hd'mem) (Subgroup.mem_sup_left hc'mem)) hy

end ShapeLemmas

section Twist

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem twist_le_aux (τ : MulAut Y) (hτ1 : ∀ x ∈ S.I₁, τ x ∈ S.I₂) (hτ2 : ∀ y ∈ S.I₂, τ y ∈ S.I₁)
    (hττ : ∀ y, τ (τ y) = y) {w : Y} (hw2 : w * w = 1) (hτw : τ w = w)
    (hq₂ : CFSG.IsQuasisimple ↥S.I₂) (hwnc : ¬ ∀ y ∈ S.I₂, w * y = y * w)
    {G1 G2 : Subgroup Y} (h1 : ∀ y, τ y = y → y ∈ G1) (h2 : ∀ y, w * τ y * w⁻¹ = y → y ∈ G2) :
    S.I₂ ≤ G1 ⊔ G2 := by
  have hn₂ := S.normal₂
  have hwI : ∀ y ∈ S.I₂, w * y * w⁻¹ ∈ S.I₂ := fun y hy => hn₂.conj_mem y hy w
  let T : Set Y := {c | ∃ y ∈ S.I₂, c = ⁅y, w⁆}
  let N : Subgroup Y := Subgroup.closure T
  have hTmem : ∀ y ∈ S.I₂, ⁅y, w⁆ ∈ G1 ⊔ G2 := by
    intro y hy
    obtain ⟨x, hx⟩ : ∃ x : Y, x = τ y⁻¹ := ⟨_, rfl⟩
    have hxI : x ∈ S.I₁ := hx ▸ hτ2 _ (inv_mem hy)
    have hτx : τ x = y⁻¹ := by rw [hx, hττ]
    have hτxI : τ x ∈ S.I₂ := hτ1 x hxI
    have hcomm := S.comm x hxI (τ x) hτxI
    have hd1 : x * τ x ∈ G1 := by
      apply h1
      rw [map_mul, hττ, hcomm]
    have hwτ : w * τ x * w⁻¹ ∈ S.I₂ := hwI _ hτxI
    have hd2 : x * (w * τ x * w⁻¹) ∈ G2 := by
      apply h2
      have hcomm2 := S.comm x hxI _ hwτ
      rw [map_mul, map_mul, map_mul, map_inv, hττ, hτw]
      calc w * (τ x * (w * x * w⁻¹)) * w⁻¹ = (w * τ x * w⁻¹) * (w * w * x * (w * w)⁻¹) := by group
        _ = (w * τ x * w⁻¹) * x := by rw [hw2]; group
        _ = x * (w * τ x * w⁻¹) := hcomm2.symm
    have e : (x * τ x)⁻¹ * (x * (w * τ x * w⁻¹)) = (τ x)⁻¹ * w * τ x * w⁻¹ := by group
    have : ⁅y, w⁆ = (x * τ x)⁻¹ * (x * (w * τ x * w⁻¹)) := by
      rw [e, hτx, commutatorElement_def]; group
    rw [this]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hd1)) (Subgroup.mem_sup_right hd2)
  have hNle : N ≤ G1 ⊔ G2 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨y, hy, rfl⟩
    exact hTmem y hy
  have hNI : N ≤ S.I₂ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨y, hy, rfl⟩
    rw [commutatorElement_def]
    have : y * w * y⁻¹ * w⁻¹ = y * (w * y⁻¹ * w⁻¹) := by group
    rw [this]
    exact mul_mem hy (hwI _ (inv_mem hy))
  have hNconj : ∀ u ∈ S.I₂, ∀ n ∈ N, u * n * u⁻¹ ∈ N := by
    intro u hu n hn
    have : N ≤ N.comap (MulAut.conj u).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro c ⟨y, hy, rfl⟩
      show u * ⁅y, w⁆ * u⁻¹ ∈ N
      have key : u * ⁅y, w⁆ * u⁻¹ = ⁅u * y, w⁆ * ⁅u, w⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [key]
      refine mul_mem (Subgroup.subset_closure ⟨u * y, mul_mem hu hy, rfl⟩) (inv_mem (Subgroup.subset_closure ⟨u, hu, rfl⟩))
    exact this hn
  have hN' : (N.subgroupOf S.I₂).Normal := by
    refine ⟨fun n hn u => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNconj u u.2 n hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq₂ hN' with htop | hcen
  · intro y hy
    have : (⟨y, hy⟩ : ↥S.I₂) ∈ N.subgroupOf S.I₂ := by rw [htop]; trivial
    exact hNle this
  · exfalso
    apply hwnc
    have hNc : N ≤ Subgroup.centralizer (S.I₂ : Set Y) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hcen (show (⟨n, hNI hn⟩ : ↥S.I₂) ∈ N.subgroupOf S.I₂ from hn)
      rw [Subgroup.mem_center_iff] at this
      have h3 := this ⟨u, hu⟩
      exact congrArg Subtype.val h3
    have hcc : ⁅S.I₂, Subgroup.zpowers w⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rcases mem_zpowers_of_sq hw2 hg₂ with rfl | rfl
      · simp
      · exact Subgroup.subset_closure ⟨g₁, hg₁, rfl⟩
    have hdc : ⁅⁅S.I₂, Subgroup.zpowers w⁆, S.I₂⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcc.trans hNc
    have hP : Group.IsPerfect ↥S.I₂ := hq₂.1
    have hfin := CFSG.LocalCores.perfect_double_commutator hP hdc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hfin
    intro y hy
    have := Subgroup.mem_centralizer_iff.1 (hfin hy) w (Subgroup.mem_zpowers w)
    exact this

theorem eq_top_of_E_le {H : Subgroup Y} (hE : S.I₁ ⊔ S.I₂ ≤ H) {y : Y} (hy : y ∈ H)
    (hyE : y ∉ S.I₁ ⊔ S.I₂) : H = ⊤ := by
  have htm : S.t ∈ H := by
    rcases mem_E_or S y with h | h
    · exact absurd h hyE
    · have : S.t = y⁻¹ * (y * S.t) := by group
      rw [this]
      exact mul_mem (inv_mem hy) (hE h)
  rw [eq_top_iff]
  intro g _
  rcases mem_E_or S g with h | h
  · exact hE h
  · have : g = (g * S.t) * S.t := by rw [mul_assoc, S.t_sq, mul_one]
    rw [this]
    exact mul_mem (hE h) htm

theorem twist_gen
    (hL3₁ : ∀ A B : SL(2, F₁), orderOf A = 4 → orderOf B = 4 → IsConj A B)
    (hL3₂ : ∀ A B : SL(2, F₂), orderOf A = 4 → orderOf B = 4 → IsConj A B)
    (hq₁ : CFSG.IsQuasisimple ↥S.I₁) (hq₂ : CFSG.IsQuasisimple ↥S.I₂)
    (τ : MulAut Y) (hτ1 : ∀ x ∈ S.I₁, τ x ∈ S.I₂) (hτ2 : ∀ y ∈ S.I₂, τ y ∈ S.I₁)
    (hττ : ∀ y, τ (τ y) = y) {w : Y} (hw2 : w * w = 1) (hτw : τ w = w) (hwz : w ∉ zpowers S.z)
    {G1 G2 G3 : Subgroup Y} (h1 : ∀ y, τ y = y → y ∈ G1) (h2 : ∀ y, w * τ y * w⁻¹ = y → y ∈ G2)
    (h3 : ∀ y, w * y = y * w → y ∈ G3) : G1 ⊔ G2 ⊔ G3 = ⊤ := by
  have hcentE : (∀ y ∈ S.I₂, w * y = y * w) → False := by
    intro h
    apply hwz
    refine cent_E S fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hx
    have ha' : w * a = a * w := by
      have := h (τ a) (hτ1 a ha)
      have h4 := congrArg τ this
      rwa [map_mul, map_mul, hττ, hτw] at h4
    have hb' : w * b = b * w := h b hb
    calc w * (a * b) = (w * a) * b := (mul_assoc _ _ _).symm
      _ = (a * w) * b := by rw [ha']
      _ = a * (w * b) := mul_assoc _ _ _
      _ = a * (b * w) := by rw [hb']
      _ = (a * b) * w := (mul_assoc _ _ _).symm
  have hwnc₂ : ¬ ∀ y ∈ S.I₂, w * y = y * w := hcentE
  have hwnc₁ : ¬ ∀ y ∈ S.I₁, w * y = y * w := by
    intro h
    apply hcentE
    intro y hy
    have := h (τ y) (hτ2 y hy)
    have h4 := congrArg τ this
    rwa [map_mul, map_mul, hττ, hτw] at h4
  have hI₂ : S.I₂ ≤ G1 ⊔ G2 := twist_le_aux S τ hτ1 hτ2 hττ hw2 hτw hq₂ hwnc₂ h1 h2
  have hI₁ : S.I₁ ≤ G1 ⊔ G2 := twist_le_aux S.swap τ hτ2 hτ1 hττ hw2 hτw hq₁ hwnc₁ h1 h2
  have hE : S.I₁ ⊔ S.I₂ ≤ G1 ⊔ G2 ⊔ G3 :=
    sup_le (hI₁.trans le_sup_left) (hI₂.trans le_sup_left)
  obtain ⟨y, hyw, hyE⟩ := exists_cent_not_mem_E S hL3₁ hL3₂ hw2 hwz
  exact eq_top_of_E_le S hE (Subgroup.mem_sup_right (h3 y hyw)) hyE

end Twist

section Stable

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem zpowers_z_comm_E {c : Y} (hc : c ∈ zpowers S.z) {a : Y} (ha : a ∈ S.I₁ ⊔ S.I₂) :
    c * a = a * c := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute S.comm ha
  have hc1 : c ∈ S.I₁ := (zpowers_le.2 S.z_mem₁) hc
  have hc2 : c ∈ S.I₂ := (zpowers_le.2 S.z_mem₂) hc
  have e1 : c * a₁ = a₁ * c := (S.comm a₁ ha₁ c hc2).symm
  have e2 : c * a₂ = a₂ * c := S.comm c hc1 a₂ ha₂
  calc c * (a₁ * a₂) = (c * a₁) * a₂ := (mul_assoc _ _ _).symm
    _ = a₁ * c * a₂ := by rw [e1]
    _ = a₁ * (c * a₂) := mul_assoc _ _ _
    _ = a₁ * (a₂ * c) := by rw [e2]
    _ = a₁ * a₂ * c := (mul_assoc _ _ _).symm

theorem false_of_stable [Finite Y] (hq₁ : CFSG.IsQuasisimple ↥S.I₁)
    (τ : MulAut Y) (hτ1 : ∀ x ∈ S.I₁, τ x ∈ S.I₁) (hτ2 : ∀ y ∈ S.I₂, τ y ∈ S.I₂)
    (Φ : Subgroup Y) (hΦfix : ∀ a ∈ Φ, τ a = a) (hΦsimple : IsSimpleGroup ↥Φ)
    (hΦperf : Group.IsPerfect ↥Φ) (hΦeven : 2 ∣ Nat.card ↥Φ)
    (hzΦ : S.z ∉ Φ) (hcard : Nat.card ↥S.I₁ = 2 * Nat.card ↥Φ)
    (hcent : ∀ y, τ y = y → y ∈ zpowers S.z ⊔ Φ) : False := by
  have hn₁ := S.normal₁
  have hn₂ := S.normal₂
  have hΦE : Φ ≤ S.I₁ ⊔ S.I₂ :=
    CFSG.GH74.GLS.IVK.GHInv.le_of_perfect_of_sup_zpowers (J := S.I₁ ⊔ S.I₂) (t := S.t) S.gen
      (Subgroup.isPerfect_iff.mp hΦperf)
  have hΦI₂ : Φ ⊓ S.I₂ = ⊥ := by
    have hnorm : (S.I₂.subgroupOf Φ).Normal := hn₂.subgroupOf Φ
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.I₂.subgroupOf Φ) with h | h
    · rw [eq_bot_iff]
      rintro y ⟨hyΦ, hyI⟩
      have : (⟨y, hyΦ⟩ : ↥Φ) ∈ S.I₂.subgroupOf Φ := hyI
      rw [h] at this
      simpa using congrArg Subtype.val (Subgroup.mem_bot.1 this)
    · exfalso
      have hΦI : Φ ≤ S.I₂ := fun y hy => by
        have : (⟨y, hy⟩ : ↥Φ) ∈ S.I₂.subgroupOf Φ := by rw [h]; trivial
        exact this
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Φ) 2 hΦeven
      have hu2 : (u : Y) * u = 1 := by
        have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
        rw [sq] at this
        exact congrArg Subtype.val this
      have hu1 : (u : Y) ≠ 1 := fun h1 => by
        have : u = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hu; omega
      rcases mem_zpowers_of_sq S.z_sq (sq_cases₂ S (hΦI u.2) hu2) with h1 | h1
      · exact hu1 h1
      · exact hzΦ (h1 ▸ u.2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard1 : Nat.card ↥(S.I₁ ⊓ S.I₂) = 2 := by
    rw [S.inter]
    have hz2 : orderOf S.z = 2 := orderOf_eq_prime (by rw [sq]; exact S.z_sq) S.z_ne
    rw [Nat.card_zpowers, hz2]
  have h1 := card_sup_mul_card_inf S.I₁ S.I₂
  have h2 := card_sup_mul_card_inf Φ S.I₂
  rw [hΦI₂, Subgroup.card_bot] at h2
  rw [hcard1] at h1
  have hEq : Φ ⊔ S.I₂ = S.I₁ ⊔ S.I₂ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hΦE le_sup_right) ?_
    have : Nat.card ↥(S.I₁ ⊔ S.I₂) = Nat.card ↥(Φ ⊔ S.I₂) := by
      rw [hcard] at h1
      rw [mul_one] at h2
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [h1, h2]
      ring
    exact this.le
  have hxd : ∀ x ∈ S.I₁, τ x * x⁻¹ ∈ zpowers S.z := by
    intro x hx
    have hxE : x ∈ Φ ⊔ S.I₂ := by rw [hEq]; exact Subgroup.mem_sup_left hx
    have hmul := Subgroup.mul_normal Φ S.I₂
    have hxm : x ∈ (Φ : Set Y) * (S.I₂ : Set Y) := by rw [← hmul]; exact hxE
    obtain ⟨a, ha, y, hy, rfl⟩ := hxm
    rw [← S.inter]
    refine ⟨?_, ?_⟩
    · exact S.I₁.mul_mem (hτ1 _ hx) (S.I₁.inv_mem hx)
    · have : τ (a * y) * (a * y)⁻¹ = a * (τ y * y⁻¹) * a⁻¹ := by
        rw [map_mul, hΦfix a ha]; group
      rw [this]
      exact hn₂.conj_mem _ (mul_mem (hτ2 y hy) (inv_mem hy)) a
  have hzc : ∀ c ∈ zpowers S.z, ∀ x ∈ S.I₁, c * x = x * c := fun c hc x hx =>
    (S.comm x hx c ((zpowers_le.2 S.z_mem₂) hc)).symm
  let d : ↥S.I₁ →* Y := MonoidHom.mk' (fun x => τ x * (x : Y)⁻¹) (by
    intro x y
    have hcy := hxd y y.2
    have hc : Commute (τ y * (y : Y)⁻¹) (x : Y)⁻¹ :=
      (Commute.inv_right (show Commute (τ y * (y : Y)⁻¹) (x : Y) from hzc _ hcy x x.2))
    show τ ((x : Y) * y) * ((x : Y) * y)⁻¹ = τ x * (x : Y)⁻¹ * (τ y * (y : Y)⁻¹)
    calc τ ((x : Y) * y) * ((x : Y) * y)⁻¹ = τ x * ((τ y * (y : Y)⁻¹) * (x : Y)⁻¹) := by
          rw [map_mul]; group
      _ = τ x * ((x : Y)⁻¹ * (τ y * (y : Y)⁻¹)) := by rw [hc.eq]
      _ = τ x * (x : Y)⁻¹ * (τ y * (y : Y)⁻¹) := by rw [mul_assoc])
  have hker : commutator ↥S.I₁ ≤ d.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hxd g₁ g₁.2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hxd g₂ g₂.2)
    show ⁅τ (g₁ : Y) * (g₁ : Y)⁻¹, τ (g₂ : Y) * (g₂ : Y)⁻¹⁆ = 1
    rw [← hm, ← hn]
    exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.zpow_zpow_self S.z m n).eq)
  have hd1 : ∀ x : ↥S.I₁, d x = 1 := by
    intro x
    have : d.ker = ⊤ := by
      rw [eq_top_iff, ← Group.isPerfect_def.mp hq₁.1]; exact hker
    have hx : x ∈ d.ker := by rw [this]; trivial
    exact hx
  have hfixI₁ : ∀ x ∈ S.I₁, τ x = x := by
    intro x hx
    have := hd1 ⟨x, hx⟩
    exact mul_inv_eq_one.1 this
  have hcommZ : ∀ c₁ ∈ zpowers S.z, ∀ c₂ ∈ zpowers S.z, Commute c₁ c₂ := by
    intro c₁ hc₁ c₂ hc₂
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc₁
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc₂
    exact Commute.zpow_zpow_self S.z m n
  have hI₁Φ : S.I₁ ≤ Φ := by
    have hI : S.I₁ ≤ zpowers S.z ⊔ Φ := fun x hx => hcent x (hfixI₁ x hx)
    have hperf : ⁅S.I₁, S.I₁⁆ = S.I₁ := Subgroup.isPerfect_iff.mp hq₁.1
    have hcomm : ∀ c ∈ zpowers S.z, ∀ a ∈ Φ, c * a = a * c := fun c hc a ha =>
      zpowers_z_comm_E S hc (hΦE ha)
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨c₁, hc₁, a₁, ha₁, rfl⟩ := mem_sup_of_commute hcomm (hI hg₁)
    obtain ⟨c₂, hc₂, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm (hI hg₂)
    rw [commutator_mul_of_commute (hcomm c₁ hc₁ a₁ ha₁) (hcomm c₁ hc₁ a₂ ha₂)
      (hcomm c₂ hc₂ a₁ ha₁) (hcomm c₂ hc₂ a₂ ha₂) (hcommZ c₁ hc₁ c₂ hc₂), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)
  exact hzΦ (hI₁Φ S.z_mem₁)

end Stable

end GenLocG2OuterShape

end CFSG.GH74.Generic.BProg.B2
