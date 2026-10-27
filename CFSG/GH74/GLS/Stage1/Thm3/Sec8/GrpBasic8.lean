module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21g

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section ConjAut

variable {G : Type*} [Group G]

@[expose] def conjAut (A : Subgroup G) (g : G) (hg : g ∈ normalizer (A : Set G)) : MulAut ↥A where
  toFun a := ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg a).1 a.2⟩
  invFun a := ⟨g⁻¹ * a * g, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) a).1 a.2
    simpa using this⟩
  left_inv a := Subtype.ext (by
    show g⁻¹ * (g * (a : G) * g⁻¹) * g = a
    group)
  right_inv a := Subtype.ext (by
    show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a
    group)
  map_mul' a b := Subtype.ext (by
    show g * ((a : G) * (b : G)) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
    group)

theorem conjAut_apply (A : Subgroup G) (g : G) (hg : g ∈ normalizer (A : Set G)) (a : ↥A) :
    ((conjAut A g hg a : ↥A) : G) = g * a * g⁻¹ := rfl

@[expose] def conjHom (A X : Subgroup G) (hX : X ≤ normalizer (A : Set G)) : ↥X →* MulAut ↥A where
  toFun x := conjAut A x (hX x.2)
  map_one' := by
    ext a
    show (1 : G) * (a : G) * (1 : G)⁻¹ = a
    group
  map_mul' x y := by
    ext a
    show ((x * y : ↥X) : G) * (a : G) * ((x * y : ↥X) : G)⁻¹ =
      (x : G) * ((y : G) * (a : G) * (y : G)⁻¹) * (x : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

end ConjAut

section Alpha

variable {G : Type} [Group G]

theorem exists_alpha {A Sg Sg' : Subgroup G} {h : G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hZ : Nonempty (↥A ≃* Bg.TwoGroups.Z4Z4)) (hSg : Sg ≤ normalizer (A : Set G))
    (hSg' : Sg' ≤ normalizer (A : Set G)) (hh : h ∈ normalizer (A : Set G))
    (hhord : orderOf (conjAut A h hh) = 3)
    (hker : ∀ x : ↥Sg, conjHom A Sg hSg x = 1 ↔ (x : G) ∈ zpowers (h ^ 3))
    (hker' : ∀ x : ↥Sg', conjHom A Sg' hSg' x = 1 ↔ (x : G) ∈ zpowers (h ^ 3))
    (hiso : ∃ _ : ((zpowers (h ^ 3)).subgroupOf Sg).Normal,
      Nonempty ((↥Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) ≃* Equiv.Perm (Fin 4)))
    (hiso' : ∃ _ : ((zpowers (h ^ 3)).subgroupOf Sg').Normal,
      Nonempty ((↥Sg' ⧸ (zpowers (h ^ 3)).subgroupOf Sg') ≃* Equiv.Perm (Fin 4))) :
    ∃ α : MulAut ↥A,
      (∀ x ∈ Sg, ∃ x' ∈ Sg', ∀ a b : ↥A, (b : G) = x * a * x⁻¹ →
        ((α b : ↥A) : G) = x' * ((α a : ↥A) : G) * x'⁻¹) ∧
      (∀ x' ∈ Sg', ∃ x ∈ Sg, ∀ a b : ↥A, (b : G) = x * a * x⁻¹ →
        ((α b : ↥A) : G) = x' * ((α a : ↥A) : G) * x'⁻¹) := by
  let _inst : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }
  have hS4 : ∀ (X : Subgroup G) (hX : X ≤ normalizer (A : Set G))
      (hk : ∀ x : ↥X, conjHom A X hX x = 1 ↔ (x : G) ∈ zpowers (h ^ 3))
      (hi : ∃ _ : ((zpowers (h ^ 3)).subgroupOf X).Normal,
        Nonempty ((↥X ⧸ (zpowers (h ^ 3)).subgroupOf X) ≃* Equiv.Perm (Fin 4))),
      Nonempty (↥(conjHom A X hX).range ≃* Equiv.Perm (Fin 4)) := by
    intro X hX hk hi
    obtain ⟨hN, ⟨e⟩⟩ := hi
    have hkereq : (conjHom A X hX).ker = (zpowers (h ^ 3)).subgroupOf X := by
      ext x
      rw [MonoidHom.mem_ker, hk x, Subgroup.mem_subgroupOf]
    have : (conjHom A X hX).ker.Normal := MonoidHom.normal_ker _
    have := hN
    exact ⟨(QuotientGroup.quotientKerEquivRange (conjHom A X hX)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans e)⟩
  have hKS4 := hS4 Sg hSg hker hiso
  have hKS4' := hS4 Sg' hSg' hker' hiso'
  obtain ⟨d, hd⟩ := Bg.TwoGroups.iv2_2_1_d ↥A hZ (conjAut A h hh) hhord
  obtain ⟨K₁, K₂, hne, hK₁, hK₂, hall, hd1, hd2⟩ :=
    Bg.TwoGroups.iv2_2_1_i ↥A hZ (conjAut A h hh) hhord d hd
  have hKc := hall (conjHom A Sg hSg).range hKS4
  have hKc' := hall (conjHom A Sg' hSg').range hKS4'
  have hα : ∃ α : MulAut ↥A, (∀ k ∈ (conjHom A Sg hSg).range, α * k * α⁻¹ ∈ (conjHom A Sg' hSg').range) ∧
      (∀ k ∈ (conjHom A Sg' hSg').range, α⁻¹ * k * α ∈ (conjHom A Sg hSg).range) := by
    have hd1' : ∀ k ∈ K₁, d * k * d⁻¹ ∈ K₂ := fun k hk => by
      rw [hd1]
      have e : d⁻¹ * (d * k * d⁻¹) * d = k := by group
      rw [e]
      exact hk
    have hd2' : ∀ k ∈ K₂, d⁻¹ * k * d ∈ K₁ := fun k hk => (hd1 k).1 hk
    rcases hKc with h1 | h1 <;> rcases hKc' with h2 | h2
    · refine ⟨1, fun k hk => ?_, fun k hk => ?_⟩
      · rw [h1, ← h2] at hk
        simpa using hk
      · rw [h2, ← h1] at hk
        simpa using hk
    · refine ⟨d, fun k hk => ?_, fun k hk => ?_⟩
      · rw [h1] at hk
        rw [h2]
        exact hd1' k hk
      · rw [h2] at hk
        rw [h1]
        exact hd2' k hk
    · refine ⟨d⁻¹, fun k hk => ?_, fun k hk => ?_⟩
      · rw [h1] at hk
        rw [h2]
        simpa using hd2' k hk
      · rw [h2] at hk
        rw [h1]
        simpa using hd1' k hk
    · refine ⟨1, fun k hk => ?_, fun k hk => ?_⟩
      · rw [h1, ← h2] at hk
        simpa using hk
      · rw [h2, ← h1] at hk
        simpa using hk
  obtain ⟨α, hα1, hα2⟩ := hα
  refine ⟨α, fun x hx => ?_, fun x' hx' => ?_⟩
  · obtain ⟨x'', hx''⟩ := hα1 (conjHom A Sg hSg ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    refine ⟨(x'' : G), x''.2, fun a b hb => ?_⟩
    have hb' : b = conjHom A Sg hSg ⟨x, hx⟩ a := Subtype.ext hb
    have key : α * conjHom A Sg hSg ⟨x, hx⟩ * α⁻¹ = conjHom A Sg' hSg' x'' := hx''.symm
    have h1 : α b = (α * conjHom A Sg hSg ⟨x, hx⟩ * α⁻¹) (α a) := by
      rw [hb']
      simp [MulAut.mul_apply]
    rw [h1, key]
    rfl
  · obtain ⟨x'', hx''⟩ := hα2 (conjHom A Sg' hSg' ⟨x', hx'⟩) ⟨⟨x', hx'⟩, rfl⟩
    refine ⟨(x'' : G), x''.2, fun a b hb => ?_⟩
    have hb' : b = conjHom A Sg hSg x'' a := Subtype.ext hb
    have key : α⁻¹ * conjHom A Sg' hSg' ⟨x', hx'⟩ * α = conjHom A Sg hSg x'' := hx''.symm
    have h1 : α b = conjHom A Sg' hSg' ⟨x', hx'⟩ (α a) := by
      have h2 : conjHom A Sg' hSg' ⟨x', hx'⟩ = α * conjHom A Sg hSg x'' * α⁻¹ := by
        rw [← key]
        group
      rw [hb', h2]
      simp [MulAut.mul_apply]
    rw [h1]
    rfl

end Alpha

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
