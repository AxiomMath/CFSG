module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

theorem exists_sq_coset {G : Type*} [Group G] [Finite G] {A U : Subgroup G} {δ : G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAδ : ∀ a ∈ A, δ * a * δ⁻¹ ∈ A)
    (hδ2 : δ * δ = 1)
    (hU : ∀ x, x ∈ U ↔ x ∈ A ∧ x * x = 1)
    (hexp : ∀ a ∈ A, (a * a) * (a * a) = 1)
    (hA16 : Nat.card ↥A = 16) (hU4 : Nat.card ↥U = 4)
    (hP1 : ∀ a ∈ A, a * a = 1 → δ * a * δ⁻¹ = a)
    (hP2 : ∀ a ∈ A, a * (δ * a * δ⁻¹) = 1 → a * a = 1) :
    ∀ x ∈ U, ∃ a ∈ A, (a * δ) * (a * δ) = x := by
  classical
  let _inst : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }
  let c : ↥A →* ↥A := MonoidHom.mk' (fun a : ↥A => (⟨δ * a * δ⁻¹, hAδ a a.2⟩ : ↥A)) (by
    intro a b
    apply Subtype.ext
    show δ * ((a : G) * (b : G)) * δ⁻¹ = (δ * (a : G) * δ⁻¹) * (δ * (b : G) * δ⁻¹)
    group)
  let f : ↥A →* ↥A := MonoidHom.id ↥A * c
  have hf : ∀ a : ↥A, ((f a : ↥A) : G) = (a : G) * (δ * (a : G) * δ⁻¹) := fun a => rfl
  have hUA : U ≤ A := fun x hx => ((hU x).1 hx).1
  let U' : Subgroup ↥A := U.subgroupOf A
  have hmemU' : ∀ a : ↥A, a ∈ U' ↔ (a : G) ∈ U := fun a => Iff.rfl
  have hker : f.ker = U' := by
    ext a
    rw [MonoidHom.mem_ker, hmemU', hU]
    constructor
    · intro h1
      have h2 : (a : G) * (δ * (a : G) * δ⁻¹) = 1 := by
        rw [← hf, h1]; rfl
      exact ⟨a.2, hP2 a a.2 h2⟩
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      rw [hf, hP1 a a.2 h1]
      exact h1
  have hrange : f.range ≤ U' := by
    rintro _ ⟨a, rfl⟩
    rw [hmemU', hU]
    refine ⟨(f a).2, ?_⟩
    rw [hf]
    have ha2 : (a : G) * (a : G) ∈ A := mul_mem a.2 a.2
    have h1 : δ * ((a : G) * (a : G)) * δ⁻¹ = (a : G) * (a : G) := hP1 _ ha2 (hexp a a.2)
    have hc := hAc _ ((hAδ a a.2)) a a.2
    have e1 : δ * ((a : G) * (a : G)) * δ⁻¹ = (δ * (a : G) * δ⁻¹) * (δ * (a : G) * δ⁻¹) := by group
    calc ((a : G) * (δ * (a : G) * δ⁻¹)) * ((a : G) * (δ * (a : G) * δ⁻¹))
        = ((a : G) * (a : G)) * ((δ * (a : G) * δ⁻¹) * (δ * (a : G) * δ⁻¹)) := by
          calc ((a : G) * (δ * (a : G) * δ⁻¹)) * ((a : G) * (δ * (a : G) * δ⁻¹))
              = (a : G) * ((δ * (a : G) * δ⁻¹) * (a : G)) * (δ * (a : G) * δ⁻¹) := by group
            _ = (a : G) * ((a : G) * (δ * (a : G) * δ⁻¹)) * (δ * (a : G) * δ⁻¹) := by rw [hc.symm]
            _ = ((a : G) * (a : G)) * ((δ * (a : G) * δ⁻¹) * (δ * (a : G) * δ⁻¹)) := by group
      _ = ((a : G) * (a : G)) * (δ * ((a : G) * (a : G)) * δ⁻¹) := by rw [e1]
      _ = ((a : G) * (a : G)) * ((a : G) * (a : G)) := by rw [h1]
      _ = 1 := hexp a a.2
  have hcardU' : Nat.card U' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv, hU4]
  have hcardker : Nat.card f.ker * Nat.card f.range = Nat.card ↥A := by
    have h1 := Subgroup.card_mul_index f.ker
    rwa [Subgroup.index_ker] at h1
  have hrange_eq : f.range = U' := by
    apply Subgroup.eq_of_le_of_card_ge hrange
    rw [hker, hcardU', hA16] at hcardker
    omega
  intro x hx
  have hxU' : (⟨x, hUA hx⟩ : ↥A) ∈ U' := hx
  rw [← hrange_eq] at hxU'
  obtain ⟨a, ha⟩ := hxU'
  refine ⟨(a : G), a.2, ?_⟩
  have h1 : ((f a : ↥A) : G) = x := by rw [ha]
  rw [hf] at h1
  rw [← h1]
  calc ((a : G) * δ) * ((a : G) * δ) = (a : G) * (δ * (a : G) * δ⁻¹) * (δ * δ) := by group
    _ = (a : G) * (δ * (a : G) * δ⁻¹) := by rw [hδ2, mul_one]

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
