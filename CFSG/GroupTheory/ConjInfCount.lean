module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.GroupTheory

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G] [Finite G]

theorem exists_inf_conjSubgroup_eq_bot_of_card {R Λ : Subgroup G}
    (hfpf : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ Λ, r * x * r⁻¹ = x → x = 1)
    (hcard : (Nat.card Λ - 1) ^ 2 < Nat.card R) :
    ∃ r ∈ R, Λ ⊓ conjSubgroup r Λ = ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  have hchoice : ∀ r : R, ∃ x : Λ, x ≠ 1 ∧
      (r : G) * (x : G) * (r : G)⁻¹ ∈ Λ := by
    intro r
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hcon r r.2)
    obtain ⟨hyΛ, hyconj⟩ := Subgroup.mem_inf.mp hy
    have hxΛ : (r : G)⁻¹ * y * (r : G) ∈ Λ := mem_conjSubgroup.mp hyconj
    refine ⟨⟨(r : G)⁻¹ * y * (r : G), hxΛ⟩, ?_, ?_⟩
    · intro hx
      apply hy1
      have hx' : (r : G)⁻¹ * y * (r : G) = 1 := congrArg (fun z : Λ => (z : G)) hx
      apply Subtype.ext
      calc y = (r : G) * ((r : G)⁻¹ * y * (r : G)) * (r : G)⁻¹ := by group
        _ = (r : G) * 1 * (r : G)⁻¹ := by rw [hx']
        _ = 1 := by group
    · rw [show (r : G) * ((r : G)⁻¹ * y * (r : G)) * (r : G)⁻¹ = y from by group]
      exact hyΛ
  let f : R → {x : Λ // x ≠ 1} × {y : Λ // y ≠ 1} := fun r =>
    let x := (hchoice r).choose
    let hx1 : x ≠ 1 := (hchoice r).choose_spec.1
    let hxmem : (r : G) * (x : G) * (r : G)⁻¹ ∈ Λ := (hchoice r).choose_spec.2
    (⟨x, hx1⟩, ⟨⟨(r : G) * (x : G) * (r : G)⁻¹, hxmem⟩, by
      intro h1
      apply hx1
      have h := congrArg (fun z : Λ => (z : G)) h1
      simpa using h⟩)
  have hinj : Function.Injective f := by
    intro r₁ r₂ heq
    set x₁ := (hchoice r₁).choose with hx₁
    set x₂ := (hchoice r₂).choose with hx₂
    have hx12 : (x₁ : G) = (x₂ : G) := by
      have h := congrArg (fun p => ((p.1 : Λ) : G)) heq
      simpa [f, hx₁, hx₂] using h
    have hy12 : (r₁ : G) * (x₁ : G) * (r₁ : G)⁻¹ =
        (r₂ : G) * (x₂ : G) * (r₂ : G)⁻¹ := by
      have h := congrArg (fun p => ((p.2 : Λ) : G)) heq
      simpa [f, hx₁, hx₂] using h
    have hy' : (r₁ : G) * (x₁ : G) * (r₁ : G)⁻¹ =
        (r₂ : G) * (x₁ : G) * (r₂ : G)⁻¹ := by
      rw [← hx12] at hy12
      exact hy12
    have hcomm : ((r₂ : G)⁻¹ * (r₁ : G)) * (x₁ : G) *
        ((r₂ : G)⁻¹ * (r₁ : G))⁻¹ = (x₁ : G) := by
      calc (r₂ : G)⁻¹ * (r₁ : G) * (x₁ : G) * ((r₂ : G)⁻¹ * (r₁ : G))⁻¹
          = (r₂ : G)⁻¹ * ((r₁ : G) * (x₁ : G) * (r₁ : G)⁻¹) * (r₂ : G) := by group
        _ = (r₂ : G)⁻¹ * ((r₂ : G) * (x₁ : G) * (r₂ : G)⁻¹) * (r₂ : G) := by rw [hy']
        _ = (x₁ : G) := by group
    have hs : (r₂ : G)⁻¹ * (r₁ : G) ∈ R :=
      R.mul_mem (R.inv_mem r₂.2) r₁.2
    by_cases hs1 : (r₂ : G)⁻¹ * (r₁ : G) = 1
    · apply Subtype.ext
      have h := congrArg (fun z => (r₂ : G) * z) hs1
      simpa [mul_assoc] using h
    · exfalso
      have hx1G : ((hchoice r₁).choose : G) = 1 :=
        hfpf _ hs hs1 _ (hchoice r₁).choose.2 hcomm
      exact (hchoice r₁).choose_spec.1 (Subtype.ext hx1G)
  have hle : Nat.card R ≤ Nat.card ({x : Λ // x ≠ 1} × {y : Λ // y ≠ 1}) :=
    Nat.card_le_card_of_injective f hinj
  have hcardne : Nat.card {x : Λ // x ≠ 1} = Nat.card Λ - 1 := by
    haveI : Fintype Λ := Fintype.ofFinite Λ
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : Λ => x = 1)]
    have h1 : Fintype.card {x : Λ // x = 1} = 1 :=
      Fintype.card_eq_one_of_forall_eq (i := ⟨1, rfl⟩) (fun y => Subtype.ext y.2)
    rw [h1]
  rw [Nat.card_prod, hcardne, ← pow_two] at hle
  omega

end CFSG.GroupTheory
