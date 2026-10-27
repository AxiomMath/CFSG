module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

section FixSub

variable {α : Type*}

@[expose] def fixSub (S : Finset α) : Subgroup (Perm α) where
  carrier := {σ | ∀ i ∈ S, σ i = i}
  mul_mem' := fun {a b} ha hb i hi => by
    simp only [Perm.mul_apply]
    rw [hb i hi, ha i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha i hi => by
    rw [Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

end FixSub

section Cent

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem comm_altSub_fixSub {S : Finset α} {g s : Perm α} (hg : g ∈ altSub S) (hs : s ∈ fixSub S) :
    g * s = s * g := by
  refine Perm.Disjoint.commute (fun x => ?_)
  by_cases hx : x ∈ S
  · exact Or.inr (hs x hx)
  · exact Or.inl ((mem_altSub.1 hg).2 x hx)

theorem mem_centralizer_altSub_card_three_iff {S : Finset α} (hS : S.card = 3) {σ : Perm α} :
    σ ∈ centralizer ((altSub S : Subgroup (Perm α)) : Set (Perm α)) ↔
      ∃ r ∈ altSub S, ∃ s ∈ fixSub S, σ = r * s := by
  constructor
  · intro hσ
    have hpres : ∀ x, σ x ∈ S ↔ x ∈ S := fun x =>
      (mem_iff_of_centralizer_altSub_card_three hS hσ x).symm
    let r₀ : Perm α := Perm.ofSubtype (σ.subtypePerm (p := (· ∈ S)) hpres)
    have hr₀S : ∀ x, x ∈ S → r₀ x = σ x := fun x hx => by
      simp only [r₀]
      exact Perm.ofSubtype_apply_of_mem _ hx
    have hr₀fix : ∀ x, x ∉ S → r₀ x = x := fun x hx => by
      simp only [r₀]
      exact Perm.ofSubtype_apply_of_not_mem _ hx
    have hr₀ : r₀ ∈ altSub S := by
      refine mem_altSub_of_card_three hS hr₀fix (fun x hx y hy z hz hxy hyz hxz => ?_)
      have hκ : σ * cyc3 x y z = cyc3 x y z * σ :=
        (mem_centralizer_iff.1 hσ _ (cyc3_mem_altSub hx hy hz hxy hyz hxz)).symm
      refine Equiv.ext fun w => ?_
      by_cases hw : w ∈ S
      · have hκw : cyc3 x y z w ∈ S := by
          by_cases h1 : w = x
          · subst h1; rw [cyc3_apply_left hxy hxz]; exact hy
          by_cases h2 : w = y
          · subst h2; rw [cyc3_apply_mid hyz hxz]; exact hz
          by_cases h3 : w = z
          · subst h3; rw [cyc3_apply_right]; exact hx
          rw [cyc3_apply_of_ne h1 h2 h3]; exact hw
        simp only [Perm.mul_apply]
        rw [hr₀S _ hκw, hr₀S _ hw]
        have := congrArg (fun f : Perm α => f w) hκ
        simpa using this
      · have : cyc3 x y z w = w := by
          apply cyc3_apply_of_ne <;> (rintro rfl; first | exact hw hx | exact hw hy | exact hw hz)
        simp only [Perm.mul_apply]
        rw [this, hr₀fix w hw]
        simp [this]
    refine ⟨r₀, hr₀, r₀⁻¹ * σ, fun i hi => ?_, by simp⟩
    simp only [Perm.mul_apply]
    rw [← hr₀S i hi]
    simp
  · rintro ⟨r, hr, s, hs, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    have h1 := altSub_comm_of_card_three hS hg hr
    have h2 := comm_altSub_fixSub hg hs
    calc g * (r * s) = (g * r) * s := by group
      _ = (r * g) * s := by rw [h1]
      _ = r * (g * s) := by group
      _ = r * (s * g) := by rw [h2]
      _ = r * s * g := by group

@[expose] noncomputable def fixSubHom (S : Finset α) : Perm ↥Sᶜ →* ↥(fixSub S) :=
  (Perm.ofSubtype (p := (· ∈ Sᶜ))).codRestrict (fixSub S) (fun s i hi =>
    Perm.ofSubtype_apply_of_not_mem s (by simpa using hi))

theorem fixSubHom_bijective (S : Finset α) : Function.Bijective (fixSubHom S) := by
  refine ⟨fun a b hab => Perm.ofSubtype_injective (congrArg Subtype.val hab), ?_⟩
  rintro ⟨σ, hσ⟩
  have hpres : ∀ x, (fun i => i ∈ Sᶜ) (σ x) ↔ (fun i => i ∈ Sᶜ) x := fun x =>
    (compl_iff_of_fixes (S := S) hσ x).symm
  refine ⟨σ.subtypePerm hpres, Subtype.ext ?_⟩
  refine Perm.ofSubtype_subtypePerm hpres (fun x hx => ?_)
  by_contra hxS
  exact hx (hσ x (by simpa using hxS))

end Cent

end CFSG.OddStandard.AltStdSec
