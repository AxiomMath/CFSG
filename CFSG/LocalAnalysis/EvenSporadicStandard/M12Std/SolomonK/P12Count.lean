module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

theorem card_le_length_of_injective {α : Type} [Finite α] (f : α → Array ℕ)
    (hf : Function.Injective f) (l : List (Array ℕ)) (hl : l.Nodup) (hmem : ∀ a, f a ∈ l) :
    Nat.card α ≤ l.length := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card α = (Finset.univ.image f).card :=
        (Finset.card_image_of_injective _ hf).symm
    _ ≤ l.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        exact List.mem_toFinset.2 (hmem a)
    _ = l.length := List.toFinset_card_of_nodup hl

section Group

variable {G : Type} [Group G] {n : ℕ} (arr : G → Array ℕ)

theorem commB_arr (hmul : ∀ x y, pmul n (arr x) (arr y) = arr (x * y))
    (hinj : Function.Injective arr) (x y : G) :
    commB n (arr x) (arr y) = true ↔ x * y = y * x := by
  unfold commB
  rw [hmul, hmul, beq_iff_eq]
  exact ⟨fun h => hinj h, fun h => by rw [h]⟩

theorem sqB_arr (hmul : ∀ x y, pmul n (arr x) (arr y) = arr (x * y))
    (hone : pid n = arr 1) (hinj : Function.Injective arr) (x : G) :
    sqB n (arr x) = true ↔ x * x = 1 := by
  unfold sqB
  rw [hmul, hone, beq_iff_eq]
  exact ⟨fun h => hinj h, fun h => by rw [h]⟩

end Group

theorem comm_of_sq_eq_one {G : Type} [Group G] {A : Subgroup G} (hsq : ∀ x ∈ A, x * x = 1)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have h1 := hsq (x * y) (A.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, hxi, hyi]

theorem countOK_sound {G : Type} [Group G] [Finite G] {n : ℕ} (arr : G → Array ℕ)
    (hinj : Function.Injective arr) (hmul : ∀ x y, pmul n (arr x) (arr y) = arr (x * y))
    (hone : pid n = arr 1) {P E : Subgroup G} {PV EV : List (Array ℕ)} (hPV : PV.Nodup)
    (hPVmem : ∀ y, y ∈ PV ↔ ∃ x ∈ P, arr x = y) (hEVmem : ∀ y, y ∈ EV ↔ ∃ x ∈ E, arr x = y)
    (h : countOK n PV EV = true) :
    ∀ A : Subgroup G, A ≤ P → (∀ x ∈ A, x * x = 1) → 64 ≤ Nat.card A → A ≤ E := by
  intro A hAP hsq hcard a ha
  by_contra haE
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => comm_of_sq_eq_one hsq hx hy
  have hmemPV : ∀ y ∈ A, arr y ∈ PV := fun y hy => (hPVmem _).2 ⟨y, hAP hy, rfl⟩
  have h1 := List.all_eq_true.1 h (arr a) (hmemPV a ha)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact haE (by rw [hone] at h1; rw [hinj h1]; exact E.one_mem)
  · have := (sqB_arr arr hmul hone hinj a).2 (hsq a ha)
    rw [this] at h1
    exact Bool.noConfusion h1
  · obtain ⟨x, hx, hxa⟩ := (hEVmem _).1 h1
    exact haE (by rw [← hinj hxa]; exact hx)
  · unfold countAt at h1
    set Cx := PV.filter (commB n (arr a)) with hCx
    have h2 : (triple n Cx).length < 64 := of_decide_eq_true h1
    have hCxnd : Cx.Nodup := hPV.filter _
    have hmemCx : ∀ y ∈ A, arr y ∈ Cx := fun y hy =>
      List.mem_filter.2 ⟨hmemPV y hy, (commB_arr arr hmul hinj a y).2 (hcomm a ha y hy)⟩
    have hinjA : Function.Injective (fun y : A => arr y.1) := fun y z hyz =>
      Subtype.ext (hinj hyz)
    have hbig : ∀ y ∈ A, 64 ≤ (Cx.filter (commB n (arr y))).length := by
      intro y hy
      refine le_trans hcard (card_le_length_of_injective (fun z : A => arr z.1) hinjA _
        (hCxnd.filter _) fun z => ?_)
      exact List.mem_filter.2 ⟨hmemCx z.1 z.2,
        (commB_arr arr hmul hinj y z.1).2 (hcomm y hy z.1 z.2)⟩
    have hle := card_le_length_of_injective (fun z : A => arr z.1) hinjA
      (triple n Cx) (hCxnd.filter _) fun z => by
        refine List.mem_filter.2 ⟨hmemCx z.1 z.2, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(sqB_arr arr hmul hone hinj z.1).2 (hsq z.1 z.2), hbig z.1 z.2⟩
    omega

end CFSG.EvenSporadicStandard.M12Std.SolomonK.P12
