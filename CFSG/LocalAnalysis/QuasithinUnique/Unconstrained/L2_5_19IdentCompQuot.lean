module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.LocalAnalysis.ComponentInitial.ConjClassSimplicity

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

section Orders

theorem not_kOrder_of_gap {n p₀ : ℕ} (h168 : n ≠ 168) (h360 : n ≠ 360)
    (hlo : p₀ * (p₀ * p₀ - 1) < 2 * n) (hhi : 2 * n < (p₀ + 1) * ((p₀ + 1) * (p₀ + 1) - 1)) :
    ¬ KOrder n := by
  rintro (h | h | ⟨p, -, -, hp⟩)
  · exact h168 h
  · exact h360 h
  · rcases le_or_gt p p₀ with hle | hgt
    · have h1 : p * (p * p - 1) ≤ p₀ * (p₀ * p₀ - 1) :=
        Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.mul_le_mul hle hle) 1)
      omega
    · have hge : p₀ + 1 ≤ p := hgt
      have h1 : (p₀ + 1) * ((p₀ + 1) * (p₀ + 1) - 1) ≤ p * (p * p - 1) :=
        Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.mul_le_mul hge hge) 1)
      omega

end Orders

section Classes

open CFSG.LocalAnalysis.ComponentInitial

theorem isSimpleGroup_of_classSizes {G : Type*} [Group G] [Finite G] {m : ℕ}
    (sizes : Fin (m + 1) → ℕ) (e : Fin (m + 1) ≃ ConjClasses G)
    (he : ∀ i, (e i).carrier.ncard = sizes i) (i₀ : Fin (m + 1))
    (hone : ∀ j, sizes j = 1 → j = i₀) (hcard : 1 < Nat.card G)
    (hdiv : ∀ I : Finset (Fin m), (1 + ∑ i ∈ I, sizes (i₀.succAbove i)) ∣ Nat.card G →
      1 + ∑ i ∈ I, sizes (i₀.succAbove i) = 1 ∨
        1 + ∑ i ∈ I, sizes (i₀.succAbove i) = Nat.card G) :
    IsSimpleGroup G := by
  have h0 : e i₀ = ConjClasses.mk 1 := by
    obtain ⟨j, hj⟩ := e.surjective (ConjClasses.mk 1)
    have h1 : sizes j = 1 := by
      rw [← he j, hj, ConjClasses.carrier_eq_preimage_mk]
      have : ConjClasses.mk ⁻¹' {ConjClasses.mk (1 : G)} = {1} := by
        ext x
        simp [ConjClasses.mk_eq_mk_iff_isConj]
      rw [this, Set.ncard_singleton]
    rw [← hone j h1, hj]
  have hC : ∀ c : ConjClasses G,
      c ∈ Set.range (fun i : Fin m => e (i₀.succAbove i)) ↔ c ≠ ConjClasses.mk 1 := by
    intro c
    constructor
    · rintro ⟨j, rfl⟩ h
      rw [← h0] at h
      exact Fin.succAbove_ne i₀ j (e.injective h)
    · intro hc
      obtain ⟨i, rfl⟩ := e.surjective c
      have hi : i ≠ i₀ := by
        rintro rfl
        exact hc h0
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      exact ⟨j, rfl⟩
  refine (conjugacy_class_divisor_simplicity hcard (fun i : Fin m => e (i₀.succAbove i))
    (fun i j h => Fin.succAbove_right_injective (e.injective h)) hC fun I hI => ?_).2
  simp only [he] at hI ⊢
  exact hdiv I hI

end Classes

section Quotient

variable {C X : Type*} [Group C] [Group X]

theorem isComponent_map_of_solvable_ker (f : C →* X) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) {B : Subgroup C} (hB : CFSG.IsComponent B) :
    CFSG.IsComponent (B.map f) := by
  have hne : ¬ B ≤ f.ker := by
    intro hle
    have hs : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    have : Group.IsPerfect ↥B := hB.1.1
    exact Group.IsPerfect.not_isSolvable ↥B hs
  exact ⟨CFSG.LocalCores.isQuasisimple_map hB.1 f hne, hB.2.map hf⟩

theorem not_hasKComponent_of_quot_noComponent (f : C →* X) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) (hX : ∀ B : Subgroup X, ¬ CFSG.IsComponent B) :
    ¬ HasKComponent C := by
  rintro ⟨B, hB, -⟩
  exact hX _ (isComponent_map_of_solvable_ker f hf hker hB)

theorem eq_of_isComponent_of_commutator_le {D : Subgroup X} [IsSimpleGroup ↥D]
    (hcomm : commutator X ≤ D) {B : Subgroup X} (hB : CFSG.IsComponent B) : B = D := by
  have hBle : B ≤ D := (le_commutator_of_isQuasisimple hB.1).trans hcomm
  have htop := isComponent_eq_top_of_isSimpleGroup (CFSG.LocalCores.component_overgroup hB hBle)
  exact le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)

theorem card_eq_card_map_mul (f : C →* X) (B : Subgroup C) :
    Nat.card ↥(f.ker.subgroupOf B) * Nat.card ↥(B.map f) = Nat.card ↥B := by
  have h := Subgroup.card_mul_index (f.ker.subgroupOf B)
  rwa [← Subgroup.relIndex, Subgroup.relIndex_ker] at h

theorem card_subgroupOf_ker_dvd (f : C →* X) (B : Subgroup C) :
    Nat.card ↥(f.ker.subgroupOf B) ∣ Nat.card ↥f.ker := by
  let φ : ↥(f.ker.subgroupOf B) →* ↥f.ker :=
    { toFun := fun x => ⟨((x : ↥B) : C), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Subgroup.card_dvd_of_injective φ fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥f.ker => (z : C)) h))

theorem not_hasKComponent_of_quot_simple [Finite C] (f : C →* X) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) {m : ℕ} (hm : Nat.card ↥f.ker ∣ m) {D : Subgroup X}
    [IsSimpleGroup ↥D] (hcomm : commutator X ≤ D)
    (hord : ∀ k, k ∣ m → ¬ KOrder (k * Nat.card ↥D)) : ¬ HasKComponent C := by
  rintro ⟨B, hB, hK⟩
  have hBD : B.map f = D :=
    eq_of_isComponent_of_commutator_le hcomm (isComponent_map_of_solvable_ker f hf hker hB)
  have h := card_eq_card_map_mul f B
  rw [hBD] at h
  exact hord _ ((card_subgroupOf_ker_dvd f B).trans hm) (by rw [h]; exact hK)

end Quotient

end CFSG.QuasithinUnique.Id2519
