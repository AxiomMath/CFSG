module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E5a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E6

public section

open scoped Classical
open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X} {E : Subgroup X}

theorem exists_orbit_min {H : Finset (Equiv.Perm (Fin 4))} (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hsq : ∀ a ∈ H, a * a = 1) (h1 : 1 ∈ H) (j : Fin 4) :
    ∃ i : Fin 4, (∀ a ∈ H, i ≤ a i) ∧ ∃ a ∈ H, a i = j := by
  classical
  have hne : (H.image (fun a => a j)).Nonempty :=
    ⟨j, Finset.mem_image.mpr ⟨1, h1, by simp⟩⟩
  refine ⟨(H.image (fun a => a j)).min' hne, ?_, ?_⟩
  · intro a ha
    obtain ⟨a0, ha0, ha0j⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    have hmem : a ((H.image (fun a => a j)).min' hne) ∈ H.image (fun a => a j) := by
      rw [← ha0j]
      exact Finset.mem_image.mpr
        ⟨a * a0, hmul a ha a0 ha0, by rw [Equiv.Perm.mul_apply, ha0j]⟩
    exact Finset.min'_le _ _ hmem
  · obtain ⟨a0, ha0, ha0j⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    refine ⟨a0, ha0, ?_⟩
    rw [← ha0j]
    have h := congrArg (fun p : Equiv.Perm (Fin 4) => p j) (hsq a0 ha0)
    simpa using h

private theorem s888_suppVec_ne_zero_iff {W : Fin 4 → Subgroup X} (y : X) (i : Fin 4) :
    suppVec W y i ≠ 0 ↔ ActsNontriv (W i) y := by
  by_cases h : ActsNontriv (W i) y <;> simp [suppVec, h]

private noncomputable abbrev s888_orbitMinima (hS : PlaneSys V W) (E : Subgroup X) :
    Finset (Fin 4) :=
  Finset.univ.filter fun i => ∀ a ∈ planeImage hS E, i ≤ a i

private theorem s888_exists_supp_witness (hS : PlaneSys V W) {i : Fin 4}
    (hi : i ∈ suppUnion (suppSet hS E)) :
    ∃ y : normalizer (V : Set X), (y : X) ∈ E ∧ planeHom hS y = 1 ∧
      ActsNontriv (W i) (y : X) := by
  classical
  simp only [suppUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨c, hc, hci⟩ := hi
  rw [mem_suppSet] at hc
  obtain ⟨y, hyE, hy1, hyv⟩ := hc
  refine ⟨y, hyE, hy1, ?_⟩
  rw [← s888_suppVec_ne_zero_iff (W := W) (y := (y : X)) (i := i), hyv]
  exact hci

private noncomputable def s888_suppWitness (hS : PlaneSys V W) (i : Fin 4)
    (hi : i ∈ suppUnion (suppSet hS E)) : normalizer (V : Set X) :=
  Classical.choose (s888_exists_supp_witness (E := E) hS hi)

private theorem s888_suppWitness_spec (hS : PlaneSys V W) (i : Fin 4)
    (hi : i ∈ suppUnion (suppSet hS E)) :
    (s888_suppWitness (E := E) hS i hi : X) ∈ E ∧
      planeHom hS (s888_suppWitness (E := E) hS i hi) = 1 ∧
      ActsNontriv (W i) (s888_suppWitness (E := E) hS i hi : X) :=
  Classical.choose_spec (s888_exists_supp_witness (E := E) hS hi)

private theorem s888_involAct (hS : PlaneSys V W) (hE : ActsElemAb V E) (i : Fin 4)
    (hi : i ∈ suppUnion (suppSet hS E)) :
    InvolAct (W i) (s888_suppWitness (E := E) hS i hi : X) := by
  obtain ⟨hyE, hy1, -⟩ := s888_suppWitness_spec (E := E) hS i hi
  refine ⟨?_, ?_⟩
  · intro a ha
    have hpi : planeHom hS (s888_suppWitness (E := E) hS i hi) i = i := by rw [hy1]; rfl
    exact (mem_plane_conj_iff hS _ hpi a).mpr ha
  · intro a ha
    exact hE.sq _ hyE a (hS.le i ha)

private noncomputable def s888_fixedSet (hS : PlaneSys V W) (i : Fin 4) : Set ↥(W i) :=
  if hi : i ∈ suppUnion (suppSet hS E) then
    {a : ↥(W i) |
      (s888_suppWitness (E := E) hS i hi : X) * (a : X) *
        (s888_suppWitness (E := E) hS i hi : X)⁻¹ = a}
  else Set.univ

private theorem s888_fixedSet_card (hS : PlaneSys V W) (hE : ActsElemAb V E) (i : Fin 4) :
    Nat.card ↥(s888_fixedSet (E := E) hS i) =
      if i ∈ suppUnion (suppSet hS E) then 2 else 4 := by
  classical
  by_cases hi : i ∈ suppUnion (suppSet hS E)
  · rw [s888_fixedSet, dif_pos hi, if_pos hi]
    exact card_fixed_of_actsNontriv (hS.card i) (fun a ha => hS.sq a (hS.le i ha))
      (s888_involAct hS hE i hi) (s888_suppWitness_spec (E := E) hS i hi).2.2
  · rw [s888_fixedSet, dif_neg hi, if_neg hi]
    rw [Nat.card_congr (Equiv.Set.univ (↥(W i)))]
    exact hS.card i

private theorem s888_comp_mem_fixedSet (hS : PlaneSys V W) (v : V)
    (hv : ∀ y ∈ E, y * (v : X) * y⁻¹ = v) (i : Fin 4) :
    (⟨comp hS v i, comp_mem hS v i⟩ : ↥(W i)) ∈ s888_fixedSet (E := E) hS i := by
  classical
  by_cases hi : i ∈ suppUnion (suppSet hS E)
  · rw [s888_fixedSet, dif_pos hi]
    change (s888_suppWitness (E := E) hS i hi : X) * comp hS v i *
      (s888_suppWitness (E := E) hS i hi : X)⁻¹ = comp hS v i
    obtain ⟨hyE, hy1, -⟩ := s888_suppWitness_spec (E := E) hS i hi
    have hpi : planeHom hS (s888_suppWitness (E := E) hS i hi) i = i := by rw [hy1]; rfl
    have hcf := comp_fixed hS v (s888_suppWitness (E := E) hS i hi) (hv _ hyE) i
    rw [hpi] at hcf
    exact hcf.symm
  · rw [s888_fixedSet, dif_neg hi]
    exact Set.mem_univ _

private theorem s888_eq_of_comp_eq_on_minima (hS : PlaneSys V W) (hE : ActsElemAb V E)
    {v v' : V} (hv : ∀ y ∈ E, y * (v : X) * y⁻¹ = v)
    (hv' : ∀ y ∈ E, y * (v' : X) * y⁻¹ = v')
    (h : ∀ i : Fin 4, (∀ a ∈ planeImage hS E, i ≤ a i) → comp hS v i = comp hS v' i) :
    v = v' := by
  apply comp_injective hS
  funext j
  obtain ⟨h1, hmul, hsq⟩ := planeImage_group hS hE
  obtain ⟨i, himin, a, haH, hai⟩ := exists_orbit_min hmul hsq h1 j
  rw [mem_planeImage] at haH
  obtain ⟨y, hyE, hy_eq⟩ := haH
  have key_v : comp hS v j = (y : X) * comp hS v i * (y : X)⁻¹ := by
    have hcf := comp_fixed hS v y (hv (y : X) hyE) i
    rw [hy_eq, hai] at hcf
    exact hcf
  have key_v' : comp hS v' j = (y : X) * comp hS v' i * (y : X)⁻¹ := by
    have hcf := comp_fixed hS v' y (hv' (y : X) hyE) i
    rw [hy_eq, hai] at hcf
    exact hcf
  rw [key_v, key_v', h i himin]

private noncomputable def s888_toProd (hS : PlaneSys V W) :
    {v : V // ∀ y ∈ E, y * (v : X) * y⁻¹ = v} →
      (i : ↥(s888_orbitMinima hS E)) → ↥(s888_fixedSet (E := E) hS i.val) :=
  fun v i => ⟨⟨comp hS (v : V) i.val, comp_mem hS (v : V) i.val⟩,
    s888_comp_mem_fixedSet (E := E) hS (v : V) v.2 i.val⟩

private theorem s888_toProd_injective (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Function.Injective (s888_toProd (E := E) hS) := by
  intro v v' h
  apply Subtype.ext
  apply s888_eq_of_comp_eq_on_minima hS hE v.2 v'.2
  intro i hi
  have h2 := congrFun h (⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩ :
    ↥(s888_orbitMinima hS E))
  exact congrArg (fun x : ↥(s888_fixedSet (E := E) hS i) => (x.1.1 : X)) h2

theorem card_fixed_le (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card {v : V // ∀ y ∈ E, y * (v : X) * y⁻¹ = v} ≤
      fixedBound (planeImage hS E) (suppSet hS E) := by
  classical
  have hcardβ : Nat.card (∀ i : ↥(s888_orbitMinima hS E),
        ↥(s888_fixedSet (E := E) hS i.val)) =
      ∏ i : ↥(s888_orbitMinima hS E), Nat.card ↥(s888_fixedSet (E := E) hS i.val) :=
    Nat.card_pi
  haveI : Finite (∀ i : ↥(s888_orbitMinima hS E),
        ↥(s888_fixedSet (E := E) hS i.val)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardβ]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [s888_fixedSet_card hS hE i.val]
    split <;> decide
  have hle := Nat.card_le_card_of_injective (s888_toProd (E := E) hS)
    (s888_toProd_injective hS hE)
  rw [Nat.card_pi] at hle
  have hprod : (∏ i : ↥(s888_orbitMinima hS E),
        Nat.card ↥(s888_fixedSet (E := E) hS i.val)) =
      fixedBound (planeImage hS E) (suppSet hS E) := by
    rw [Finset.prod_coe_sort (s := s888_orbitMinima hS E)
      (f := fun i : Fin 4 => Nat.card ↥(s888_fixedSet (E := E) hS i))]
    unfold fixedBound
    apply Finset.prod_congr rfl
    intro i _
    exact s888_fixedSet_card hS hE i
  rw [hprod] at hle
  exact hle

end CFSG.OddStandard.SmallF3.Omega
