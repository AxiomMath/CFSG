module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YPl
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Set.Card

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private def planProd {Y : Type} [Group Y] (a : Fin 4 → Y) : Y := a 0 * a 1 * a 2 * a 3

private lemma commGroup_ratio {G : Type} [CommGroup G] (i : Fin 4) (a b : Fin 4 → G)
    (h : ∀ j, j ≠ i → b j = a j) :
    (a 0 * a 1 * a 2 * a 3)⁻¹ * (b 0 * b 1 * b 2 * b 3) = (a i)⁻¹ * b i := by
  rw [← Fin.prod_univ_four a, ← Fin.prod_univ_four b]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [h j hj, inv_mul_cancel])
    (fun hmem => absurd (Finset.mem_univ i) hmem)]

private lemma ratio_eq {Y : Type} [Group Y] {D : Subgroup Y} {W : Fin 4 → Subgroup Y}
    (hP : IsPlanes D W) {i : Fin 4} {a b : Fin 4 → Y}
    (ha : ∀ j, a j ∈ D) (hb : ∀ j, b j ∈ D) (h : ∀ j, j ≠ i → b j = a j) :
    (a 0 * a 1 * a 2 * a 3)⁻¹ * (b 0 * b 1 * b 2 * b 3) = (a i)⁻¹ * b i := by
  letI : CommGroup D := { (inferInstance : Group D) with
    mul_comm := fun x y => Subtype.ext (hP.comm x.1 x.2 y.1 y.2) }
  let av : Fin 4 → D := fun j => ⟨a j, ha j⟩
  let bv : Fin 4 → D := fun j => ⟨b j, hb j⟩
  have hbv : ∀ j, j ≠ i → bv j = av j := fun j hj => Subtype.ext (h j hj)
  have key := commGroup_ratio (G := D) i av bv hbv
  have keyY := congrArg (Subtype.val) key
  simpa [av, bv] using keyY

theorem comm_mem_plane {Y : Type} [Group Y] {D : Subgroup Y} {W : Fin 4 → Subgroup Y}
    {τ : Fin 4 → Y ≃* Y} (hP : IsPlanes D W) (hτ : IsPlaneAuts D W τ) (i : Fin 4) :
    ∀ d ∈ D, d⁻¹ * τ i d ∈ W i := by
  intro d hd
  obtain ⟨w, hw, hd_eq⟩ := hP.decomp d hd
  have hratio := ratio_eq hP (a := w) (b := fun j => τ i (w j))
    (fun j => hP.le j (hw j))
    (fun j => hτ.mem_D i (w j) (hP.le j (hw j)))
    (fun j hj => hτ.triv i j (fun hij => hj hij.symm) (w j) (hw j))
  rw [hd_eq]
  simp only [map_mul]
  rw [hratio]
  exact (W i).mul_mem ((W i).inv_mem (hw i)) (hτ.mem_W i (w i) (hw i))

private noncomputable def chosen {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} (hP : IsPlanes D W) {E : Subgroup Y} (hED : E ≤ D)
    (e : E) : ∀ i : Fin 4, W i :=
  fun i => ⟨Classical.choose (hP.decomp e.1 (hED e.2)) i,
    (Classical.choose_spec (hP.decomp e.1 (hED e.2))).1 i⟩

private lemma chosen_planProd {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} (hP : IsPlanes D W) {E : Subgroup Y} (hED : E ≤ D) (e : E) :
    planProd (fun i => (chosen hP hED e i : Y)) = e.1 := by
  simpa [chosen, planProd] using (Classical.choose_spec (hP.decomp e.1 (hED e.2))).2.symm

private lemma planProd_injective {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} (hP : IsPlanes D W) :
    Function.Injective (fun v : ∀ i, W i => planProd (fun i => (v i : Y))) := by
  classical
  let F : (∀ i : Fin 4, W i) → D := fun v =>
    ⟨planProd (fun i => (v i : Y)), by
      simp only [planProd]
      exact mul_mem (mul_mem (mul_mem (hP.le 0 (v 0).2) (hP.le 1 (v 1).2))
        (hP.le 2 (v 2).2)) (hP.le 3 (v 3).2)⟩
  have hsurj : Function.Surjective F := by
    intro d
    obtain ⟨w, hw, hd⟩ := hP.decomp d.1 d.2
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    apply Subtype.ext
    change w 0 * w 1 * w 2 * w 3 = (d : Y)
    exact hd.symm
  have hcardG : Nat.card (∀ i : Fin 4, W i) = 2 ^ 8 := by
    rw [Nat.card_pi]
    simp only [hP.card]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    decide
  have hcard : Nat.card (∀ i : Fin 4, W i) = Nat.card D := by
    rw [hcardG, hP.card_D]
  haveI : ∀ i, Finite (W i) := fun i =>
    Nat.finite_of_card_ne_zero (by rw [hP.card i]; decide)
  haveI : Finite (∀ i : Fin 4, W i) := inferInstance
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le (le_of_eq hcard)
  intro v u huv
  exact hbij.1 (Subtype.ext huv)

private lemma tau_planProd_ne_self {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y} (hP : IsPlanes D W)
    (hτ : IsPlaneAuts D W τ) (i : Fin 4) (w : ∀ j, W j) (hi : (w i : Y) ≠ 1) :
    τ i (planProd (fun j => (w j : Y))) ≠ planProd (fun j => (w j : Y)) := by
  intro heq
  have hmem : ∀ j, τ i (w j : Y) ∈ W j := by
    intro j
    by_cases h : j = i
    · rw [h]; exact hτ.mem_W i (w i : Y) (w i).2
    · have h2 : τ i (w j : Y) = w j :=
        hτ.triv i j (fun hij => h hij.symm) (w j) (w j).2
      rw [h2]
      exact (w j).2
  let v : ∀ j, W j := fun j => ⟨τ i (w j : Y), hmem j⟩
  have hv : (fun j => (v j : Y)) = fun j => τ i (w j : Y) := rfl
  have hve : planProd (fun j => (v j : Y)) = planProd (fun j => (w j : Y)) := by
    rw [hv]
    rw [show planProd (fun j => τ i (w j : Y)) = τ i (planProd (fun j => (w j : Y)))
      by simp only [planProd, map_mul]]
    exact heq
  have hvw : v = w := planProd_injective hP hve
  have hvi : (v i : Y) = (w i : Y) := congrArg (fun f : ∀ j, W j => (f i : Y)) hvw
  exact hτ.fpf i (w i : Y) (w i).2 hi hvi

private lemma plane_le_of_mem_ne_one {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y} (hP : IsPlanes D W)
    (hτ : IsPlaneAuts D W τ) {E : Subgroup Y} (hE : ∀ i, ∀ e ∈ E, τ i e ∈ E)
    {i : Fin 4} {x : Y} (hxW : x ∈ W i) (hxE : x ∈ E) (hx1 : x ≠ 1) :
    W i ≤ E := by
  have hyW : τ i x ∈ W i := hτ.mem_W i x hxW
  have hyE : τ i x ∈ E := hE i x hxE
  have hzW : τ i (τ i x) ∈ W i := hτ.mem_W i (τ i x) hyW
  have hzE : τ i (τ i x) ∈ E := hE i (τ i x) hyE
  have hy1 : τ i x ≠ 1 := by
    intro h
    have h' : τ i x = τ i 1 := by simpa using h
    exact hx1 ((τ i).injective h')
  have hz1 : τ i (τ i x) ≠ 1 := by
    intro h
    have h' : τ i (τ i x) = τ i 1 := by simpa using h
    exact hy1 ((τ i).injective h')
  have hxy : x ≠ τ i x := (hτ.fpf i x hxW hx1).symm
  have hxz : x ≠ τ i (τ i x) := by
    intro h
    apply hxy
    have h' := congrArg (τ i) h
    rw [hτ.cube i x] at h'
    exact h'.symm
  have hyz : τ i x ≠ τ i (τ i x) := by
    intro h
    apply hxz
    have h' := congrArg (τ i) h
    rw [hτ.cube i x] at h'
    exact h'.symm
  have h1 : (1 : Y) ∉ ({x, τ i x, τ i (τ i x)} : Set Y) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm, hz1.symm⟩
  have h2 : x ∉ ({τ i x, τ i (τ i x)} : Set Y) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy, hxz⟩
  have h3 : τ i x ∉ ({τ i (τ i x)} : Set Y) := by
    simpa using hyz
  have hs : ({1, x, τ i x, τ i (τ i x)} : Set Y).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hsub : ({1, x, τ i x, τ i (τ i x)} : Set Y) ⊆ (W i : Set Y) := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact (W i).one_mem
    · exact hxW
    · exact hyW
    · exact hzW
  haveI hWifin : Finite (W i) := Nat.finite_of_card_ne_zero (by rw [hP.card i]; decide)
  have hWn : (W i : Set Y).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    simpa using hP.card i
  have hEq : ({1, x, τ i x, τ i (τ i x)} : Set Y) = (W i : Set Y) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hWn, hs])
  intro a ha
  have ha' : a ∈ ({1, x, τ i x, τ i (τ i x)} : Set Y) := hEq.symm ▸ ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
  rcases ha' with rfl | rfl | rfl | rfl
  · exact E.one_mem
  · exact hxE
  · exact hyE
  · exact hzE

private lemma chosen_eq_one_of_not_le {Y : Type} [Group Y] {D : Subgroup Y}
    {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y} (hP : IsPlanes D W)
    (hτ : IsPlaneAuts D W τ) {E : Subgroup Y} (hED : E ≤ D)
    (hE : ∀ i, ∀ e ∈ E, τ i e ∈ E) (e : E) {i : Fin 4} (hi : ¬ W i ≤ E) :
    (chosen hP hED e i : Y) = 1 := by
  by_contra hne
  apply hi
  have hc : e.1⁻¹ * τ i e.1 ∈ W i := comm_mem_plane hP hτ i e.1 (hED e.2)
  have hcE : e.1⁻¹ * τ i e.1 ∈ E := E.mul_mem (E.inv_mem e.2) (hE i e.1 e.2)
  have hcne : e.1⁻¹ * τ i e.1 ≠ 1 := by
    intro h0
    have hτe : τ i e.1 = e.1 := by
      have h' := congrArg (fun z => e.1 * z) h0
      simpa [mul_assoc] using h'
    exact tau_planProd_ne_self hP hτ i (chosen hP hED e) hne
      (by rw [chosen_planProd hP hED e, hτe])
  exact plane_le_of_mem_ne_one hP hτ hE hc hcE hcne

private noncomputable def extend {Y : Type} [Group Y] {W : Fin 4 → Subgroup Y}
    {E : Subgroup Y} (u : ∀ i : {i : Fin 4 // W i ≤ E}, W i.1) : ∀ j : Fin 4, W j := by
  classical
  exact fun j => if h : W j ≤ E then u ⟨j, h⟩ else 1

private lemma extend_mem {Y : Type} [Group Y] {W : Fin 4 → Subgroup Y} {E : Subgroup Y}
    (u : ∀ i : {i : Fin 4 // W i ≤ E}, W i.1) (j : Fin 4) :
    (extend u j : Y) ∈ E := by
  simp only [extend]
  by_cases h : W j ≤ E
  · rw [dif_pos h]; exact h (u ⟨j, h⟩).2
  · rw [dif_neg h]; exact E.one_mem

private lemma extend_planProd_mem {Y : Type} [Group Y] {W : Fin 4 → Subgroup Y}
    {E : Subgroup Y} (u : ∀ i : {i : Fin 4 // W i ≤ E}, W i.1) :
    planProd (fun j => (extend u j : Y)) ∈ E := by
  simp only [planProd]
  exact E.mul_mem (E.mul_mem (E.mul_mem (extend_mem u 0) (extend_mem u 1))
    (extend_mem u 2)) (extend_mem u 3)

theorem card_of_invariant {Y : Type} [Group Y] {D : Subgroup Y} {W : Fin 4 → Subgroup Y}
    {τ : Fin 4 → Y ≃* Y} (hP : IsPlanes D W) (hτ : IsPlaneAuts D W τ) {E : Subgroup Y}
    (hED : E ≤ D) (hE : ∀ i, ∀ e ∈ E, τ i e ∈ E) :
    Nat.card E = 4 ^ Nat.card {i : Fin 4 // W i ≤ E} := by
  classical
  let I : Type := {i : Fin 4 // W i ≤ E}
  change Nat.card E = 4 ^ Nat.card I
  haveI hWi : ∀ i : Fin 4, Finite (W i) := fun i =>
    Nat.finite_of_card_ne_zero (by rw [hP.card i]; decide)
  haveI hIfin : Finite I := Finite.of_injective (fun i : I => i.1) (fun a b h => Subtype.ext h)
  haveI hIfintype : Fintype I := Fintype.ofFinite I
  haveI hPifin : Finite (∀ i : I, W i.1) := by infer_instance
  haveI hDfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hP.card_D]; decide)
  haveI hEfin : Finite E := Finite.of_injective (fun e : E => (⟨e.1, hED e.2⟩ : D))
    (fun a b h => Subtype.ext (congrArg (fun x : D => (x : Y)) h))
  have hinj1 : Nat.card E ≤ Nat.card (∀ i : I, W i.1) := by
    refine Nat.card_le_card_of_injective
      (fun e : E => fun i : I => chosen hP hED e i.1) ?_
    intro e e' heq
    apply Subtype.ext
    rw [← chosen_planProd hP hED e, ← chosen_planProd hP hED e']
    congr 1
    funext j
    by_cases hj : W j ≤ E
    · have h := congrFun heq (⟨j, hj⟩ : I)
      exact congrArg Subtype.val h
    · rw [chosen_eq_one_of_not_le hP hτ hED hE e hj,
          chosen_eq_one_of_not_le hP hτ hED hE e' hj]
  have hinj2 : Nat.card (∀ i : I, W i.1) ≤ Nat.card E := by
    refine Nat.card_le_card_of_injective
      (fun u : ∀ i : I, W i.1 =>
        (⟨planProd (fun j => (extend u j : Y)), extend_planProd_mem u⟩ : E)) ?_
    intro u u' heq
    have hprod : planProd (fun j => (extend u j : Y)) =
        planProd (fun j => (extend u' j : Y)) := congrArg Subtype.val heq
    have hext : extend u = extend u' := planProd_injective hP hprod
    funext i
    have h1 : (extend u i.1 : Y) = (u i : Y) := by
      simp only [extend]
      rw [dif_pos i.2]
    have h2 : (extend u' i.1 : Y) = (u' i : Y) := by
      simp only [extend]
      rw [dif_pos i.2]
    apply Subtype.ext
    rw [← h1, ← h2]
    exact congrArg Subtype.val (congrFun hext i.1)
  have hcardpi : Nat.card (∀ i : I, W i.1) = 4 ^ Nat.card I := by
    rw [Nat.card_pi]
    simp only [hP.card]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  calc Nat.card E = Nat.card (∀ i : I, W i.1) := le_antisymm hinj1 hinj2
    _ = 4 ^ Nat.card I := hcardpi

end CFSG.OddStandard.SmallF3.Omega
