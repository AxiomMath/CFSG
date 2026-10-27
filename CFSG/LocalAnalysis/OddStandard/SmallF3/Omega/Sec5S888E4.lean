module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

@[expose] def PlaneParity (V : Subgroup X) (W : Fin 4 → Subgroup X) : Prop :=
  ∀ y ∈ normalizer (V : Set X), (∀ i, ∀ w ∈ W i, y * w * y⁻¹ ∈ W i) →
    (∀ v ∈ V, y * y * v * (y * y)⁻¹ = v) → Even (Nat.card {i : Fin 4 // ActsNontriv (W i) y})

open scoped Classical in
@[expose] noncomputable def suppVec (W : Fin 4 → Subgroup X) (y : X) : Fin 4 → ZMod 2 :=
  fun i => if ActsNontriv (W i) y then 1 else 0

open scoped Classical in
noncomputable def planeImage (hS : PlaneSys V W) (E : Subgroup X) :
    Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter fun a =>
    ∃ y : normalizer (V : Set X), (y : X) ∈ E ∧ planeHom hS y = a

open scoped Classical in
noncomputable def suppSet (hS : PlaneSys V W) (E : Subgroup X) : Finset (Fin 4 → ZMod 2) :=
  Finset.univ.filter fun c =>
    ∃ y : normalizer (V : Set X), (y : X) ∈ E ∧ planeHom hS y = 1 ∧ suppVec W y = c

theorem mem_planeImage (hS : PlaneSys V W) {E : Subgroup X}
    {a : Equiv.Perm (Fin 4)} :
    a ∈ planeImage hS E ↔ ∃ y : normalizer (V : Set X), (y : X) ∈ E ∧ planeHom hS y = a := by
  simp [planeImage]

theorem mem_suppSet (hS : PlaneSys V W) {E : Subgroup X} {c : Fin 4 → ZMod 2} :
    c ∈ suppSet hS E ↔
      ∃ y : normalizer (V : Set X), (y : X) ∈ E ∧ planeHom hS y = 1 ∧ suppVec W y = c := by
  simp [suppSet]

private theorem zmod_two_ite_add {c p q : Prop} [Decidable c] [Decidable p] [Decidable q]
    (h : c ↔ (p ↔ ¬ q)) :
    (if c then (1 : ZMod 2) else 0) =
      (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q
  · have hc : ¬c := fun hc => (h.mp hc).mp hp hq
    simp only [if_neg hc, if_pos hp, if_pos hq, one_add_one_eq_two, CharTwo.two_eq_zero]
  · have hc : c := h.mpr ⟨fun _ => hq, fun _ => hp⟩
    simp only [if_pos hc, if_pos hp, if_neg hq, add_zero]
  · have hc : c := h.mpr ⟨fun hp' => absurd hp' hp, fun hnq => absurd hq hnq⟩
    simp only [if_pos hc, if_neg hp, if_pos hq, zero_add]
  · have hc : ¬c := fun hc => hp ((h.mp hc).mpr hq)
    simp only [if_neg hc, if_neg hp, if_neg hq, add_zero]

theorem actsNontriv_conj (hS : PlaneSys V W) (τ : normalizer (V : Set X)) (i : Fin 4)
    (y : X) :
    ActsNontriv (W (planeHom hS τ i)) ((τ : X) * y * (τ : X)⁻¹) ↔ ActsNontriv (W i) y := by
  have h1 := not_actsNontriv_iff (A := W i) (y := y)
  have h2 := not_actsNontriv_iff (A := W (planeHom hS τ i)) (y := (τ : X) * y * (τ : X)⁻¹)
  have hfix : (∀ u ∈ W (planeHom hS τ i),
        (τ : X) * y * (τ : X)⁻¹ * u * ((τ : X) * y * (τ : X)⁻¹)⁻¹ = u) ↔
      (∀ a ∈ W i, y * a * y⁻¹ = a) := by
    constructor
    · intro hu a ha
      have hua : (τ : X) * a * (τ : X)⁻¹ ∈ W (planeHom hS τ i) := planeHom_spec hS τ i a ha
      have h := hu ((τ : X) * a * (τ : X)⁻¹) hua
      have heq : (τ : X) * (y * a * y⁻¹) * (τ : X)⁻¹ = (τ : X) * a * (τ : X)⁻¹ := by
        rw [← h]; group
      exact mul_right_cancel (mul_left_cancel (by simpa only [mul_assoc] using heq))
    · intro ha u hu
      have hw : (τ : X)⁻¹ * u * (τ : X) ∈ W i := by
        have h' := planeHom_spec hS τ⁻¹ (planeHom hS τ i) u hu
        have hsub : planeHom hS τ⁻¹ (planeHom hS τ i) = i := by rw [map_inv]; simp
        rw [hsub] at h'
        simpa using h'
      have h := ha ((τ : X)⁻¹ * u * (τ : X)) hw
      have heq : (τ : X) * (y * ((τ : X)⁻¹ * u * (τ : X)) * y⁻¹) * (τ : X)⁻¹ =
          (τ : X) * ((τ : X)⁻¹ * u * (τ : X)) * (τ : X)⁻¹ := by rw [h]
      rw [show (τ : X) * (y * ((τ : X)⁻¹ * u * (τ : X)) * y⁻¹) * (τ : X)⁻¹ =
          (τ : X) * y * (τ : X)⁻¹ * u * ((τ : X) * y * (τ : X)⁻¹)⁻¹ by group] at heq
      rwa [show (τ : X) * ((τ : X)⁻¹ * u * (τ : X)) * (τ : X)⁻¹ = u by group] at heq
  constructor
  · intro h
    by_contra hc
    exact (h2.mpr (hfix.mpr (h1.mp hc))) h
  · intro h
    by_contra hc
    exact (h1.mpr (hfix.mp (h2.mp hc))) h

structure ActsElemAb (V E : Subgroup X) : Prop where
  le_normalizer : E ≤ normalizer (V : Set X)
  sq : ∀ a ∈ E, ∀ v ∈ V, a * a * v * (a * a)⁻¹ = v
  comm : ∀ a ∈ E, ∀ b ∈ E, ∀ v ∈ V, a * b * v * (a * b)⁻¹ = b * a * v * (b * a)⁻¹

theorem ActsElemAb.of_exact {V E : Subgroup X} (hE : E ≤ normalizer (V : Set X))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEs : ∀ a ∈ E, a * a = 1) : ActsElemAb V E := by
  refine ⟨hE, fun a ha v _ => ?_, fun a ha b hb v _ => ?_⟩
  · rw [hEs a ha]
    group
  · rw [hEc a ha b hb]

theorem planeHom_eq_one_of_centralizes (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (h : ∀ v ∈ V, (y : X) * v * (y : X)⁻¹ = v) : planeHom hS y = 1 := by
  refine Equiv.ext fun i => ?_
  refine planeHom_eq_of_mem hS y (j := i) (fun w hw => ?_)
  rw [h w (hS.le i hw)]
  exact hw

variable {E : Subgroup X}

theorem planeImage_group (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    (1 ∈ planeImage hS E) ∧
      (∀ a ∈ planeImage hS E, ∀ b ∈ planeImage hS E, a * b ∈ planeImage hS E) ∧
      ∀ a ∈ planeImage hS E, a * a = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_planeImage]
    exact ⟨1, E.one_mem, map_one (planeHom hS)⟩
  · intro a ha b hb
    rw [mem_planeImage] at ha hb ⊢
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y * z, E.mul_mem hy hz, map_mul (planeHom hS) y z⟩
  · intro a ha
    rw [mem_planeImage] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    rw [← map_mul]
    exact planeHom_eq_one_of_centralizes hS (y * y) fun v hv => hE.sq (y : X) hy v hv

theorem suppVec_mul (hS : PlaneSys V W) (hE : ActsElemAb V E)
    {y y' : normalizer (V : Set X)} (hy : (y : X) ∈ E)
    (hy' : (y' : X) ∈ E) (hy1 : planeHom hS y = 1) (hy'1 : planeHom hS y' = 1) :
    suppVec W (y * y') = suppVec W y + suppVec W y' := by
  classical
  funext i
  have hyI : InvolAct (W i) (y : X) := by
    refine ⟨?_, ?_⟩
    · intro a ha
      have hi : planeHom hS y i = i := by rw [hy1]; rfl
      exact (mem_plane_conj_iff hS y hi a).mpr ha
    · intro a ha
      exact hE.sq (y : X) hy a (hS.le i ha)
  have hy'I : InvolAct (W i) (y' : X) := by
    refine ⟨?_, ?_⟩
    · intro a ha
      have hi : planeHom hS y' i = i := by rw [hy'1]; rfl
      exact (mem_plane_conj_iff hS y' hi a).mpr ha
    · intro a ha
      exact hE.sq (y' : X) hy' a (hS.le i ha)
  have hcomm : ∀ a ∈ W i,
      (y : X) * (y' : X) * a * ((y : X) * (y' : X))⁻¹ =
        (y' : X) * (y : X) * a * ((y' : X) * (y : X))⁻¹ := by
    intro a ha
    exact hE.comm (y : X) hy (y' : X) hy' a (hS.le i ha)
  have hiff := actsNontriv_mul_iff (hS.card i) (fun a ha => hS.sq a (hS.le i ha)) hyI hy'I hcomm
  simp only [suppVec]
  change (if ActsNontriv (W i) ((y : X) * (y' : X)) then (1 : ZMod 2) else 0) =
    (if ActsNontriv (W i) (y : X) then 1 else 0) +
      (if ActsNontriv (W i) (y' : X) then 1 else 0)
  exact zmod_two_ite_add hiff

theorem suppSet_subspace (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    (0 ∈ suppSet hS E) ∧ ∀ x ∈ suppSet hS E, ∀ y ∈ suppSet hS E, x + y ∈ suppSet hS E := by
  classical
  constructor
  · rw [mem_suppSet]
    refine ⟨1, E.one_mem, map_one (planeHom hS), ?_⟩
    funext i
    have h1 : ¬ ActsNontriv (W i) (((1 : normalizer (V : Set X))) : X) :=
      not_actsNontriv_iff.mpr (fun a ha => by simp)
    simp only [suppVec]
    rw [if_neg h1]
    rfl
  · intro x hx z hz
    rw [mem_suppSet] at hx hz ⊢
    obtain ⟨y, hy, hy1, rfl⟩ := hx
    obtain ⟨y', hy', hy'1, rfl⟩ := hz
    refine ⟨y * y', E.mul_mem hy hy', ?_, ?_⟩
    · rw [map_mul, hy1, hy'1, mul_one]
    · exact suppVec_mul hS hE hy hy' hy1 hy'1

theorem suppSet_fixed (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    ∀ x ∈ suppSet hS E, ∀ a ∈ planeImage hS E, ∀ i, x (a i) = x i := by
  classical
  intro x hx a ha i
  rw [mem_suppSet] at hx
  rw [mem_planeImage] at ha
  obtain ⟨y, hy, hy1, rfl⟩ := hx
  obtain ⟨τ, hτ, rfl⟩ := ha
  have key : ∀ a ∈ V, (τ : X) * (y : X) * (τ : X)⁻¹ * a * ((τ : X) * (y : X) * (τ : X)⁻¹)⁻¹ =
      (y : X) * a * (y : X)⁻¹ := by
    intro a ha
    have hu : (τ : X)⁻¹ * a * (τ : X) ∈ V := by
      have h' := (Subgroup.mem_normalizer_iff.mp (τ⁻¹).2 a).mp ha
      simpa using h'
    have h := hE.comm (τ : X) hτ (y : X) hy ((τ : X)⁻¹ * a * (τ : X)) hu
    have e1 : (τ : X) * (y : X) * ((τ : X)⁻¹ * a * (τ : X)) * ((τ : X) * (y : X))⁻¹ =
        (τ : X) * (y : X) * (τ : X)⁻¹ * a * ((τ : X) * (y : X) * (τ : X)⁻¹)⁻¹ := by group
    have e2 : (y : X) * (τ : X) * ((τ : X)⁻¹ * a * (τ : X)) * ((y : X) * (τ : X))⁻¹ =
        (y : X) * a * (y : X)⁻¹ := by group
    rw [← e1, ← e2]
    exact h
  have hconj : ∀ j, ActsNontriv (W j) ((τ : X) * (y : X) * (τ : X)⁻¹) ↔
      ActsNontriv (W j) (y : X) := by
    intro j
    have h1 := not_actsNontriv_iff (A := W j) (y := (τ : X) * (y : X) * (τ : X)⁻¹)
    have h2 := not_actsNontriv_iff (A := W j) (y := (y : X))
    have h3 : (∀ a ∈ W j, (τ : X) * (y : X) * (τ : X)⁻¹ * a *
          ((τ : X) * (y : X) * (τ : X)⁻¹)⁻¹ = a) ↔ ∀ a ∈ W j, (y : X) * a * (y : X)⁻¹ = a :=
      forall₂_congr fun a ha => by rw [key a (hS.le j ha)]
    exact not_iff_not.mp (h1.trans (h3.trans h2.symm))
  have hiff : ActsNontriv (W (planeHom hS τ i)) (y : X) ↔ ActsNontriv (W i) (y : X) := by
    have h := actsNontriv_conj hS τ i (y : X)
    rwa [hconj (planeHom hS τ i)] at h
  simp only [suppVec]
  by_cases hp : ActsNontriv (W (planeHom hS τ i)) (y : X)
  · have hq : ActsNontriv (W i) (y : X) := hiff.mp hp
    simp [hp, hq]
  · have hq : ¬ ActsNontriv (W i) (y : X) := fun h => hp (hiff.mpr h)
    simp [hp, hq]

theorem suppSet_even (hS : PlaneSys V W) (hpar : PlaneParity V W) (hE : ActsElemAb V E) :
    ∀ x ∈ suppSet hS E, IsEvenVec x := by
  classical
  intro x hx
  rw [mem_suppSet] at hx
  obtain ⟨y, hy, hy1, rfl⟩ := hx
  have hmaps : ∀ i, ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W i := by
    intro i w hw
    have hi : planeHom hS y i = i := by rw [hy1]; rfl
    exact (mem_plane_conj_iff hS y hi w).mpr hw
  have hsq : ∀ v ∈ V, (y : X) * (y : X) * v * ((y : X) * (y : X))⁻¹ = v :=
    fun v hv => hE.sq (y : X) hy v hv
  have heven := hpar (y : X) (hE.le_normalizer hy) hmaps hsq
  have hcard : Nat.card {i : Fin 4 // ActsNontriv (W i) (y : X)} =
      (Finset.univ.filter (fun i => ActsNontriv (W i) (y : X))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : (∑ i : Fin 4, suppVec W y i) =
      ((Finset.univ.filter (fun i => ActsNontriv (W i) (y : X))).card : ZMod 2) := by
    simp only [suppVec]
    exact Finset.sum_boole _ _
  unfold IsEvenVec
  rw [hsum]
  exact (ZMod.natCast_eq_zero_iff_even).mpr (by rwa [hcard] at heven)

end CFSG.OddStandard.SmallF3.Omega
