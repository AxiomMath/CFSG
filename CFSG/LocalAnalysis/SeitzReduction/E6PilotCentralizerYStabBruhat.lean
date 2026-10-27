module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYStab
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYParabolic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

local instance e6CentralizerYStabBruhatNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def yLow : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1]]

@[expose] def yZr : List (Fin Tag.E6.rank → ℤ) := yU5 ++ yLow

@[expose] def yNegRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {δ | IsRoot .E6 δ ∧ height δ < 0 ∧ δ 0 = 0 ∧ δ 5 = 0}

theorem yLow_check :
    (∀ ζ ∈ yLow, ζ ∈ rootFinset .E6 ∧ 0 < height ζ) ∧ yZr.Nodup ∧
    (∀ ζ ∈ yZr, ∀ ζ' ∈ yZr, 0 ≤ iform ζ ζ') ∧
    (∀ δ ∈ rootFinset .E6, height δ < 0 → δ 0 = 0 → δ 5 = 0 →
      (yAlphaAS + δ ∈ rootFinset .E6 → yAlphaAS + δ ∈ yLow) ∧
      (yBetaAS + δ ∈ rootFinset .E6 → yBetaAS + δ ∈ yLow) ∧
      (∀ ζ ∈ yLow, ζ + δ ∈ rootFinset .E6 → ζ + δ ∈ yLow) ∧
      (∀ ζ ∈ yZr, δ ≠ ζ ∧ δ ≠ -ζ)) := by
  decide +kernel

section Mem


theorem mem_yZr_of_mem_yU5 {ζ : Fin Tag.E6.rank → ℤ} (h : ζ ∈ yU5) : ζ ∈ yZr :=
  List.mem_append_left _ h

theorem mem_yZr_of_mem_yLow {ζ : Fin Tag.E6.rank → ℤ} (h : ζ ∈ yLow) : ζ ∈ yZr :=
  List.mem_append_right _ h

theorem yAlphaAS_mem_yU5 : yAlphaAS ∈ yU5 := List.mem_cons_self

theorem yBetaAS_mem_yU5 : yBetaAS ∈ yU5 := List.mem_cons_of_mem _ List.mem_cons_self

theorem yZr_pos : ∀ ζ ∈ yZr, IsRoot .E6 ζ ∧ 0 < height ζ := by
  intro ζ hζ
  rcases List.mem_append.1 hζ with h | h
  · exact ⟨mem_rootFinset.1 (yU5_check.1 ζ h).1, (yU5_check.1 ζ h).2.1⟩
  · exact ⟨mem_rootFinset.1 (yLow_check.1 ζ h).1, (yLow_check.1 ζ h).2⟩

end Mem

section Groups


variable (K : Type) [Field K]

@[expose] noncomputable def yLowSpan : Subgroup (ModGL .E6 K) :=
  rootSpan .E6 K {ζ | ζ ∈ yLow}

@[expose] noncomputable def yNegLevi : Subgroup (ModGL .E6 K) :=
  rootSpan .E6 K yNegRoots

end Groups

section Products

variable {K : Type} [Field K]


@[expose] noncomputable def yListProd (L : List (Fin Tag.E6.rank → ℤ))
    (c : (Fin Tag.E6.rank → ℤ) → K) : ModGL .E6 K :=
  (L.map fun ζ => pinnedX .E6 K ζ (c ζ)).prod

theorem yListProd_zero (L : List (Fin Tag.E6.rank → ℤ)) :
    yListProd (K := K) L 0 = 1 := by
  simp [yListProd, pinnedX_zero]

theorem commute_pinnedX_of_mem_yZr {ζ ζ' : Fin Tag.E6.rank → ℤ} (hζ : ζ ∈ yZr) (hζ' : ζ' ∈ yZr)
    (c c' : K) : Commute (pinnedX .E6 K ζ c) (pinnedX .E6 K ζ' c') :=
  classD4_commute_pinnedX e6_simplyLaced (yZr_pos ζ hζ).1 (yZr_pos ζ' hζ').1
    (yLow_check.2.2.1 ζ hζ ζ' hζ') c c'

theorem commute_pinnedX_yListProd {L : List (Fin Tag.E6.rank → ℤ)} (hL : ∀ ζ ∈ L, ζ ∈ yZr)
    {ζ : Fin Tag.E6.rank → ℤ} (hζ : ζ ∈ yZr) (a : K) (c : (Fin Tag.E6.rank → ℤ) → K) :
    Commute (pinnedX .E6 K ζ a) (yListProd L c) :=
  Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.1 hx
    exact commute_pinnedX_of_mem_yZr hζ (hL ξ hξ) a (c ξ)

theorem yListProd_add {L : List (Fin Tag.E6.rank → ℤ)} (hL : ∀ ζ ∈ L, ζ ∈ yZr)
    (c c' : (Fin Tag.E6.rank → ℤ) → K) :
    yListProd L (c + c') = yListProd L c * yListProd L c' := by
  induction L with
  | nil => simp [yListProd]
  | cons ζ L ih =>
    have hζ := hL ζ List.mem_cons_self
    have hL' : ∀ ξ ∈ L, ξ ∈ yZr := fun ξ hξ => hL ξ (List.mem_cons_of_mem _ hξ)
    have e : yListProd (ζ :: L) (c + c') =
        pinnedX .E6 K ζ (c ζ) * pinnedX .E6 K ζ (c' ζ) * yListProd L (c + c') := by
      simp only [yListProd, List.map_cons, List.prod_cons, Pi.add_apply, pinnedX_add, mul_assoc]
    rw [e, ih hL']
    simp only [yListProd, List.map_cons, List.prod_cons]
    have hc := commute_pinnedX_yListProd (K := K) hL' hζ (c' ζ) c
    simp only [yListProd] at hc
    rw [mul_assoc, ← mul_assoc (pinnedX .E6 K ζ (c' ζ)), hc.eq]
    group

theorem yListProd_neg {L : List (Fin Tag.E6.rank → ℤ)} (hL : ∀ ζ ∈ L, ζ ∈ yZr)
    (c : (Fin Tag.E6.rank → ℤ) → K) : (yListProd L c)⁻¹ = yListProd L (-c) := by
  have h := yListProd_add (K := K) hL c (-c)
  rw [add_neg_cancel, yListProd_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm).symm

theorem pinnedX_eq_yListProd {L : List (Fin Tag.E6.rank → ℤ)} (hnd : L.Nodup)
    {ξ : Fin Tag.E6.rank → ℤ} (hξ : ξ ∈ L) (a : K) :
    pinnedX .E6 K ξ a = yListProd L (fun ζ => if ζ = ξ then a else 0) := by
  induction L with
  | nil => simp at hξ
  | cons ζ L ih =>
    rw [List.nodup_cons] at hnd
    simp only [yListProd, List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hξ with rfl | h
    · have h0 : (L.map fun ζ' => pinnedX .E6 K ζ' (if ζ' = ξ then a else 0)).prod = 1 := by
        rw [List.prod_eq_one]
        intro x hx
        obtain ⟨ζ', hζ', rfl⟩ := List.mem_map.1 hx
        have hne : ζ' ≠ ξ := fun e => hnd.1 (by subst e; exact hζ')
        simp only [hne, ↓reduceIte, pinnedX_zero]
      rw [h0]
      simp
    · have hne : ζ ≠ ξ := fun e => hnd.1 (by subst e; exact h)
      simp only [hne, ↓reduceIte, pinnedX_zero, one_mul]
      exact ih hnd.2 h

theorem exists_eq_yListProd_of_mem_rootSpan {L : List (Fin Tag.E6.rank → ℤ)} (hnd : L.Nodup)
    (hL : ∀ ζ ∈ L, ζ ∈ yZr) {g : ModGL .E6 K} (hg : g ∈ rootSpan .E6 K {ζ | ζ ∈ L}) :
    ∃ c : (Fin Tag.E6.rank → ℤ) → K, g = yListProd L c := by
  rw [rootSpan_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨ξ, hξ, a, rfl⟩ := hx
    exact ⟨_, pinnedX_eq_yListProd hnd hξ a⟩
  | one => exact ⟨0, (yListProd_zero L).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', (yListProd_add hL c c').symm⟩
  | inv x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨-c, yListProd_neg hL c⟩

end Products

section Neg

variable {K : Type} [Field K]


theorem conj_pinnedX_cases [CharP K 2] {δ ζ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ)
    (hζ : IsRoot .E6 ζ) (hne : δ ≠ ζ) (hne' : δ ≠ -ζ) (s l : K) :
    (IsRoot .E6 (δ + ζ) ∧ pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹ =
        pinnedX .E6 K (δ + ζ) (s * l) * pinnedX .E6 K ζ l) ∨
      pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹ = pinnedX .E6 K ζ l := by
  by_cases hr : IsRoot .E6 (δ + ζ)
  · left
    refine ⟨hr, ?_⟩
    obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ
      hζ hne hne').1 hr
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hε1 : (commConst Tag.E6 δ ζ (1, 1) : K) = 1 := by
      rcases hε with h | h
      · rw [h, Int.cast_one]
      · rw [h, Int.cast_neg, Int.cast_one]
        linear_combination -h2
    have hc := hcomm K s l
    rw [hε1, one_mul, commutatorElement_def] at hc
    rw [← hc]
    group
  · right
    have hc := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ hζ
      hne hne').2 hr K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _ (mem_rootSubgroup.2 ⟨l, rfl⟩)
    rw [hc.eq, mul_inv_cancel_right]

theorem commute_of_mem_yLowSpan {h : ModGL .E6 K} (hh : h ∈ yLowSpan K)
    {ζ : Fin Tag.E6.rank → ℤ} (hζ : ζ ∈ yZr) (c : K) : Commute h (pinnedX .E6 K ζ c) := by
  have hle : yLowSpan K ≤ centralizer ({pinnedX .E6 K ζ c} : Set (ModGL .E6 K)) := by
    refine iSup₂_le fun ξ hξ => (closure_le _).2 ?_
    rintro _ ⟨d, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (commute_pinnedX_of_mem_yZr (mem_yZr_of_mem_yLow hξ) hζ d c).eq
  exact mem_centralizer_singleton_iff.1 (hle hh)

theorem pinnedX_mem_normalizer_yLowSpan [CharP K 2] {δ : Fin Tag.E6.rank → ℤ}
    (hδ : δ ∈ yNegRoots) (s : K) :
    pinnedX .E6 K δ s ∈ normalizer (yLowSpan K : Set (ModGL .E6 K)) := by
  obtain ⟨hδr, hneg, h0, h5⟩ := hδ
  have hchk := yLow_check.2.2.2 δ (mem_rootFinset.2 hδr) hneg h0 h5
  have key : ∀ t : K, ∀ x ∈ {g | ∃ α ∈ {ζ | ζ ∈ yLow}, ∃ c : K, pinnedX .E6 K α c = g},
      pinnedX .E6 K δ t * x * (pinnedX .E6 K δ t)⁻¹ ∈ yLowSpan K := by
    rintro t _ ⟨ζ, hζ, c, rfl⟩
    have hζr := mem_rootFinset.1 (yLow_check.1 ζ hζ).1
    obtain ⟨hne, hne'⟩ := hchk.2.2.2 ζ (mem_yZr_of_mem_yLow hζ)
    rcases conj_pinnedX_cases (K := K) hδr hζr hne hne' t c with ⟨hr, e⟩ | e
    · rw [e]
      have hmem : δ + ζ ∈ yLow := by
        rw [add_comm]
        exact hchk.2.2.1 ζ hζ (by rw [add_comm]; exact mem_rootFinset.2 hr)
      exact mul_mem (pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yLow}) hmem _)
        (pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yLow}) hζ c)
    · rw [e]
      exact pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yLow}) hζ c
  have hspan : yLowSpan K = closure {g | ∃ α ∈ {ζ | ζ ∈ yLow}, ∃ c : K, pinnedX .E6 K α c = g} :=
    rootSpan_eq_closure K _
  rw [hspan]
  refine mem_normalizer_closure_of_conj (fun x hx => ?_) (fun x hx => ?_)
  · rw [← hspan]
    exact key s x hx
  · rw [← hspan]
    have e : (pinnedX .E6 K δ s)⁻¹ * x * pinnedX .E6 K δ s =
        pinnedX .E6 K δ (-s) * x * (pinnedX .E6 K δ (-s))⁻¹ := by
      rw [pinnedX_neg, pinnedX_neg, neg_neg]
    rw [e]
    exact key (-s) x hx

theorem yNegLevi_le_normalizer_yLowSpan [CharP K 2] :
    yNegLevi K ≤ normalizer (yLowSpan K : Set (ModGL .E6 K)) := by
  rw [yNegLevi, rootSpan_eq_closure, closure_le]
  rintro _ ⟨δ, hδ, s, rfl⟩
  exact pinnedX_mem_normalizer_yLowSpan hδ s

theorem conj_pinnedX_mem_of_neg [CharP K 2] {ζ : Fin Tag.E6.rank → ℤ}
    (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ yNegRoots) (s l : K) :
    (pinnedX .E6 K ζ l)⁻¹ * (pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹) ∈
      yLowSpan K := by
  have hζ5 : ζ ∈ yU5 := by rcases hζ with rfl | rfl <;> simp [yU5]
  have hζr := mem_rootFinset.1 (yU5_check.1 ζ hζ5).1
  obtain ⟨hδr, hneg, h0, h5⟩ := hδ
  have hchk := yLow_check.2.2.2 δ (mem_rootFinset.2 hδr) hneg h0 h5
  obtain ⟨hne, hne'⟩ := hchk.2.2.2 ζ (mem_yZr_of_mem_yU5 hζ5)
  rcases conj_pinnedX_cases (K := K) hδr hζr hne hne' s l with ⟨hr, e⟩ | e
  · have hmem : δ + ζ ∈ yLow := by
      rcases hζ with rfl | rfl
      · rw [add_comm]; exact hchk.1 (by rw [add_comm]; exact mem_rootFinset.2 hr)
      · rw [add_comm]; exact hchk.2.1 (by rw [add_comm]; exact mem_rootFinset.2 hr)
    have hX : pinnedX .E6 K (δ + ζ) (s * l) ∈ yLowSpan K :=
      pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yLow}) hmem (s * l)
    rw [e, (commute_of_mem_yLowSpan hX (mem_yZr_of_mem_yU5 hζ5) l).eq, ← mul_assoc,
      inv_mul_cancel, one_mul]
    exact hX
  · rw [e, inv_mul_cancel]
    exact one_mem _

theorem conj_pinnedX_mem_of_mem_yNegLevi [CharP K 2] {ζ : Fin Tag.E6.rank → ℤ}
    (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) {u : ModGL .E6 K} (hu : u ∈ yNegLevi K) (l : K) :
    (pinnedX .E6 K ζ l)⁻¹ * (u * pinnedX .E6 K ζ l * u⁻¹) ∈ yLowSpan K := by
  have hN := yNegLevi_le_normalizer_yLowSpan (K := K)
  have hu' := hu
  rw [yNegLevi, rootSpan_eq_closure] at hu'
  induction hu' using Subgroup.closure_induction generalizing l with
  | mem x hx =>
    obtain ⟨δ, hδ, s, rfl⟩ := hx
    exact conj_pinnedX_mem_of_neg hζ hδ s l
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxN : x ∈ normalizer (yLowSpan K : Set (ModGL .E6 K)) := hN (by
      rw [yNegLevi, rootSpan_eq_closure]; exact hx)
    have e : (pinnedX .E6 K ζ l)⁻¹ * (x * y * pinnedX .E6 K ζ l * (x * y)⁻¹) =
        ((pinnedX .E6 K ζ l)⁻¹ * (x * pinnedX .E6 K ζ l * x⁻¹)) *
          (x * ((pinnedX .E6 K ζ l)⁻¹ * (y * pinnedX .E6 K ζ l * y⁻¹)) * x⁻¹) := by group
    rw [e]
    exact mul_mem (ihx (by rw [yNegLevi, rootSpan_eq_closure]; exact hx) l)
      ((mem_normalizer_iff.1 hxN _).1 (ihy (by rw [yNegLevi, rootSpan_eq_closure]; exact hy) l))
  | inv x hx ihx =>
    have hxN : x ∈ normalizer (yLowSpan K : Set (ModGL .E6 K)) := hN (by
      rw [yNegLevi, rootSpan_eq_closure]; exact hx)
    have e : (pinnedX .E6 K ζ l)⁻¹ * (x⁻¹ * pinnedX .E6 K ζ l * x⁻¹⁻¹) =
        x⁻¹ * ((pinnedX .E6 K ζ l)⁻¹ * (x * pinnedX .E6 K ζ l * x⁻¹))⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hxN) _).1
      (inv_mem (ihx (by rw [yNegLevi, rootSpan_eq_closure]; exact hx) l))

theorem exists_conj_e6ASRep_one_of_mem_yNegLevi [CharP K 2] {v : ModGL .E6 K}
    (hv : v ∈ yNegLevi K) : ∃ z ∈ yLowSpan K,
      v * (e6ASRep K 1 : ModGL .E6 K) * v⁻¹ =
        pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * z := by
  have h1 := conj_pinnedX_mem_of_mem_yNegLevi (K := K) (Or.inl rfl) hv 1
  have h2 := conj_pinnedX_mem_of_mem_yNegLevi (K := K) (Or.inr rfl) hv 1
  set z₁ := (pinnedX .E6 K yAlphaAS 1)⁻¹ * (v * pinnedX .E6 K yAlphaAS 1 * v⁻¹) with hz₁
  set z₂ := (pinnedX .E6 K yBetaAS 1)⁻¹ * (v * pinnedX .E6 K yBetaAS 1 * v⁻¹) with hz₂
  refine ⟨z₁ * z₂, mul_mem h1 h2, ?_⟩
  have e1 : v * pinnedX .E6 K yAlphaAS 1 * v⁻¹ = pinnedX .E6 K yAlphaAS 1 * z₁ := by
    rw [hz₁]; group
  have e2 : v * pinnedX .E6 K yBetaAS 1 * v⁻¹ = pinnedX .E6 K yBetaAS 1 * z₂ := by
    rw [hz₂]; group
  have hc : Commute z₁ (pinnedX .E6 K yBetaAS 1) :=
    commute_of_mem_yLowSpan h1 (mem_yZr_of_mem_yU5 yBetaAS_mem_yU5) 1
  rw [coe_e6ASRep_one_eq]
  calc v * (pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1) * v⁻¹
      = (v * pinnedX .E6 K yAlphaAS 1 * v⁻¹) * (v * pinnedX .E6 K yBetaAS 1 * v⁻¹) := by group
    _ = pinnedX .E6 K yAlphaAS 1 * (z₁ * pinnedX .E6 K yBetaAS 1) * z₂ := by
        rw [e1, e2]; group
    _ = _ := by rw [hc.eq]; group

theorem exists_conj_pinnedX_pair_of_mem_posUnipotent [CharP K 2] {u : ModGL .E6 K}
    (hu : u ∈ posUnipotent .E6 K) (a b : K) : ∃ z ∈ yHighSpan K,
      u * (pinnedX .E6 K yAlphaAS a * pinnedX .E6 K yBetaAS b) * u⁻¹ =
        pinnedX .E6 K yAlphaAS a * pinnedX .E6 K yBetaAS b * z := by
  have h1 := conj_pinnedX_mem_of_mem_posUnipotent (K := K) (Or.inl rfl) hu a
  have h2 := conj_pinnedX_mem_of_mem_posUnipotent (K := K) (Or.inr rfl) hu b
  set z₁ := (pinnedX .E6 K yAlphaAS a)⁻¹ * (u * pinnedX .E6 K yAlphaAS a * u⁻¹) with hz₁
  set z₂ := (pinnedX .E6 K yBetaAS b)⁻¹ * (u * pinnedX .E6 K yBetaAS b * u⁻¹) with hz₂
  refine ⟨z₁ * z₂, mul_mem h1 h2, ?_⟩
  have e1 : u * pinnedX .E6 K yAlphaAS a * u⁻¹ = pinnedX .E6 K yAlphaAS a * z₁ := by
    rw [hz₁]; group
  have e2 : u * pinnedX .E6 K yBetaAS b * u⁻¹ = pinnedX .E6 K yBetaAS b * z₂ := by
    rw [hz₂]; group
  have hc : Commute z₁ (pinnedX .E6 K yBetaAS b) := commute_of_mem_yHighSpan h1 yBetaAS_mem_yU5 b
  calc u * (pinnedX .E6 K yAlphaAS a * pinnedX .E6 K yBetaAS b) * u⁻¹
      = (u * pinnedX .E6 K yAlphaAS a * u⁻¹) * (u * pinnedX .E6 K yBetaAS b * u⁻¹) := by group
    _ = pinnedX .E6 K yAlphaAS a * (z₁ * pinnedX .E6 K yBetaAS b) * z₂ := by
        rw [e1, e2]; group
    _ = _ := by rw [hc.eq]; group

end Neg

theorem yZr_mem_check :
    (∀ ζ ∈ yHigh, ζ ≠ yAlphaAS ∧ ζ ≠ yBetaAS ∧ ζ ∉ yLow) ∧
      (∀ ζ ∈ yLow, ζ ≠ yAlphaAS ∧ ζ ≠ yBetaAS) ∧ yAlphaAS ≠ yBetaAS ∧ yHigh.Nodup ∧
      yLow.Nodup := by
  decide +kernel

section Bruhat

variable {K : Type} [Field K]


theorem pair_mul_eq_yListProd_yZr (a b : K) (c d : (Fin Tag.E6.rank → ℤ) → K) :
    pinnedX .E6 K yAlphaAS a * pinnedX .E6 K yBetaAS b * yListProd yHigh c * yListProd yLow d =
      yListProd yZr (fun ζ => if ζ = yAlphaAS then a else if ζ = yBetaAS then b else
        if ζ ∈ yLow then d ζ else c ζ) := by
  obtain ⟨hH, hL, hab, -, -⟩ := yZr_mem_check
  have eH : yListProd (K := K) yHigh c = yListProd yHigh (fun ζ => if ζ = yAlphaAS then a else
      if ζ = yBetaAS then b else if ζ ∈ yLow then d ζ else c ζ) := by
    refine congrArg List.prod (List.map_congr_left fun ζ hζ => ?_)
    obtain ⟨h1, h2, h3⟩ := hH ζ hζ
    simp only [h1, h2, h3, ↓reduceIte]
  have eL : yListProd (K := K) yLow d = yListProd yLow (fun ζ => if ζ = yAlphaAS then a else
      if ζ = yBetaAS then b else if ζ ∈ yLow then d ζ else c ζ) := by
    refine congrArg List.prod (List.map_congr_left fun ζ hζ => ?_)
    obtain ⟨h1, h2⟩ := hL ζ hζ
    simp only [h1, h2, hζ, ↓reduceIte]
  rw [eH, eL]
  simp only [yListProd, yZr, yU5, List.cons_append, List.map_cons, List.prod_cons, List.map_append,
    List.prod_append, ↓reduceIte, hab.symm]
  group

theorem exists_bruhat_factors_of_mem_centralizer [CharP K 2] {g : ModGL .E6 K}
    (hg : g ∈ adjointGroup .E6 K)
    (hgy : g ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))) :
    ∃ w : WeylGroup .E6, w ∈ parabolicWeylGroup .E6 nodes16 ∧
      ∃ h ∈ torusGroup .E6 K ⊓ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)),
      ∃ u ∈ posUnipotent .E6 K ⊓ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)),
      ∃ v ∈ rootSpan .E6 K (inversionSet w) ⊓
        centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)),
        canonicalRep (coxeterSystem .E6) K w ∈
          centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ∧
        ((w • yAlphaAS = yAlphaAS ∧ w • yBetaAS = yBetaAS) ∨
          (w • yAlphaAS = yBetaAS ∧ w • yBetaAS = yAlphaAS)) ∧
        g = h * u * canonicalRep (coxeterSystem .E6) K w * v := by
  set y := (e6ASRep K 1 : ModGL .E6 K) with hydef
  have hy : y = pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 := coe_e6ASRep_one_eq
  have hαr := mem_rootFinset.1 (yU5_check.1 _ yAlphaAS_mem_yU5).1
  have hβr := mem_rootFinset.1 (yU5_check.1 _ yBetaAS_mem_yU5).1
  have hcommαβ : ∀ a b : K, Commute (pinnedX .E6 K yAlphaAS a) (pinnedX .E6 K yBetaAS b) :=
    fun a b => commute_pinnedX_of_mem_yZr (mem_yZr_of_mem_yU5 yAlphaAS_mem_yU5)
      (mem_yZr_of_mem_yU5 yBetaAS_mem_yU5) a b
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := (bijOn_bruhatCell (K := K) w).surjOn hw
  simp only at hbv
  have hb' : b ∈ (torusGroup .E6 K : Set (ModGL .E6 K)) *
      (posUnipotent .E6 K : Set (ModGL .E6 K)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ torusGroup_le_normalizer_posUnipotent]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  have hvU : v ∈ posUnipotent .E6 K :=
    rootSpan_le_posUnipotent (fun α hα => inversionSet_pos (w := w) hα) hv
  have hgc : g * y = y * g := mem_centralizer_singleton_iff.1 hgy
  have key : n * (v * y * v⁻¹) * n⁻¹ = (h * u)⁻¹ * y * (h * u) := by
    rw [← hbv] at hgc
    calc n * (v * y * v⁻¹) * n⁻¹
        = (h * u)⁻¹ * (h * u * n * v * y) * (h * u * n * v)⁻¹ * (h * u) := by group
      _ = (h * u)⁻¹ * (y * (h * u * n * v)) * (h * u * n * v)⁻¹ * (h * u) := by rw [hgc]
      _ = (h * u)⁻¹ * y * (h * u) := by group
  obtain ⟨z, hz, hvz⟩ := exists_conj_pinnedX_pair_of_mem_posUnipotent (K := K) hvU 1 1
  have hhinv : h⁻¹ ∈ torusGroup .E6 K := inv_mem hh
  have hty : h⁻¹ * y * h⁻¹⁻¹ = pinnedX .E6 K yAlphaAS (torusRootChar h⁻¹ yAlphaAS * 1) *
      pinnedX .E6 K yBetaAS (torusRootChar h⁻¹ yBetaAS * 1) := by
    rw [hy, ← conj_pinnedX_of_mem_torusGroup hhinv hαr, ← conj_pinnedX_of_mem_torusGroup hhinv hβr]
    group
  set a := torusRootChar h⁻¹ yAlphaAS * 1 with ha
  set b' := torusRootChar h⁻¹ yBetaAS * 1 with hb'def
  obtain ⟨z', hz', huz⟩ := exists_conj_pinnedX_pair_of_mem_posUnipotent (K := K) (inv_mem hu) a b'
  have hRHS : (h * u)⁻¹ * y * (h * u) =
      pinnedX .E6 K yAlphaAS a * pinnedX .E6 K yBetaAS b' * z' := by
    rw [← huz, ← hty]
    group
  have hLHS : v * y * v⁻¹ = pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * z := by
    rw [hy]; exact hvz
  obtain ⟨c, hc⟩ := exists_eq_yListProd_of_mem_rootSpan (K := K) yZr_mem_check.2.2.2.1
    (fun ζ hζ => mem_yZr_of_mem_yU5 (mem_yU5_of_mem_yHigh hζ)) hz
  set c₅ : (Fin Tag.E6.rank → ℤ) → K := fun ζ => if ζ = yAlphaAS then 1 else
    if ζ = yBetaAS then 1 else c ζ with hc₅
  have hc₅α : c₅ yAlphaAS ≠ 0 := by simp [hc₅]
  have hc₅β : c₅ yBetaAS ≠ 0 := by simp [hc₅, yZr_mem_check.2.2.1.symm]
  have hprod5 : (yU5.map fun ζ => pinnedX .E6 K ζ (c₅ ζ)).prod =
      pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * z := by
    rw [hc]
    have eH : yListProd (K := K) yHigh c = yListProd yHigh c₅ := by
      refine congrArg List.prod (List.map_congr_left fun ζ hζ => ?_)
      obtain ⟨h1, h2, -⟩ := yZr_mem_check.1 ζ hζ
      simp only [hc₅, h1, h2, ↓reduceIte]
    rw [eH]
    simp only [yListProd, yU5, List.map_cons, List.prod_cons, hc₅, ↓reduceIte,
      yZr_mem_check.2.2.1.symm, mul_assoc]
  have hin5 : n * (yU5.map fun ζ => pinnedX .E6 K ζ (c₅ ζ)).prod * n⁻¹ ∈
      rootSpan .E6 K {ζ | ζ ∈ yU5} := by
    rw [hprod5, ← hLHS, key, hRHS]
    have hle : yHighSpan K ≤ rootSpan .E6 K {ζ | ζ ∈ yU5} :=
      rootSpan_mono fun ζ hζ => mem_yU5_of_mem_yHigh hζ
    exact mul_mem (mul_mem (pinnedX_mem_rootSpan (S := {ζ | ζ ∈ yU5}) yAlphaAS_mem_yU5 a)
      (pinnedX_mem_rootSpan (S := {ζ | ζ ∈ yU5}) yBetaAS_mem_yU5 b')) (hle hz')
  obtain ⟨hwα, hwβ⟩ := smul_mem_yU5_of_conj w c₅ hc₅α hc₅β hin5
  have hwJ : w ∈ parabolicWeylGroup .E6 nodes16 :=
    mem_parabolicWeylGroup_nodes16_of_smul _ w rfl (smul_yLamAS_of_mem_yU5 hwα hwβ)
  have h0 : iform (w • yAlphaAS) (w • yBetaAS) = 0 := by
    rw [iform_smul]; exact yLevel_check.2.2.2.2
  have hpair := yU5_check.2.2.2.2.1 _ hwα _ hwβ h0
  have hny : n * y * n⁻¹ = y := by
    rw [hy]
    have e : n * (pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1) * n⁻¹ =
        (n * pinnedX .E6 K yAlphaAS 1 * n⁻¹) * (n * pinnedX .E6 K yBetaAS 1 * n⁻¹) := by group
    rw [e, hn, canonicalRep_mul_pinnedX_mul_inv_of_charTwo w hαr,
      canonicalRep_mul_pinnedX_mul_inv_of_charTwo w hβr]
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact (hcommαβ 1 1).eq.symm
  have hnC : n ∈ centralizer ({y} : Set (ModGL .E6 K)) := by
    refine mem_centralizer_singleton_iff.2 ?_
    calc n * y = (n * y * n⁻¹) * n := by group
      _ = y * n := by rw [hny]
  have hv' : n * v * n⁻¹ ∈ yNegLevi K := by
    have hS : ∀ α ∈ inversionSet w, IsRoot .E6 α := fun α hα => hα.1
    have h1 := canonicalRep_conj_mem_rootSpan (K := K) (w := w) hS hv
    refine rootSpan_mono ?_ h1
    rintro _ ⟨δ, hδ, rfl⟩
    have hδJ := inversionSet_subset_parabolicPosRoots hwJ hδ
    have hwδ := smul_mem_parabolicRoots hwJ hδJ.1
    exact ⟨hwδ.1, hδ.2.2.2, hwδ.2 0 (by simp [nodes16]), hwδ.2 5 (by simp [nodes16])⟩
  obtain ⟨zl, hzl, hv'y⟩ := exists_conj_e6ASRep_one_of_mem_yNegLevi (K := K) hv'
  have hv'eq : (n * v * n⁻¹) * y * (n * v * n⁻¹)⁻¹ = (h * u)⁻¹ * y * (h * u) := by
    calc (n * v * n⁻¹) * y * (n * v * n⁻¹)⁻¹ = n * (v * (n⁻¹ * y * n) * v⁻¹) * n⁻¹ := by group
      _ = n * (v * y * v⁻¹) * n⁻¹ := by
          rw [show n⁻¹ * y * n = y by
            calc n⁻¹ * y * n = n⁻¹ * (n * y * n⁻¹) * n := by rw [hny]
              _ = y := by group]
      _ = _ := key
  obtain ⟨cl, hcl⟩ := exists_eq_yListProd_of_mem_rootSpan (K := K) yZr_mem_check.2.2.2.2
    (fun ζ hζ => mem_yZr_of_mem_yLow hζ) hzl
  obtain ⟨ch, hch⟩ := exists_eq_yListProd_of_mem_rootSpan (K := K) yZr_mem_check.2.2.2.1
    (fun ζ hζ => mem_yZr_of_mem_yU5 (mem_yU5_of_mem_yHigh hζ)) hz'
  have hE : yListProd yZr (fun ζ => if ζ = yAlphaAS then (1 : K) else if ζ = yBetaAS then 1 else
        if ζ ∈ yLow then cl ζ else 0) =
      yListProd yZr (fun ζ => if ζ = yAlphaAS then a else if ζ = yBetaAS then b' else
        if ζ ∈ yLow then 0 else ch ζ) := by
    have hz0 : ∀ L : List (Fin Tag.E6.rank → ℤ), yListProd (K := K) L (fun _ => 0) = 1 :=
      fun L => yListProd_zero L
    rw [← pair_mul_eq_yListProd_yZr, ← pair_mul_eq_yListProd_yZr, hz0, hz0,
      mul_one, mul_one, ← hcl, ← hch, ← hv'y, ← hRHS, hydef]
    exact hv'eq
  have hinj := pinnedX_list_prod_injective (R := K) yZr yLow_check.2.1 yZr_pos _ _ hE
  have hAα := hinj yAlphaAS (mem_yZr_of_mem_yU5 yAlphaAS_mem_yU5)
  have hAβ := hinj yBetaAS (mem_yZr_of_mem_yU5 yBetaAS_mem_yU5)
  simp only [↓reduceIte, yZr_mem_check.2.2.1.symm] at hAα hAβ
  have hz'1 : z' = 1 := by
    rw [hch, yListProd, List.prod_eq_one]
    intro x hx
    obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hx
    have hζ8 := hinj ζ (mem_yZr_of_mem_yU5 (mem_yU5_of_mem_yHigh hζ))
    obtain ⟨h1, h2, h3⟩ := yZr_mem_check.1 ζ hζ
    simp only [h1, h2, h3, ↓reduceIte] at hζ8
    rw [← hζ8, pinnedX_zero]
  have hzl1 : zl = 1 := by
    rw [hcl, yListProd, List.prod_eq_one]
    intro x hx
    obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.1 hx
    have hζ8 := hinj ζ (mem_yZr_of_mem_yLow hζ)
    obtain ⟨h1, h2⟩ := yZr_mem_check.2.1 ζ hζ
    simp only [h1, h2, hζ, ↓reduceIte] at hζ8
    rw [hζ8, pinnedX_zero]
  have hAy : (h * u)⁻¹ * y * (h * u) = y := by
    rw [hRHS, hz'1, mul_one, ← hAα, ← hAβ, hy]
  have hv'C : (n * v * n⁻¹) * y * (n * v * n⁻¹)⁻¹ = y := by
    rw [hv'y, hzl1, mul_one, hy]
  have hhC : h * y = y * h := by
    have : h⁻¹ * y * h⁻¹⁻¹ = y := by rw [hty, ← hAα, ← hAβ, hy]
    calc h * y = h * (h⁻¹ * y * h⁻¹⁻¹) := by rw [this]
      _ = y * h := by group
  have huC : u * y = y * u := by
    have e1 : (h * u) * y = y * (h * u) := by
      calc (h * u) * y = (h * u) * ((h * u)⁻¹ * y * (h * u)) := by rw [hAy]
        _ = y * (h * u) := by group
    calc u * y = h⁻¹ * ((h * u) * y) := by group
      _ = h⁻¹ * (y * (h * u)) := by rw [e1]
      _ = h⁻¹ * y * h * u := by group
      _ = h⁻¹ * (h * y) * u := by rw [mul_assoc h⁻¹ y h, ← hhC]
      _ = y * u := by group
  have hvC : v * y = y * v := by
    have e1 : (n * v * n⁻¹) * y = y * (n * v * n⁻¹) := by
      calc (n * v * n⁻¹) * y = ((n * v * n⁻¹) * y * (n * v * n⁻¹)⁻¹) * (n * v * n⁻¹) := by group
        _ = y * (n * v * n⁻¹) := by rw [hv'C]
    have e2 : n⁻¹ * y * n = y := by
      calc n⁻¹ * y * n = n⁻¹ * (n * y * n⁻¹) * n := by rw [hny]
        _ = y := by group
    calc v * y = n⁻¹ * ((n * v * n⁻¹) * (n * y * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * v * n⁻¹) * y) * n := by rw [hny]
      _ = n⁻¹ * (y * (n * v * n⁻¹)) * n := by rw [e1]
      _ = (n⁻¹ * y * n) * v := by group
      _ = y * v := by rw [e2]
  refine ⟨w, hwJ, h, mem_inf.2 ⟨hh, mem_centralizer_singleton_iff.2 hhC⟩, u,
    mem_inf.2 ⟨hu, mem_centralizer_singleton_iff.2 huC⟩, v,
    mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 hvC⟩, hnC, hpair, hbv.symm⟩

end Bruhat

section U3

variable {K : Type} [Field K]


theorem mem_parabolicLeviUnipotent_of_mem_posUnipotent (J : Set (Fin Tag.E6.rank))
    {u : ModGL .E6 K} (hu : u ∈ posUnipotent .E6 K) (huL : u ∈ parabolicLevi .E6 K J) :
    u ∈ parabolicLeviUnipotent .E6 K J := by
  obtain ⟨-, -, -, hML, hQM, -, -, hB, -, hVM, -⟩ := parabolic_root_radical_Levi_factors .E6 K J
  have huB : u ∈ (borelGroup .E6 K : Set (ModGL .E6 K)) := mem_sup_right hu
  rw [hB] at huB
  obtain ⟨q, hq, tv, htv, rfl⟩ := huB
  obtain ⟨t, ht, v, hv, rfl⟩ := htv
  have htM : t ∈ parabolicLevi .E6 K J := torusGroup_le_parabolicLevi J ht
  have hq1 : q = 1 := by
    have hqM : q ∈ parabolicLevi .E6 K J := by
      have e : q = (q * (t * v)) * (t * v)⁻¹ := by group
      rw [e]
      exact mul_mem huL (inv_mem (mul_mem htM (hVM hv)))
    have h := mem_inf.2 ⟨hq, hqM⟩
    rwa [hQM, mem_bot] at h
  subst hq1
  have htU : t ∈ posUnipotent .E6 K := by
    have hvU : v ∈ posUnipotent .E6 K :=
      rootSpan_le_posUnipotent (fun α hα => hα.2) hv
    have e : t = (1 * (t * v)) * v⁻¹ := by group
    rw [e]
    exact mul_mem hu (inv_mem hvU)
  have h := mem_inf.2 ⟨ht, htU⟩
  rw [torusGroup_inf_posUnipotent, mem_bot] at h
  subst h
  simpa using hv

theorem leviStabilizerAS_of_unipotent [CharP K 2]
    (hP4 : ∀ u ∈ parabolicLeviUnipotent .E6 K nodes16,
      u ∈ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) → u ∈ yLeviF4 K)
    (hP5 : ∀ w ∈ parabolicWeylGroup .E6 nodes16,
      ((w • yAlphaAS = yAlphaAS ∧ w • yBetaAS = yBetaAS) ∨
        (w • yAlphaAS = yBetaAS ∧ w • yBetaAS = yAlphaAS)) →
      canonicalRep (coxeterSystem .E6) K w ∈ yLeviF4 K) :
    LeviStabilizerAS K := by
  intro m hmL hmy
  have hmC : m ∈ adjointGroup .E6 K := parabolicLevi_le_adjointGroup (τ := .E6) (K := K) nodes16 hmL
  obtain ⟨w, hwJ, h, hh, u, hu, v, hv, -, hab, rfl⟩ :=
    exists_bruhat_factors_of_mem_centralizer hmC hmy
  set n := canonicalRep (coxeterSystem .E6) K w
  have hnL : n ∈ parabolicLevi .E6 K nodes16 := canonicalRep_mem_parabolicLevi hwJ
  have hhL : h ∈ parabolicLevi .E6 K nodes16 := torusGroup_le_parabolicLevi nodes16 (mem_inf.1 hh).1
  have hvV : v ∈ parabolicLeviUnipotent .E6 K nodes16 :=
    rootSpan_mono (inversionSet_subset_parabolicPosRoots hwJ) (mem_inf.1 hv).1
  have hvL : v ∈ parabolicLevi .E6 K nodes16 :=
    parabolicLeviUnipotent_le_parabolicLevi (K := K) nodes16 hvV
  have huL : u ∈ parabolicLevi .E6 K nodes16 := by
    have e : u = h⁻¹ * (h * u * n * v) * v⁻¹ * n⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hhL) hmL) (inv_mem hvL)) (inv_mem hnL)
  have hu' := hP4 u (mem_parabolicLeviUnipotent_of_mem_posUnipotent nodes16 (mem_inf.1 hu).1 huL)
    (mem_inf.1 hu).2
  have hv' := hP4 v hvV (mem_inf.1 hv).2
  have hn' := hP5 w hwJ hab
  have e : h * u * n * v = h * (u * n * v) := by group
  rw [e]
  exact mul_mem (mem_sup_right hh) (mem_sup_left (mul_mem (mul_mem hu' hn') hv'))

end U3

end CFSG.SeitzReduction.E6Pilot
