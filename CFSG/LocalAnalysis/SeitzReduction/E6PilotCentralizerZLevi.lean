module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZ

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e6CentralizerZLeviNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]


section General

variable {τ : Tag}

theorem list_sum_single_apply' {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    (β₀ : Fin τ.rank → ℤ) (v : K) :
    (l.map fun β => (Pi.single β₀ v : (Fin τ.rank → ℤ) → K) β).sum =
      if β₀ ∈ l then v else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases ha : a = β₀
    · subst ha
      rw [Pi.single_eq_same, ite_eq_left List.mem_cons_self, ite_eq_right hnd.1, add_zero]
    · rw [Pi.single_eq_of_ne ha, zero_add]
      by_cases hb : β₀ ∈ l
      · rw [ite_eq_left hb, ite_eq_left (List.mem_cons_of_mem _ hb)]
      · have : β₀ ∉ a :: l := by
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm ha, hb⟩
        rw [ite_eq_right hb, ite_eq_right this]

theorem conjCoeff_apply {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    (hlr : ∀ β ∈ l, IsRoot τ β) (α : Fin τ.rank → ℤ) (t : K) (c : (Fin τ.rank → ℤ) → K)
    {ρ : Fin τ.rank → ℤ} (hρ : ρ ∈ l) :
    conjCoeff α t l c ρ = c ρ + if ρ - α ∈ l ∧ α ≠ ρ - α then t * c (ρ - α) else 0 := by
  classical
  rw [conjCoeff, list_sum_apply, List.map_map]
  have e : ∀ β ∈ l, ((fun f : (Fin τ.rank → ℤ) → K => f ρ) ∘ fun β => Pi.single β (c β) +
      if α ≠ β ∧ IsRoot τ (α + β) then Pi.single (α + β) (t * c β) else 0) β =
      (Pi.single β (c β) : (Fin τ.rank → ℤ) → K) ρ +
        (Pi.single (ρ - α) (if α ≠ ρ - α then t * c (ρ - α) else 0) :
          (Fin τ.rank → ℤ) → K) β := by
    intro β _
    simp only [Function.comp_apply, Pi.add_apply]
    congr 1
    by_cases hβ : β = ρ - α
    · subst hβ
      have hs : α + (ρ - α) = ρ := by abel
      rw [Pi.single_eq_same]
      by_cases hne : α ≠ ρ - α
      · have hr : IsRoot τ (α + (ρ - α)) := by rw [hs]; exact hlr ρ hρ
        rw [ite_eq_left ⟨hne, hr⟩, ite_eq_left hne, hs, Pi.single_eq_same]
      · rw [ite_eq_right fun h => hne h.1, ite_eq_right hne]
        rfl
    · have hs : α + β ≠ ρ := fun h => hβ (by rw [← h]; abel)
      rw [Pi.single_eq_of_ne hβ]
      split_ifs
      · exact Pi.single_eq_of_ne (Ne.symm hs) _
      · rfl
  rw [List.map_congr_left e, List.sum_map_add, list_sum_single_apply hnd hρ c,
    list_sum_single_apply' hnd]
  congr 1
  by_cases h1 : ρ - α ∈ l <;> by_cases h2 : α ≠ ρ - α <;> simp [h1, h2]

end General

@[expose] def zPairCheck (a b : Fin Tag.E6.rank → ℤ) : Bool :=
  zPsi.all fun ρ =>
    (decide (ρ - b ∈ zPsi ∧ b ≠ ρ - b ∧ ρ - b ∈ zFrame) ==
      decide (ρ - a ∈ zPsi ∧ a ≠ ρ - a ∧ ρ - a ∈ zFrame)) &&
    !decide (ρ - a ∈ zPsi ∧ a ≠ ρ - a ∧ ρ - a - b ∈ zPsi ∧ b ≠ ρ - a - b ∧ ρ - a - b ∈ zFrame)

theorem zCoeff_eq_zero_of_not_mem {β : Fin Tag.E6.rank → ℤ} (h : β ∉ zFrame) :
    (zCoeff : (Fin Tag.E6.rank → ℤ) → K) β = 0 := by
  simp only [zCoeff]
  rw [ite_eq_right h]

theorem zCoeff_eq_one_of_mem {β : Fin Tag.E6.rank → ℤ} (h : β ∈ zFrame) :
    (zCoeff : (Fin Tag.E6.rank → ℤ) → K) β = 1 := by
  simp only [zCoeff]
  rw [ite_eq_left h]

theorem conj_pair_zAS [CharP K 2] {a b : Fin Tag.E6.rank → ℤ} (ha : IsRoot .E6 a)
    (ha3 : a 3 = 0) (hb : IsRoot .E6 b) (hb3 : b 3 = 0) (h : zPairCheck a b = true) (t : K) :
    pinnedX .E6 K a t * pinnedX .E6 K b t * zAS K * (pinnedX .E6 K a t * pinnedX .E6 K b t)⁻¹ =
      zAS K := by
  have hr : ∀ β ∈ zPsi, IsRoot .E6 β := fun _ hβ => isRoot_of_mem_zPsi hβ
  have key : ∀ ρ ∈ zPsi, conjCoeff a t zPsi (conjCoeff b t zPsi zCoeff) ρ = zCoeff ρ := by
    intro ρ hρ
    have hc := List.all_eq_true.1 h ρ hρ
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_decide] at hc
    rw [conjCoeff_apply zPsi_nodup hr a t _ hρ, conjCoeff_apply zPsi_nodup hr b t _ hρ]
    by_cases hA : ρ - a ∈ zPsi ∧ a ≠ ρ - a
    · rw [ite_eq_left hA, conjCoeff_apply zPsi_nodup hr b t _ hA.1]
      have hA' : (if ρ - a - b ∈ zPsi ∧ b ≠ ρ - a - b then t * zCoeff (ρ - a - b) else 0) =
          (0 : K) := by
        split_ifs with h3
        · rw [zCoeff_eq_zero_of_not_mem fun hf => hc.2 ⟨hA.1, hA.2, h3.1, h3.2, hf⟩, mul_zero]
        · rfl
      have hB : (if ρ - b ∈ zPsi ∧ b ≠ ρ - b then t * zCoeff (ρ - b) else 0) =
          t * (zCoeff : (Fin Tag.E6.rank → ℤ) → K) (ρ - a) := by
        by_cases hfa : ρ - a ∈ zFrame
        · have hb' := hc.1.2 ⟨hA.1, hA.2, hfa⟩
          rw [ite_eq_left ⟨hb'.1, hb'.2.1⟩, zCoeff_eq_one_of_mem hb'.2.2,
            zCoeff_eq_one_of_mem hfa]
        · rw [zCoeff_eq_zero_of_not_mem hfa, mul_zero]
          split_ifs with hB'
          · rw [zCoeff_eq_zero_of_not_mem fun hf => hfa (hc.1.1 ⟨hB'.1, hB'.2, hf⟩).2.2,
              mul_zero]
          · rfl
      rw [hA', hB, add_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [ite_eq_right hA, add_zero]
      split_ifs with hB'
      · rw [zCoeff_eq_zero_of_not_mem fun hf => hA ⟨(hc.1.1 ⟨hB'.1, hB'.2, hf⟩).1,
          (hc.1.1 ⟨hB'.1, hB'.2, hf⟩).2.1⟩, mul_zero, add_zero]
      · rw [add_zero]
  calc pinnedX .E6 K a t * pinnedX .E6 K b t * zAS K * (pinnedX .E6 K a t * pinnedX .E6 K b t)⁻¹
      = pinnedX .E6 K a t * (pinnedX .E6 K b t * rootProd .E6 K zPsi zCoeff *
          (pinnedX .E6 K b t)⁻¹) * (pinnedX .E6 K a t)⁻¹ := by
        rw [rootProd_zPsi_zCoeff]
        group
    _ = rootProd .E6 K zPsi (conjCoeff a t zPsi (conjCoeff b t zPsi zCoeff)) := by
        rw [conj_rootProd_zPsi hb hb3.ge, conj_rootProd_zPsi ha ha3.ge]
    _ = rootProd .E6 K zPsi zCoeff := rootProd_congr key
    _ = zAS K := rootProd_zPsi_zCoeff

@[expose] def zSPairs : List ((Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)) :=
  [(![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0]), (![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]),
    (![1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1]), (![-1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0]),
    (![0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, -1]), (![-1, 0, -1, 0, 0, 0], ![0, 0, 0, 0, -1, -1])]

theorem zSPairs_check : ∀ p ∈ zSPairs,
    isRootB .E6 p.1 = true ∧ isRootB .E6 p.2 = true ∧ p.1 3 = 0 ∧ p.2 3 = 0 ∧
      zPairCheck p.1 p.2 = true ∧ isRootB .E6 (p.1 + p.2) = false ∧ p.1 ≠ -p.2 ∧
      isRootB .E6 (Pi.single 1 1 + p.1) = false ∧ isRootB .E6 (Pi.single 1 1 + p.2) = false ∧
      isRootB .E6 (-Pi.single 1 1 + p.1) = false ∧ isRootB .E6 (-Pi.single 1 1 + p.2) = false ∧
      Pi.single 1 1 ≠ -p.1 ∧ Pi.single 1 1 ≠ -p.2 ∧ -Pi.single 1 1 ≠ -p.1 ∧
      -Pi.single 1 1 ≠ -p.2 := by
  decide +kernel

variable (K) in
@[expose] noncomputable def zJ : Subgroup (ModGL .E6 K) :=
  rootSubgroup .E6 K (Pi.single 1 1) ⊔ rootSubgroup .E6 K (-Pi.single 1 1)

variable (K) in
@[expose] noncomputable def zS : Subgroup (ModGL .E6 K) :=
  closure {g | ∃ p ∈ zSPairs, ∃ t : K, g = pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t}

theorem zS_le_centralizer [CharP K 2] : zS K ≤ centralizer ({zAS K} : Set (ModGL .E6 K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨p, hp, t, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := zSPairs_check p hp
  refine mem_centralizer_singleton_iff.2 ?_
  have e := conj_pair_zAS (K := K) (isRootB_iff.1 h1) h3 (isRootB_iff.1 h2) h4 h5 t
  calc pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t * zAS K =
      pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t * zAS K *
        (pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t)⁻¹ *
          (pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t) := by group
    _ = zAS K * (pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t) := by rw [e]

theorem mem_parabolicRoots_zNodes {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot .E6 a) (ha3 : a 3 = 0) :
    a ∈ parabolicRoots .E6 zNodes :=
  ⟨ha, fun i hi => by
    have : i = 3 := by simpa [zNodes] using hi
    rw [this]
    exact ha3⟩

theorem zS_le_parabolicLevi : zS K ≤ parabolicLevi .E6 K zNodes := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨p, hp, t, rfl⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := zSPairs_check p hp
  exact mul_mem
    (F4Pilot.rootSubgroup_le_parabolicLevi (mem_parabolicRoots_zNodes (isRootB_iff.1 h1) h3)
      (mem_rootSubgroup.2 ⟨t, rfl⟩))
    (F4Pilot.rootSubgroup_le_parabolicLevi (mem_parabolicRoots_zNodes (isRootB_iff.1 h2) h4)
      (mem_rootSubgroup.2 ⟨t, rfl⟩))

theorem zS_le_levi_inf_centralizer [CharP K 2] :
    zS K ≤ parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) :=
  le_inf zS_le_parabolicLevi zS_le_centralizer

theorem zJ_le_levi_inf_centralizer :
    zJ K ≤ parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) :=
  rootPair_alpha2_le_levi_inf_centralizer

theorem zS_le_centralizer_zJ : zS K ≤ centralizer (zJ K : Set (ModGL .E6 K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨p, hp, t, rfl⟩
  obtain ⟨h1, h2, -, -, -, -, -, k1, k2, k3, k4, n1, n2, n3, n4⟩ := zSPairs_check p hp
  have hcomm : ∀ {σ : Fin Tag.E6.rank → ℤ}, (σ = Pi.single 1 1 ∨ σ = -Pi.single 1 1) →
      ∀ s : K, Commute (pinnedX .E6 K σ s) (pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t) := by
    intro σ hσ s
    have hσr : IsRoot .E6 σ := by
      rcases hσ with rfl | rfl
      · exact isRoot_single .E6 1
      · exact isRoot_neg_single .E6 1
    refine Commute.mul_right ?_ ?_
    · refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hσr (isRootB_iff.1 h1) ?_ ?_ s t
      · rcases hσ with rfl | rfl
        · exact n1
        · exact n3
      · rcases hσ with rfl | rfl
        · rw [← isRootB_iff, k1]; exact Bool.false_ne_true
        · rw [← isRootB_iff, k3]; exact Bool.false_ne_true
    · refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hσr (isRootB_iff.1 h2) ?_ ?_ s t
      · rcases hσ with rfl | rfl
        · exact n2
        · exact n4
      · rcases hσ with rfl | rfl
        · rw [← isRootB_iff, k2]; exact Bool.false_ne_true
        · rw [← isRootB_iff, k4]; exact Bool.false_ne_true
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro y hy
  have hle : zJ K ≤ centralizer ({pinnedX .E6 K p.1 t * pinnedX .E6 K p.2 t} :
      Set (ModGL .E6 K)) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨s, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hcomm (Or.inl rfl) s).eq
    · rintro _ ⟨s, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hcomm (Or.inr rfl) s).eq
  exact mem_centralizer_singleton_iff.1 (hle hy)

end CFSG.SeitzReduction.E6Pilot
