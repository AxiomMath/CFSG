module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup Equiv Equiv.Perm

theorem eq_one_of_perfect {X β : Type*} [Group X] [Finite β] (hX : Group.IsPerfect X)
    (hβ : Nat.card β ≤ 4) (ρ : X →* Perm β) (x : X) : ρ x = 1 := by
  have hsolv : Group.IsSolvable (Perm β) := Equiv.Perm.isSolvable hβ
  have hrp : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  have hrs : Group.IsSolvable ↥ρ.range := subgroup_solvable_of_solvable _
  have hsub : Subsingleton ↥ρ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ hrs
  have h1 : (⟨ρ x, x, rfl⟩ : ↥ρ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

variable {m : ℕ}

theorem fixes_of_perfect {X : Subgroup (Perm (Fin m))} (hX : ⁅X, X⁆ = X) (S : Finset (Fin m))
    (hS : ∀ x ∈ X, ∀ a ∈ S, x a ∈ S) (hcard : S.card ≤ 4) :
    ∀ x ∈ X, ∀ a ∈ S, x a = a := by
  classical
  have hiff : ∀ x ∈ X, ∀ a, x a ∈ S ↔ a ∈ S := by
    intro x hx a
    refine ⟨fun h => ?_, hS x hx a⟩
    have := hS x⁻¹ (inv_mem hx) (x a) h
    rwa [Perm.inv_eq_iff_eq.mpr rfl] at this
  let r : ↥X →* Perm {a : Fin m // a ∈ S} :=
    { toFun := fun x => (x : Perm (Fin m)).subtypePerm (hiff x x.2)
      map_one' := by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  intro x hx a ha
  have h1 := eq_one_of_perfect hperf
    (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hcard) r ⟨x, hx⟩
  have h2 := congrArg (fun f : Perm {a : Fin m // a ∈ S} => (f ⟨a, ha⟩ : Fin m)) h1
  simpa [r] using h2

theorem finsetCongr_inv_apply (x : Perm (Fin m)) (T : Finset (Fin m)) :
    Equiv.finsetCongr (x⁻¹ : Perm (Fin m)) (Equiv.finsetCongr x T) = T := by
  ext b
  simp [Equiv.finsetCongr_apply, Perm.inv_def]

theorem mem_pair_of_perfect {π : Perm (Fin m)} {X : Subgroup (Perm (Fin m))} (hX : ⁅X, X⁆ = X)
    (hXπ : ∀ x ∈ X, x * π = π * x) (hπ2 : π * π = 1) (hcard : π.support.card ≤ 8) :
    ∀ x ∈ X, ∀ a ∈ π.support, x a = a ∨ x a = π a := by
  classical
  have hππ : ∀ a, π (π a) = a := fun a => by rw [← Perm.mul_apply, hπ2, Perm.one_apply]
  have hxπ : ∀ x ∈ X, ∀ a, x (π a) = π (x a) := fun x hx a => by
    rw [← Perm.mul_apply, hXπ x hx, Perm.mul_apply]
  set O : Finset (Finset (Fin m)) :=
    π.support.image (fun a => ({a, π a} : Finset (Fin m))) with hO
  have hOcard : O.card ≤ 4 := by
    have h1 := Finset.card_eq_sum_card_image (fun a => ({a, π a} : Finset (Fin m))) π.support
    have h2 : O.card • 2 ≤ ∑ T ∈ O,
        (π.support.filter (fun a => ({a, π a} : Finset (Fin m)) = T)).card := by
      apply Finset.card_nsmul_le_sum
      intro T hT
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
      have hne : a ≠ π a := fun h => (mem_support.mp ha) h.symm
      apply Finset.one_lt_card.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩, π a, Finset.mem_filter.mpr
        ⟨apply_mem_support.mpr ha, ?_⟩, hne⟩
      rw [hππ, Finset.pair_comm]
    rw [smul_eq_mul] at h2
    rw [← hO] at h1
    omega
  have hmapO : ∀ x ∈ X, ∀ T ∈ O, Equiv.finsetCongr x T ∈ O := by
    intro x hx T hT
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hT
    refine Finset.mem_image.mpr ⟨x a, (AltCent.mem_support_iff_of_comm (hXπ x hx) a).mpr ha, ?_⟩
    rw [Equiv.finsetCongr_apply, Finset.map_insert, Finset.map_singleton]
    simp [hxπ x hx]
  have hiffO : ∀ x ∈ X, ∀ T, Equiv.finsetCongr x T ∈ O ↔ T ∈ O := by
    intro x hx T
    refine ⟨fun h => ?_, hmapO x hx T⟩
    have := hmapO x⁻¹ (inv_mem hx) _ h
    rwa [finsetCongr_inv_apply] at this
  let r : ↥X →* Perm {T : Finset (Fin m) // T ∈ O} :=
    { toFun := fun x => Equiv.Perm.subtypePerm (Equiv.finsetCongr (x : Perm (Fin m)))
        (hiffO x x.2)
      map_one' := by
        apply Equiv.ext
        rintro ⟨T, hT⟩
        apply Subtype.ext
        show T.map (Equiv.toEmbedding (1 : Perm (Fin m))) = T
        ext b
        simp only [Finset.mem_map_equiv]
        exact Iff.rfl
      map_mul' := fun x y => by
        apply Equiv.ext
        rintro ⟨T, hT⟩
        apply Subtype.ext
        show T.map (Equiv.toEmbedding ((x : Perm (Fin m)) * (y : Perm (Fin m)))) =
          (T.map (y : Perm (Fin m)).toEmbedding).map (x : Perm (Fin m)).toEmbedding
        rw [Finset.map_map]
        rfl }
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  intro x hx a ha
  have hT : ({a, π a} : Finset (Fin m)) ∈ O := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have h1 := eq_one_of_perfect hperf
    (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hOcard) r ⟨x, hx⟩
  have h2 := congrArg (fun f : Perm {T : Finset (Fin m) // T ∈ O} => (f ⟨_, hT⟩ :
    Finset (Fin m))) h1
  have h3 : x a ∈ Equiv.finsetCongr x ({a, π a} : Finset (Fin m)) := by
    rw [Equiv.finsetCongr_apply]
    exact Finset.mem_map_of_mem _ (Finset.mem_insert_self _ _)
  have h4 : Equiv.finsetCongr x ({a, π a} : Finset (Fin m)) = {a, π a} := by
    simpa [r] using h2
  rw [h4] at h3
  simpa using h3

theorem eq_bot_of_perfect_of_card_support {π : Perm (Fin m)} {X : Subgroup (Perm (Fin m))}
    (hX : ⁅X, X⁆ = X) (hXπ : ∀ x ∈ X, x * π = π * x) (hπ2 : π * π = 1)
    (hcard : π.support.card ≤ 8) (hm : m ≤ π.support.card + 4) : X = ⊥ := by
  classical
  have hππ : ∀ a, π (π a) = a := fun a => by rw [← Perm.mul_apply, hπ2, Perm.one_apply]
  have hxπ : ∀ x ∈ X, ∀ a, x (π a) = π (x a) := fun x hx a => by
    rw [← Perm.mul_apply, hXπ x hx, Perm.mul_apply]
  have hpair := mem_pair_of_perfect hX hXπ hπ2 hcard
  have hfix : ∀ x ∈ X, ∀ a, x a = a := by
    intro x hx a
    by_cases ha : a ∈ π.support
    · refine fixes_of_perfect hX {a, π a} (fun y hy b hb => ?_) (Finset.card_le_two.trans
        (by norm_num)) x hx a (Finset.mem_insert_self _ _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
      rcases hb with rfl | rfl
      · exact hpair y hy b ha
      · rw [hxπ y hy]
        rcases hpair y hy a ha with h | h
        · rw [h]
          exact Or.inr rfl
        · rw [h, hππ]
          exact Or.inl rfl
    · refine fixes_of_perfect hX π.supportᶜ (fun y hy b hb => ?_) ?_ x hx a
        (Finset.mem_compl.mpr ha)
      · rw [Finset.mem_compl] at hb ⊢
        exact fun h => hb ((AltCent.mem_support_iff_of_comm (hXπ y hy) b).mp h)
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  exact Equiv.ext fun a => hfix x hx a

theorem two_dvd_card_of_perfect {X : Type*} [Group X] [Finite X] [Nontrivial X]
    (hX : Group.IsPerfect X) : 2 ∣ Nat.card X := by
  by_contra h
  have hodd : Odd (Nat.card X) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  exact Group.IsPerfect.not_isSolvable X (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
