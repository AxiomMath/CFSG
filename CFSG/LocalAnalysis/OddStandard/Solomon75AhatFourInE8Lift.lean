module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataLift
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section PeelPerm

variable {n : ℕ}

theorem exists_peel_perm {σ : Perm (Fin n)} (hσ : sign σ = 1) (h2 : ∀ y, σ (σ y) = y)
    (h1 : σ ≠ 1) :
    ∃ δ : Perm (Fin n), sign δ = 1 ∧ δ.cycleType = {2, 2} ∧
      (∀ y, (δ⁻¹ * σ) ((δ⁻¹ * σ) y) = y) ∧ (δ⁻¹ * σ).support.card + 4 = σ.support.card ∧
      (∀ y, δ y ≠ y → σ y ≠ y) ∧ (∀ y, (δ⁻¹ * σ) y ≠ y → σ y = (δ⁻¹ * σ) y) ∧
      (∀ y, δ y ≠ y → (δ⁻¹ * σ) y = y) := by
  classical
  have hσ2 : σ * σ = 1 := by
    ext y
    simp [Perm.mul_apply, h2]
  obtain ⟨a₁, b₁, a₂, b₂, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (Perm.mem_alternatingGroup.2 hσ) hσ2 h1
  set δ : Perm (Fin n) := swap a₁ b₁ * swap a₂ b₂ with hδ
  have hnd : [a₁, b₁, a₂, b₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      List.nodup_nil, and_true, not_false_eq_true]
    grind
  have hδcyc : δ.cycleType = {2, 2} := cycleType_swap_mul_swap_of_nodup hnd
  have hδsign : sign δ = 1 := by
    rw [hδ, map_mul, sign_swap h1b1, sign_swap h2b2]
    decide
  have hδP : ∀ y, (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) → δ y = σ y := by
    intro y hy
    simp only [hδ, Perm.mul_apply, swap_apply_def]
    split_ifs <;> grind
  have hδ0 : ∀ y, ¬ (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) → δ y = y := by
    intro y hy
    simp only [hδ, Perm.mul_apply, swap_apply_def]
    split_ifs <;> grind
  have hδδ : ∀ y, δ (δ y) = y := by
    intro y
    by_cases hy : (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂)
    · have hσy : (σ y = a₁ ∨ σ y = b₁ ∨ σ y = a₂ ∨ σ y = b₂) := by
        rcases hy with rfl | rfl | rfl | rfl <;> grind
      rw [hδP y hy, hδP _ hσy, h2]
    · rw [hδ0 y hy, hδ0 y hy]
  have hδinv : ∀ y, δ⁻¹ y = δ y := fun y => by
    rw [Perm.inv_eq_iff_eq]
    exact (hδδ y).symm
  have hPσ : ∀ y, (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) ↔
      (σ y = a₁ ∨ σ y = b₁ ∨ σ y = a₂ ∨ σ y = b₂) := by
    intro y
    constructor
    · intro hy
      rcases hy with rfl | rfl | rfl | rfl <;> grind
    · intro hy
      have h3 : σ (σ y) = y := h2 y
      rcases hy with h | h | h | h <;> rw [h] at h3 <;> grind
  have hσ₂P : ∀ y, (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) → (δ⁻¹ * σ) y = y := by
    intro y hy
    rw [Perm.mul_apply, hδinv, hδP _ ((hPσ y).1 hy), h2]
  have hσ₂0 : ∀ y, ¬ (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) → (δ⁻¹ * σ) y = σ y := by
    intro y hy
    rw [Perm.mul_apply, hδinv, hδ0 _ (fun h => hy ((hPσ y).2 h))]
  have hσne : ∀ y, (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) → σ y ≠ y := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl <;> grind
  refine ⟨δ, hδsign, hδcyc, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂)
    · rw [hσ₂P y hy, hσ₂P y hy]
    · have hy' : ¬ (σ y = a₁ ∨ σ y = b₁ ∨ σ y = a₂ ∨ σ y = b₂) := fun h => hy ((hPσ y).2 h)
      rw [hσ₂0 y hy, hσ₂0 (σ y) hy', h2]
  · have hF : ({a₁, b₁, a₂, b₂} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;>
        (try simp only [Finset.mem_insert, Finset.mem_singleton]) <;> grind
    have hsub : ({a₁, b₁, a₂, b₂} : Finset (Fin n)) ⊆ σ.support := by
      intro y hy
      rw [Perm.mem_support]
      apply hσne
      simpa using hy
    have hsupp : (δ⁻¹ * σ).support = σ.support \ {a₁, b₁, a₂, b₂} := by
      ext y
      rw [Perm.mem_support, Finset.mem_sdiff, Perm.mem_support]
      by_cases hy : (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂)
      · have hy' : y ∈ ({a₁, b₁, a₂, b₂} : Finset (Fin n)) := by simpa using hy
        rw [hσ₂P y hy]
        simp [hy']
      · have hy' : y ∉ ({a₁, b₁, a₂, b₂} : Finset (Fin n)) := by simpa using hy
        rw [hσ₂0 y hy]
        simp [hy']
    rw [hsupp, Finset.card_sdiff_of_subset hsub, hF]
    have := Finset.card_le_card hsub
    omega
  · intro y hy
    by_contra hy'
    exact hy (hδ0 y (fun h => hσne y h hy'))
  · intro y hy
    have : ¬ (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂) := fun h => hy (hσ₂P y h)
    exact (hσ₂0 y this).symm
  · intro y hy
    by_cases hP : (y = a₁ ∨ y = b₁ ∨ y = a₂ ∨ y = b₂)
    · exact hσ₂P y hP
    · exact absurd (hδ0 y hP) hy

end PeelPerm

namespace CoverSetup

variable {n : ℕ} {K : Type} [Group K]

theorem toTwoCover (C : CoverSetup n K) : CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover C.π :=
  ⟨C.surj, C.ker.le, by rw [C.ker]; exact C.center_card, C.hX.1.1⟩

theorem exists_central_generator (C : CoverSetup n K) :
    ∃ z : K, z ∈ center K ∧ z ≠ 1 ∧ ∀ u ∈ center K, u = 1 ∨ u = z := by
  obtain ⟨⟨z, hz⟩, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : center K)).mp C.center_card
  refine ⟨z, hz, fun h => hz1 (Subtype.ext h), fun u hu => ?_⟩
  by_cases h1 : u = 1
  · exact Or.inl h1
  · right
    have := huniq ⟨u, hu⟩ (fun h => h1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem sq_mem_center_ne_one_of_cycleType_two_two (C : CoverSetup n K) (hn : 5 ≤ n) {x : K}
    (hx : (C.ρ x).cycleType = {2, 2}) : x * x ∈ center K ∧ x * x ≠ 1 := by
  obtain ⟨h1, h2⟩ := C.toTwoCover.sq_mem_ker_ne_one_of_cycleType_two_two hn hx
  rw [C.ker, pow_two] at h1
  rw [pow_two] at h2
  exact ⟨h1, h2⟩

theorem commute_of_cycleType_two_two_of_disjoint (C : CoverSetup n K) (hn : 8 ≤ n) {u v : K}
    (hu : (C.ρ u).cycleType = {2, 2}) (hv : (C.ρ v).cycleType = {2, 2})
    (hd : (C.ρ u).Disjoint (C.ρ v)) : u * v = v * u := by
  have hu2 := C.sq_mem_center_ne_one_of_cycleType_two_two (by omega) hu
  have hv2 := C.sq_mem_center_ne_one_of_cycleType_two_two (by omega) hv
  obtain ⟨z, hz, hz1, hzu⟩ := C.exists_central_generator
  have huz : u * u = z := (hzu _ hu2.1).resolve_left hu2.2
  have hvz : v * v = z := (hzu _ hv2.1).resolve_left hv2.2
  have hcomm : C.ρ u * C.ρ v = C.ρ v * C.ρ u := hd.commute.eq
  have hc : u * v * u⁻¹ * v⁻¹ ∈ center K := by
    rw [← C.ρ_eq_one_iff]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hsq := CoverSetup.sq_mul_of_comm_central hc
  have h1 : (u * v) * (u * v) = 1 := by
    have := C.toTwoCover.sq_eq_one_of_cycleType_two_two_two_two hn (x := u * v) (by
      show (C.ρ (u * v)).cycleType = {2, 2, 2, 2}
      rw [map_mul, hd.cycleType_mul, hu, hv]
      rfl)
    simpa [pow_two] using this
  rw [h1, huz, hvz, C.sq_of_mem_center hz, mul_one] at hsq
  have h3 : (u * v * u⁻¹ * v⁻¹)⁻¹ = 1 := hsq.symm
  have h4 : u * v * u⁻¹ * v⁻¹ = 1 := inv_eq_one.1 h3
  calc u * v = (u * v * u⁻¹ * v⁻¹) * v * u := by group
    _ = v * u := by rw [h4, one_mul]

theorem exists_peel (C : CoverSetup n K) {x : K} (h2 : ∀ y, C.ρ x (C.ρ x y) = y)
    (h1 : C.ρ x ≠ 1) :
    ∃ d x₂ : K, x = d * x₂ ∧ (C.ρ d).cycleType = {2, 2} ∧ (∀ y, C.ρ x₂ (C.ρ x₂ y) = y) ∧
      (C.ρ x₂).support.card + 4 = (C.ρ x).support.card ∧
      (∀ y, C.ρ d y ≠ y → C.ρ x y ≠ y) ∧ (∀ y, C.ρ x₂ y ≠ y → C.ρ x y = C.ρ x₂ y) ∧
      (∀ y, C.ρ d y ≠ y → C.ρ x₂ y = y) := by
  obtain ⟨δ, hδs, hδc, h2', hcard, h3, h4, h5⟩ := exists_peel_perm (C.sign_ρ x) h2 h1
  obtain ⟨d, hd⟩ := C.exists_ρ_eq hδs
  have hx₂ : C.ρ (d⁻¹ * x) = δ⁻¹ * C.ρ x := by rw [map_mul, map_inv, hd]
  refine ⟨d, d⁻¹ * x, by group, by rw [hd]; exact hδc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx₂]
    exact h2'
  · rw [hx₂]
    exact hcard
  · rw [hd]
    exact h3
  · rw [hx₂]
    exact h4
  · rw [hx₂, hd]
    exact h5

theorem commute_of_cycleType_two_two_of_fixed (C : CoverSetup n K) (hn : 8 ≤ n) {u : K}
    (hu : (C.ρ u).cycleType = {2, 2}) :
    ∀ N : ℕ, ∀ x : K, (C.ρ x).support.card = N → (∀ y, C.ρ x (C.ρ x y) = y) →
      (∀ y, C.ρ u y ≠ y → C.ρ x y = y) → u * x = x * u := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hN h2 hfix
    by_cases h1 : C.ρ x = 1
    · exact mem_center_iff.1 ((C.ρ_eq_one_iff).1 h1) u
    · obtain ⟨d, x₂, hx, hd, h2', hcard, hsupp, hagree, -⟩ := C.exists_peel h2 h1
      have hux₂ : u * x₂ = x₂ * u := by
        refine ih _ (by omega) x₂ rfl h2' (fun y hy => ?_)
        by_contra hne
        have h3 := hagree y hne
        have h4 := hfix y hy
        exact hne (by rw [← h3, h4])
      have hdisj : (C.ρ u).Disjoint (C.ρ d) := fun y => by
        by_cases hy : C.ρ u y = y
        · exact Or.inl hy
        · right
          by_contra hdy
          exact hsupp y hdy (hfix y hy)
      have hud : u * d = d * u := C.commute_of_cycleType_two_two_of_disjoint hn hu hd hdisj
      rw [hx]
      calc u * (d * x₂) = (u * d) * x₂ := by group
        _ = (d * u) * x₂ := by rw [hud]
        _ = d * (u * x₂) := by group
        _ = d * (x₂ * u) := by rw [hux₂]
        _ = d * x₂ * u := by group

theorem sq_lift (C : CoverSetup n K) (hn : 8 ≤ n) :
    ∀ N : ℕ, ∀ x : K, (C.ρ x).support.card = N → (∀ y, C.ρ x (C.ρ x y) = y) →
      4 ∣ N ∧ (x * x = 1 ↔ 8 ∣ N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x hN h2
    by_cases h1 : C.ρ x = 1
    · have hN0 : N = 0 := by rw [← hN, h1]; simp
      have hxc : x ∈ center K := (C.ρ_eq_one_iff).1 h1
      subst hN0
      exact ⟨dvd_zero 4, ⟨fun _ => dvd_zero 8, fun _ => C.sq_of_mem_center hxc⟩⟩
    · obtain ⟨d, x₂, hx, hd, h2', hcard, -, -, hfixd⟩ := C.exists_peel h2 h1
      obtain ⟨h4, hiff⟩ := ih _ (by omega) x₂ rfl h2'
      have hcomm : d * x₂ = x₂ * d :=
        C.commute_of_cycleType_two_two_of_fixed hn hd _ x₂ rfl h2' hfixd
      obtain ⟨z, hz, hz1, hzu⟩ := C.exists_central_generator
      have hdd := C.sq_mem_center_ne_one_of_cycleType_two_two (by omega) hd
      have hdz : d * d = z := (hzu _ hdd.1).resolve_left hdd.2
      have hx₂c : x₂ * x₂ ∈ center K := by
        apply C.sq_mem_center
        ext y
        simp [Perm.mul_apply, h2']
      have hxsq : x * x = z * (x₂ * x₂) := by
        rw [hx]
        calc d * x₂ * (d * x₂) = d * (x₂ * d) * x₂ := by group
          _ = d * (d * x₂) * x₂ := by rw [hcomm]
          _ = (d * d) * (x₂ * x₂) := by group
          _ = z * (x₂ * x₂) := by rw [hdz]
      have hzz : z * z = 1 := C.sq_of_mem_center hz
      refine ⟨by omega, ?_⟩
      rcases hzu _ hx₂c with hw | hw
      · have h8 : 8 ∣ (C.ρ x₂).support.card := hiff.1 hw
        rw [hxsq, hw, mul_one]
        constructor
        · intro h
          exact absurd h hz1
        · intro h
          omega
      · have h8 : ¬ 8 ∣ (C.ρ x₂).support.card := fun h => by
          have := hiff.2 h
          rw [hw] at this
          exact hz1 this
        rw [hxsq, hw, hzz]
        constructor
        · intro _
          omega
        · intro _
          rfl

theorem sq_eq_one_iff (C : CoverSetup n K) (hn : 8 ≤ n) {x : K}
    (h2 : ∀ y, C.ρ x (C.ρ x y) = y) : x * x = 1 ↔ 8 ∣ (C.ρ x).support.card :=
  (C.sq_lift hn _ x rfl h2).2

end CoverSetup

end CFSG.OddStandard.Solomon75.AhatData
