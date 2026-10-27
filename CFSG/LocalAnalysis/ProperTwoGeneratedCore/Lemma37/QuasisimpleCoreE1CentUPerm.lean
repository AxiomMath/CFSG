module

public import CFSG.Sporadic.Th.Max3.AltNine
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

private instance instDecEqPermFinFourE1 : DecidableEq (Perm (Fin 4)) := fun a b =>
  decidable_of_iff (∀ i : Fin 4, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

private instance instDecEqPermFinFiveE1 : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

@[expose] def permNine : Perm (Fin 4) × Perm (Fin 5) →* Perm (Fin 9) :=
  (finSumFinEquiv (m := 4) (n := 5)).permCongrHom.toMonoidHom.comp (sumCongrHom (Fin 4) (Fin 5))

theorem permNine_castAdd (p : Perm (Fin 4) × Perm (Fin 5)) (i : Fin 4) :
    permNine p (Fin.castAdd 5 i) = Fin.castAdd 5 (p.1 i) := by
  change finSumFinEquiv (Sum.map p.1 p.2 (finSumFinEquiv.symm (Fin.castAdd 5 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem permNine_natAdd (p : Perm (Fin 4) × Perm (Fin 5)) (i : Fin 5) :
    permNine p (Fin.natAdd 4 i) = Fin.natAdd 4 (p.2 i) := by
  change finSumFinEquiv (Sum.map p.1 p.2 (finSumFinEquiv.symm (Fin.natAdd 4 i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem permNine_injective : Function.Injective permNine := fun _ _ h =>
  sumCongrHom_injective ((finSumFinEquiv (m := 4) (n := 5)).permCongrHom.injective h)

theorem sign_permNine (p : Perm (Fin 4) × Perm (Fin 5)) :
    sign (permNine p) = sign p.1 * sign p.2 := by
  change sign ((finSumFinEquiv (m := 4) (n := 5)).permCongr (p.1.sumCongr p.2)) = _
  rw [sign_permCongr, sign_sumCongr]

theorem card_support_permNine (p : Perm (Fin 4) × Perm (Fin 5)) :
    (permNine p).support.card = p.1.support.card + p.2.support.card := by
  simp only [Perm.support, Finset.card_filter]
  rw [show (∑ i : Fin 9, if permNine p i ≠ i then 1 else 0) =
      ∑ i : Fin (4 + 5), if permNine p i ≠ i then 1 else 0 from rfl, Fin.sum_univ_add]
  simp only [permNine_castAdd, permNine_natAdd, ne_eq]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [Fin.ext_iff]

theorem cycleType_eq_replicate {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}
    (h : π * π = 1) : π.cycleType = Multiset.replicate (π.support.card / 2) 2 := by
  have h2 : ∀ n ∈ π.cycleType, n = 2 := by
    intro n hn
    have hd := dvd_of_mem_cycleType hn
    have hle := two_le_of_mem_cycleType hn
    have ho : orderOf π ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have := Nat.le_of_dvd (by norm_num) (hd.trans ho)
    omega
  have hsum := sum_cycleType π
  have hrep : π.cycleType = Multiset.replicate (Multiset.card π.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, h2⟩
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep, ← hsum]
  congr 1
  omega

@[expose] def fourRep : Perm (Fin 4) := swap 0 1 * swap 2 3

theorem altRep2_eq_permNine : altRep2 = permNine (fourRep, 1) := by
  ext i
  fin_cases i <;> rfl

@[expose] def altRep2A : alternatingGroup (Fin 9) :=
  ⟨altRep2, mem_alternatingGroup.mpr sign_altRep2⟩

theorem card_centralizer_altRep2_perm :
    Nat.card (Subgroup.centralizer ({altRep2} : Set (Perm (Fin 9)))) = 960 := by
  rw [nat_card_centralizer, cycleType_altRep2]
  decide

theorem card_centralizer_altRep2 :
    Nat.card (Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9)))) = 480 := by
  set C := Subgroup.centralizer ({altRep2} : Set (Perm (Fin 9))) with hC
  let f : C →* ℤˣ := sign.comp C.subtype
  have hsurj : Function.Surjective f := by
    intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap 0 1, Subgroup.mem_centralizer_singleton_iff.mpr swap_mul_altRep2⟩,
        sign_swap (show (0 : Fin 9) ≠ 1 by decide)⟩
  have hker : Nat.card f.ker * 2 = 960 := by
    rw [← card_centralizer_altRep2_perm, ← Subgroup.card_mul_index f.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int]
  have heq : Nat.card (Subgroup.centralizer ({altRep2A} : Set (alternatingGroup (Fin 9)))) =
      Nat.card f.ker := Nat.card_congr
    { toFun := fun a => ⟨⟨(a : alternatingGroup (Fin 9)), Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp a.2))⟩,
        mem_alternatingGroup.mp (a : alternatingGroup (Fin 9)).2⟩
      invFun := fun c => ⟨⟨((c : C) : Perm (Fin 9)), mem_alternatingGroup.mpr c.2⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.mp (c : C).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  omega

theorem perm4_card_support_of_fpf : ∀ σ : Perm (Fin 4), σ * σ = 1 → (∀ i, σ i ≠ i) →
    σ.support.card = 4 := by
  decide +kernel

theorem perm4_card_support_of_odd : ∀ σ : Perm (Fin 4), σ * σ = 1 → sign σ = -1 →
    σ.support.card = 2 := by
  decide +kernel

theorem perm4_pow_four_of_commute : ∀ σ : Perm (Fin 4), σ * fourRep = fourRep * σ →
    σ ^ 4 = 1 := by
  decide +kernel

theorem perm5_card_support_of_even : ∀ τ : Perm (Fin 5), sign τ = 1 → τ * τ = 1 → τ ≠ 1 →
    τ.support.card = 4 := by
  decide +kernel

theorem perm5_card_support_of_odd : ∀ τ : Perm (Fin 5), sign τ = -1 → τ * τ = 1 →
    τ.support.card = 2 := by
  decide +kernel

theorem perm5_four_group : ∀ a b : Perm (Fin 5), (sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    (sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ i₀ : Fin 5, ∀ π : Perm (Fin 5), π i₀ = i₀ →
      ∀ σ ∈ [1, a, b, a * b], π * σ * π⁻¹ ∈ [1, a, b, a * b] := by
  decide +kernel

theorem eq_bot_of_normal_of_odd {N : Subgroup (Perm (Fin 5))} [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hsign : ∀ n ∈ N, sign n = 1 := fun n hn => by
    have hodd : Odd (orderOf n) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
    rcases Int.units_eq_one_or (sign n) with h | h
    · exact h
    · have h1 : sign n ^ orderOf n = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h, hodd.neg_one_pow] at h1
      exact absurd h1 (by decide)
  have hle : N ≤ alternatingGroup (Fin 5) := fun n hn => mem_alternatingGroup.mpr (hsign n hn)
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp)
      (N := N.subgroupOf (alternatingGroup (Fin 5))) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have h1 : (⟨n, hle hn⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
      Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · exfalso
    have hA : alternatingGroup (Fin 5) ≤ N := fun a ha => by
      have h1 : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
        h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    have hdvd := Subgroup.card_dvd_of_le hA
    rw [show Nat.card (alternatingGroup (Fin 5)) = 60 by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl] at hdvd
    obtain ⟨k, hk⟩ := hN
    omega

theorem eq_top_of_stabilizer_le {α : Type*} [DecidableEq α] {M : Subgroup (Perm α)} {j : α}
    (hM : ∀ π : Perm α, π j = j → π ∈ M) {π₀ : Perm α} (h0 : π₀ ∈ M) (hj : π₀ j ≠ j) :
    M = ⊤ := by
  rw [eq_top_iff]
  intro τ _
  by_cases hτ : τ j = j
  · exact hM τ hτ
  set σ := swap (π₀ j) (τ j) with hσ
  have hσj : σ j = j := swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hτ)
  have hσM : σ ∈ M := hM σ hσj
  have hrest : (σ * π₀)⁻¹ * τ ∈ M := hM _ (by
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq, Perm.mul_apply, hσ, swap_apply_left])
  rw [show τ = σ * π₀ * ((σ * π₀)⁻¹ * τ) by group]
  exact M.mul_mem (M.mul_mem hσM h0) hrest

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
