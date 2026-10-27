module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem exists_mem_alternatingGroup_conj {α : Type*} [DecidableEq α] [Fintype α]
    {f g : Fin 4 → α} (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ ρ ∈ alternatingGroup α, ρ * (swap (g 0) (g 1) * swap (g 2) (g 3)) * ρ⁻¹ =
      swap (f 0) (f 1) * swap (f 2) (f 3) := by
  obtain ⟨ρ, hρ⟩ := Perm.exists_extending_pair g f hg hf
  have hconj : ∀ ρ' : Perm α, ρ' * (swap (g 0) (g 1) * swap (g 2) (g 3)) * ρ'⁻¹ =
      swap (ρ' (g 0)) (ρ' (g 1)) * swap (ρ' (g 2)) (ρ' (g 3)) := fun ρ' => by
    rw [swap_apply_apply, swap_apply_apply]
    group
  have h01 : g 0 ≠ g 1 := hg.ne (by decide)
  rcases Int.units_eq_one_or (sign ρ) with hs | hs
  · exact ⟨ρ, mem_alternatingGroup.mpr hs, by simp only [hconj, hρ]⟩
  · refine ⟨ρ * swap (g 0) (g 1), ?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, hs, Perm.sign_swap h01]
      decide
    · have h20 : g 2 ≠ g 0 := hg.ne (by decide)
      have h21 : g 2 ≠ g 1 := hg.ne (by decide)
      have h30 : g 3 ≠ g 0 := hg.ne (by decide)
      have h31 : g 3 ≠ g 1 := hg.ne (by decide)
      rw [hconj]
      simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
        swap_apply_of_ne_of_ne h20 h21, swap_apply_of_ne_of_ne h30 h31, hρ]
      rw [swap_comm]

variable {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]

theorem sq_lift_ne_one {m : ℕ} (hm : 3 ≤ m) (η : P →* alternatingGroup (Fin (m + 2)))
    (hη : Function.Surjective η) (hK : η.ker ≤ center P) (hK2 : IsPGroup 2 η.ker)
    (hne : η.ker ≠ ⊥) {y : Fin m → P} (hyη : ∀ i, η (y i) = altThreeCycle i)
    (hy3 : ∀ i, y i ^ 3 = 1) :
    (y ⟨0, by omega⟩ * y ⟨1, by omega⟩) ^ 2 ≠ 1 := by
  intro hz1
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hL : closure (Set.range y) = ⊤ := by
    have hmap : (closure (Set.range y)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ y = altThreeCycle := funext hyη
      rw [this, closure_altThreeCycle]
    have hsup : closure (Set.range y) ⊔ η.ker = ⊤ := by
      rw [← comap_map_eq, hmap, comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (closure (Set.range y)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (commutator_le_self _))
  have hcard := card_closure_le_of_carmichael m y hy3
    (fun i j hij => by rw [lift_sq_eq η hη hK hK2 hyη hy3 hij h01, hz1])
  rw [hL, card_top] at hcard
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hle : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * 1 := by
    calc (m + 2).factorial / 2 * Nat.card η.ker = Nat.card P := by rw [hP2, hA]
      _ ≤ (m + 2).factorial / 2 := hcard
      _ = (m + 2).factorial / 2 * 1 := (mul_one _).symm
  have hk1 : Nat.card η.ker ≤ 1 := Nat.le_of_mul_le_mul_left hle hApos
  exact hne (eq_bot_of_card_eq _ (le_antisymm hk1 Nat.card_pos))

theorem sq_ne_one_of_map_eq_swap_mul_swap {n : ℕ} (hn : 5 ≤ n)
    (η : P →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (hK2 : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥)
    {f : Fin 4 → Fin n} (hf : Function.Injective f) {x : P}
    (hx : ((η x : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap (f 0) (f 1) * swap (f 2) (f 3)) :
    x ^ 2 ≠ 1 := by
  have hk2 := alternating_perfect_central_two_kernel_order_at_most_two hn η hη hK hK2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hlift : ∀ i : Fin m, ∃ y : P, η y = altThreeCycle i ∧ y ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨y', hy', hy3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨y', hy'.trans hy, hy3⟩
  choose y hyη hy3 using hlift
  have hz1 := sq_lift_ne_one (by omega) η hη hK hK2 hne hyη hy3
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let g : Fin 4 → Fin (m + 2) := fun i => Fin.castLE (by omega) (swap (1 : Fin 4) 2 i)
  have hg : Function.Injective g := (Fin.castLE_injective _).comp (swap (1 : Fin 4) 2).injective
  have hg0 : g 0 = 0 := Fin.ext (by simp [g, show swap (1 : Fin 4) 2 0 = 0 by decide])
  have hg1 : g 1 = (⟨0, by omega⟩ : Fin m).addNat 2 :=
    Fin.ext (by simp [g, show swap (1 : Fin 4) 2 1 = 2 by decide])
  have hg2 : g 2 = 1 := Fin.ext (by simp [g, show swap (1 : Fin 4) 2 2 = 1 by decide])
  have hg3 : g 3 = (⟨1, by omega⟩ : Fin m).addNat 2 :=
    Fin.ext (by simp [g, show swap (1 : Fin 4) 2 3 = 3 by decide])
  have hwη : ((η (y ⟨0, by omega⟩ * y ⟨1, by omega⟩) : alternatingGroup (Fin (m + 2))) :
      Perm (Fin (m + 2))) = swap (g 0) (g 1) * swap (g 2) (g 3) := by
    rw [map_mul, hyη, hyη, coe_altThreeCycle_mul h01, hg0, hg1, hg2, hg3]
  obtain ⟨ρ, hρA, hρ⟩ := exists_mem_alternatingGroup_conj hf hg
  obtain ⟨r, hr⟩ := hη ⟨ρ, hρA⟩
  set w := y ⟨0, by omega⟩ * y ⟨1, by omega⟩ with hw
  set c := (r * w * r⁻¹)⁻¹ * x with hc
  have hcker : c ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [hc, map_mul, map_inv, hr, Subgroup.coe_mul, Subgroup.coe_inv, hwη, hx,
      OneMemClass.coe_one]
    rw [hρ, inv_mul_cancel]
  have hcZ : c ∈ center P := hK hcker
  have hc2 : c ^ 2 = 1 := by
    have hd : Nat.card η.ker ∣ 2 := by
      have hpos : 0 < Nat.card η.ker := Nat.card_pos
      rcases (by omega : Nat.card η.ker = 1 ∨ Nat.card η.ker = 2) with h | h
      · rw [h]
        exact one_dvd 2
      · rw [h]
    have h1 := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard (⟨c, hcker⟩ : η.ker)).trans hd)
    simpa using congrArg Subtype.val h1
  have hxc : x = r * w * r⁻¹ * c := by rw [hc]; group
  have hcomm : Commute (r * w * r⁻¹) c := mem_center_iff.mp hcZ _
  rw [hxc, hcomm.mul_pow, hc2, mul_one, conj_pow]
  intro h1
  apply hz1
  calc w ^ 2 = r⁻¹ * (r * w ^ 2 * r⁻¹) * r := by group
    _ = 1 := by rw [h1]; group

end CFSG.ComponentClassification.HarrisLit.N36
