module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG.LocalAnalysis.ComponentInitial

variable {Q : Type} [Group Q]

theorem ker_eq_bot_of_lift_mul_self [Finite Q] [Group.IsPerfect Q] {m : ℕ} (hm : 3 ≤ m)
    (η : Q →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center Q) (hK2 : IsPGroup 2 η.ker) {d : Q}
    (hd : η d = altThreeCycle (⟨0, by omega⟩ : Fin m) * altThreeCycle (⟨1, by omega⟩ : Fin m))
    (hd2 : d * d = 1) : η.ker = ⊥ := by
  classical
  have hlift : ∀ i : Fin m, ∃ x : Q, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hκ : (x i₀ * x i₁)⁻¹ * d ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hxη, hxη, hd, inv_mul_cancel]
  set κ : η.ker := ⟨(x i₀ * x i₁)⁻¹ * d, hκ⟩ with hκdef
  have hκ2 : κ ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (G := η.ker) (x := κ)
    have hle := card_ker_le_two_of_alternating hm η hη hK hK2
    have hpos : 0 < Nat.card η.ker := Nat.card_pos
    interval_cases h : Nat.card η.ker
    · rw [pow_one] at hpow
      rw [hpow, one_pow]
    · exact hpow
  have hκc : ∀ g : Q, g * ((κ : η.ker) : Q) = ((κ : η.ker) : Q) * g := fun g =>
    (Subgroup.mem_center_iff.mp (hK κ.2) g)
  have hde : d = x i₀ * x i₁ * (κ : Q) := by
    rw [hκdef]
    show d = x i₀ * x i₁ * ((x i₀ * x i₁)⁻¹ * d)
    group
  have hz : (x i₀ * x i₁) ^ 2 = 1 := by
    have hκ2' : (κ : Q) * (κ : Q) = 1 := by
      have := congrArg Subtype.val hκ2
      simpa [sq] using this
    have h1 : d * d = (x i₀ * x i₁) ^ 2 * ((κ : Q) * (κ : Q)) := by
      rw [hde, sq]
      calc x i₀ * x i₁ * (κ : Q) * (x i₀ * x i₁ * (κ : Q))
          = x i₀ * x i₁ * ((κ : Q) * (x i₀ * x i₁)) * (κ : Q) := by group
        _ = x i₀ * x i₁ * ((x i₀ * x i₁) * (κ : Q)) * (κ : Q) := by rw [hκc (x i₀ * x i₁)]
        _ = x i₀ * x i₁ * (x i₀ * x i₁) * ((κ : Q) * (κ : Q)) := by group
    rw [hd2, hκ2', mul_one] at h1
    exact h1.symm
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij => by
    rw [lift_sq_eq η hη hK hK2 hxη hx3 hij h01, hz]
  have hcardQ : Nat.card Q ≤ (m + 2).factorial / 2 := by
    have h := card_closure_le_of_carmichael m x hx3 hzij
    rw [hL, Subgroup.card_top] at h
    exact h
  have hQ : Nat.card Q = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hK1 : Nat.card η.ker ≤ 1 := by
    have : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * 1 := by
      rw [mul_one, ← hA, ← hQ, hA]
      exact hcardQ
    exact Nat.le_of_mul_le_mul_left this hApos
  exact Subgroup.eq_bot_of_card_le _ hK1

end CFSG.ClassicalInvolution.Q3.TL4.AECov
