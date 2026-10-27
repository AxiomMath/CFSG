module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesWitness
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.Janko

open Equiv Subgroup

theorem cycleType_eq_replicate_iff_of_pow_three_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (h : σ ^ 3 = 1) (k : ℕ) :
    σ.cycleType = Multiset.replicate k 3 ↔ σ.support.card = 3 * k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · intro hk
    rw [← Perm.sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  · intro hk
    have h1 := Perm.cycleType_of_pow_prime_eq_one h
    have h2 := Perm.sum_cycleType σ
    rw [h1, Multiset.sum_replicate, smul_eq_mul, hk] at h2
    rw [h1]
    congr 1
    omega

theorem cycleType_of_pow_three_eq_one {σ : Perm (Fin 9)} (h : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} ∨ σ.cycleType = {3, 3, 3} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 3 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one h⟩
  have hsum := Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1 (Perm.cycleType_eq_zero.mp hk)
  have hk3 : k ≤ 3 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  rw [hk]
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem card_centralizer_perm_of_cycleType_eq_three {σ : Perm (Fin 9)} (h : σ.cycleType = {3}) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 9)))) = 2160 := by
  rw [Perm.nat_card_centralizer, h, Fintype.card_fin]
  decide

theorem card_centralizer_perm_of_cycleType_eq_three_three {σ : Perm (Fin 9)}
    (h : σ.cycleType = {3, 3}) : Nat.card (centralizer ({σ} : Set (Perm (Fin 9)))) = 108 := by
  rw [Perm.nat_card_centralizer, h, Fintype.card_fin]
  decide

theorem card_centralizer_perm_of_cycleType_eq_three_three_three {σ : Perm (Fin 9)}
    (h : σ.cycleType = {3, 3, 3}) : Nat.card (centralizer ({σ} : Set (Perm (Fin 9)))) = 162 := by
  rw [Perm.nat_card_centralizer, h, Fintype.card_fin]
  decide

theorem cycleType_sbar₁ : (sbar₁ : Perm (Fin 9)).cycleType = {3} :=
  (cycleType_eq_replicate_iff_of_pow_three_eq_one (by decide) 1).mpr (by decide)

theorem cycleType_sbar₂ : (sbar₂ : Perm (Fin 9)).cycleType = {3, 3} :=
  (cycleType_eq_replicate_iff_of_pow_three_eq_one (by decide) 2).mpr (by decide)

theorem cycleType_sbar₃ : (sbar₃ : Perm (Fin 9)).cycleType = {3, 3, 3} :=
  (cycleType_eq_replicate_iff_of_pow_three_eq_one (by decide) 3).mpr (by decide)

private theorem cycleType_eq_two_two_two_two {σ : Perm (Fin 9)} (h : σ ^ 2 = 1)
    (hs : σ.support.card = 2 * 4) : σ.cycleType = {2, 2, 2, 2} := by
  rw [← multiset_replicate_four_two, cycleType_eq_replicate_iff_of_sq_eq_one h]
  exact hs

theorem cycleType_tbar : (tbar : Perm (Fin 9)).cycleType = {2, 2, 2, 2} :=
  cycleType_eq_two_two_two_two (by decide) (by decide)

theorem cycleType_bbar₁ : (bbar₁ : Perm (Fin 9)).cycleType = {2, 2, 2, 2} :=
  cycleType_eq_two_two_two_two (by decide) (by decide)

theorem cycleType_bbar₂ : (bbar₂ : Perm (Fin 9)).cycleType = {2, 2, 2, 2} :=
  cycleType_eq_two_two_two_two (by decide) (by decide)

theorem cycleType_bbar₃ : (bbar₃ : Perm (Fin 9)).cycleType = {2, 2, 2, 2} :=
  cycleType_eq_two_two_two_two (by decide) (by decide)

theorem orderOf_sbar₁ : orderOf sbar₁ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext (show (sbar₁ : Perm (Fin 9)) ^ 3 = 1 by decide))
    (ne_one_of_cycleType_eq cycleType_sbar₁ (by decide))

theorem orderOf_sbar₂ : orderOf sbar₂ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext (show (sbar₂ : Perm (Fin 9)) ^ 3 = 1 by decide))
    (ne_one_of_cycleType_eq cycleType_sbar₂ (by decide))

theorem orderOf_sbar₃ : orderOf sbar₃ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext (show (sbar₃ : Perm (Fin 9)) ^ 3 = 1 by decide))
    (ne_one_of_cycleType_eq cycleType_sbar₃ (by decide))

theorem bbar₁_conj_sbar₁ : bbar₁ * sbar₁ * bbar₁⁻¹ = sbar₁⁻¹ :=
  Subtype.ext (show (bbar₁ : Perm (Fin 9)) * sbar₁ * (bbar₁ : Perm (Fin 9))⁻¹ =
    (sbar₁ : Perm (Fin 9))⁻¹ by decide)

theorem bbar₂_conj_sbar₂ : bbar₂ * sbar₂ * bbar₂⁻¹ = sbar₂⁻¹ :=
  Subtype.ext (show (bbar₂ : Perm (Fin 9)) * sbar₂ * (bbar₂ : Perm (Fin 9))⁻¹ =
    (sbar₂ : Perm (Fin 9))⁻¹ by decide)

theorem bbar₃_conj_sbar₃ : bbar₃ * sbar₃ * bbar₃⁻¹ = sbar₃⁻¹ :=
  Subtype.ext (show (bbar₃ : Perm (Fin 9)) * sbar₃ * (bbar₃ : Perm (Fin 9))⁻¹ =
    (sbar₃ : Perm (Fin 9))⁻¹ by decide)

theorem tbar_conj_sbar₁ : tbar * sbar₁ * tbar⁻¹ = sbar₁⁻¹ :=
  Subtype.ext (show (tbar : Perm (Fin 9)) * sbar₁ * (tbar : Perm (Fin 9))⁻¹ =
    (sbar₁ : Perm (Fin 9))⁻¹ by decide)

theorem card_centralizer_conj {X : Type*} [Group X] (g a : X) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set X)) = Nat.card (centralizer ({a} : Set X)) := by
  have h : centralizer ({g * a * g⁻¹} : Set X) =
      (centralizer ({a} : Set X)).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [hx]
        _ = a * (g⁻¹ * x * g) := by group
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
        _ = g * (a * y) * g⁻¹ := by rw [hy]
        _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  rw [h, card_map_of_injective (MulAut.conj g).injective]

theorem card_centralizer_sbar₁ :
    Nat.card (centralizer ({sbar₁} : Set (alternatingGroup (Fin 9)))) = 1080 := by
  have h := CFSG.GH74.GLS.Layer3.card_centralizer_alt_mul_two sbar₁ (swap 3 4)
    (Perm.sign_swap (by decide)) (by decide)
  rw [card_centralizer_perm_of_cycleType_eq_three cycleType_sbar₁] at h
  omega

theorem card_centralizer_sbar₂ :
    Nat.card (centralizer ({sbar₂} : Set (alternatingGroup (Fin 9)))) = 54 := by
  have h := CFSG.GH74.GLS.Layer3.card_centralizer_alt_mul_two sbar₂ (swap 0 1)
    (Perm.sign_swap (by decide)) (by decide)
  rw [card_centralizer_perm_of_cycleType_eq_three_three cycleType_sbar₂] at h
  omega

theorem card_centralizer_sbar₃ :
    Nat.card (centralizer ({sbar₃} : Set (alternatingGroup (Fin 9)))) = 81 := by
  have h := CFSG.GH74.GLS.Layer3.card_centralizer_alt_mul_two sbar₃
    (swap 0 3 * swap 1 4 * swap 2 5) (by decide) (by decide)
  rw [card_centralizer_perm_of_cycleType_eq_three_three_three cycleType_sbar₃] at h
  omega

theorem isConj_sbar₁ {g : alternatingGroup (Fin 9)} (hg : (g : Perm (Fin 9)).cycleType = {3}) :
    IsConj sbar₁ g :=
  isConj_of_commute_of_sign_eq_neg_one
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_sbar₁.trans hg.symm))
    (Perm.sign_swap (show (3 : Fin 9) ≠ 4 by decide))
    (show swap (3 : Fin 9) 4 * (sbar₁ : Perm (Fin 9)) = (sbar₁ : Perm (Fin 9)) * swap 3 4 by
      decide)

theorem isConj_sbar₂ {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {3, 3}) : IsConj sbar₂ g :=
  isConj_of_commute_of_sign_eq_neg_one
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_sbar₂.trans hg.symm))
    (Perm.sign_swap (show (0 : Fin 9) ≠ 1 by decide))
    (show swap (0 : Fin 9) 1 * (sbar₂ : Perm (Fin 9)) = (sbar₂ : Perm (Fin 9)) * swap 0 1 by
      decide)

theorem isConj_sbar₃ {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {3, 3, 3}) : IsConj sbar₃ g :=
  isConj_of_commute_of_sign_eq_neg_one
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_sbar₃.trans hg.symm))
    (show Perm.sign (swap (0 : Fin 9) 3 * swap 1 4 * swap 2 5) = -1 by decide)
    (show swap (0 : Fin 9) 3 * swap 1 4 * swap 2 5 * (sbar₃ : Perm (Fin 9)) =
      (sbar₃ : Perm (Fin 9)) * (swap 0 3 * swap 1 4 * swap 2 5) by decide)

theorem isConj_sbar_of_pow_three_eq_one {g : alternatingGroup (Fin 9)} (h : g ^ 3 = 1)
    (h1 : g ≠ 1) : IsConj sbar₁ g ∨ IsConj sbar₂ g ∨ IsConj sbar₃ g := by
  rcases cycleType_of_pow_three_eq_one (σ := (g : Perm (Fin 9)))
      (by rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]) (fun h' => h1 (Subtype.ext h'))
    with hg | hg | hg
  · exact Or.inl (isConj_sbar₁ hg)
  · exact Or.inr (Or.inl (isConj_sbar₂ hg))
  · exact Or.inr (Or.inr (isConj_sbar₃ hg))

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.Janko
