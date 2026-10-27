module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLieFast
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank

theorem card_of_isTwinGroup {X : Type} [Group X] (h : IsTwinGroup X) :
    Nat.card X = 1451520 ∨ Nat.card X = 174182400 := by
  rcases h with h | h
  · exact Or.inl h.card_psp_three_two
  · right
    rw [h.card_eq_lieOrd (by norm_num)]
    decide

@[expose] def twinSearchProp (N : ℕ) : StatedLieTag → ℕ → ℕ → ℕ → Bool := fun t n q o =>
  !(o == N && (q == 3 ||
    (q % 2 == 1 && ((t == .PSL && (n == 2 || n == 3)) || (t == .PSU && n == 3)))))

set_option maxRecDepth 100000 in
theorem lieSearch_sp62 : lieSearch [2, 3, 5, 7] 1451520 (twinSearchProp 1451520) = true := by
  unfold twinSearchProp
  exact lieSearch_of_lieSearchB (L := 20) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lieSearch_o8p2 : lieSearch [2, 3, 5, 7] 174182400 (twinSearchProp 174182400) = true := by
  unfold twinSearchProp
  exact lieSearch_of_lieSearchB (L := 27) (by decide +kernel)

theorem not_lieOrd_eq_twin {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hq : p ^ f = 3 ∨ (p ≠ 2 ∧ ((t = .PSL ∧ (n = 2 ∨ n = 3)) ∨ (t = .PSU ∧ n = 3))))
    (hN : lieOrd t n (p ^ f) = 1451520 ∨ lieOrd t n (p ^ f) = 174182400) : False := by
  have hodd : p ≠ 2 → p ^ f % 2 = 1 := fun hp2 =>
    Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  rcases hN with hN | hN
  · have hps : ∀ r : ℕ, r.Prime → r ∣ 1451520 → r ∈ [2, 3, 5, 7] := fun r hr hd => by
      simpa using mem_of_prime_dvd [(2, 9), (3, 4), (5, 1), (7, 1)] (by decide) (by decide) hr hd
    have h := lieSearch_sound (by norm_num) hps lieSearch_sp62 ht hp hf hn hnB hadm
      (hN ▸ dvd_refl _)
    rw [hN] at h
    rcases hq with hq | ⟨hp2, hq⟩
    · simp [twinSearchProp, hq] at h
    · rcases hq with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp [twinSearchProp, hodd hp2] at h
  · have hps : ∀ r : ℕ, r.Prime → r ∣ 174182400 → r ∈ [2, 3, 5, 7] := fun r hr hd => by
      simpa using mem_of_prime_dvd [(2, 12), (3, 5), (5, 2), (7, 1)] (by decide) (by decide) hr hd
    have h := lieSearch_sound (by norm_num) hps lieSearch_o8p2 ht hp hf hn hnB hadm
      (hN ▸ dvd_refl _)
    rw [hN] at h
    rcases hq with hq | ⟨hp2, hq⟩
    · simp [twinSearchProp, hq] at h
    · rcases hq with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp [twinSearchProp, hodd hp2] at h

theorem search_data_of_fundTag {t : StatedLieTag} {n p f : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) :
    t ∈ searchTags ∧ lieMin t ≤ n ∧ n ≤ lieExp t n + 1 ∧ lieAdm t p f = true := by
  cases t
  case PSL =>
    exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
  case PSU =>
    exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
  case PSp =>
    exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
  case POmegaOdd =>
    exact ⟨by decide, hadm.2.2.1, le_lieExp_add_one hadm.2.2.1 (by simp), rfl⟩
  case POmegaPlus =>
    exact ⟨by decide, hadm.2.2, le_lieExp_add_one hadm.2.2 (by simp), rfl⟩
  case POmegaMinus =>
    exact ⟨by decide, hadm.2.2, le_lieExp_add_one hadm.2.2 (by simp), rfl⟩
  case G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  case trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact ⟨by decide, le_rfl, by omega, rfl⟩
  all_goals exact hfund.elim

section Model


theorem card_eq_lieOrd_of_fundTag {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    (h : CFSG.Blueprint.LieModel G t n p f) : Nat.card G = lieOrd t n (p ^ f) := by
  cases t
  case PSL => exact h.card_eq_lieOrd (by have := hadm.2.2.1; omega)
  case PSU => exact h.card_eq_lieOrd (by have := hadm.2.2.1; omega)
  case PSp => exact h.card_eq_lieOrd (by have := hadm.2.2.1; omega)
  case POmegaOdd => exact h.card_eq_lieOrd (by have := hadm.2.2.1; omega)
  case POmegaPlus => exact h.card_eq_lieOrd (by have := hadm.2.2; omega)
  case POmegaMinus => exact h.card_eq_lieOrd (by have := hadm.2.2; omega)
  case G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  case trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact card_eq_lieOrd_of_exceptional (h.chevalleyExceptionalModel (by decide))
  all_goals exact hfund.elim

theorem card_eq_card_quotient_center {K X : Type} [Group K] [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (φ : K →* X) (hs : Function.Surjective φ)
    (hk : φ.ker ≤ Subgroup.center K) : Nat.card X = Nat.card (K ⧸ Subgroup.center K) := by
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hker : φ.ker = Subgroup.center K := by
    refine le_antisymm hk fun g hg => ?_
    have hφg : φ g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun x => ?_
      obtain ⟨y, rfl⟩ := hs x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg y]
    rw [hZX, Subgroup.mem_bot] at hφg
    exact hφg
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hs)).toEquiv.symm

theorem coincTwin : CoincTwin := by
  intro X _ _ ht
  have hN := card_of_isTwinGroup ht
  haveI : IsSimpleGroup X := by
    rcases ht with h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
    have hp := IsSimpleGroup.prime_card (α := X)
    rcases hN with h | h <;> rw [h] at hp <;> norm_num at hp
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hV, hne, φ, hs, hk⟩
    have hcard := card_eq_card_quotient_center hnab φ hs hk
    rcases hV with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
    · have hL := (ModelFacts.modelClauseZero t n 3 1 Nat.prime_three hfund hadm).2
      have hc := card_eq_lieOrd_of_fundTag hfund hadm hL
      obtain ⟨hst, hmin, hnB, hla⟩ := search_data_of_fundTag hfund hadm
      exact not_lieOrd_eq_twin hst Nat.prime_three le_rfl hmin hnB hla (Or.inl (pow_one 3))
        (by rw [← hc, ← hcard]; exact hN)
    · exact absurd rfl hne
    · have h7920 : Nat.card (CompData.m11.G ⧸ Subgroup.center CompData.m11.G) = 7920 := by
        have hZ : Subgroup.center CompData.m11.G = ⊥ := Q3W.center_m11_eq_bot
        rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
          QuotientGroup.quotientBot).toEquiv]
        exact card_m11_kernel
      rw [hcard, h7920] at hN
      norm_num at hN
  · rintro ⟨p, f, hp, hp2, ⟨-, hl2⟩ | ⟨hl3 | hu3, -⟩⟩
    · exact not_lieOrd_eq_twin (by decide) hp hl2.admissible.2.1 (by decide) (by decide) rfl
        (Or.inr ⟨hp2, Or.inl ⟨rfl, Or.inl rfl⟩⟩)
        (by rw [← hl2.card_eq_lieOrd (by norm_num)]; exact hN)
    · exact not_lieOrd_eq_twin (by decide) hp hl3.admissible.2.1 (by decide) (by decide) rfl
        (Or.inr ⟨hp2, Or.inl ⟨rfl, Or.inr rfl⟩⟩)
        (by rw [← hl3.card_eq_lieOrd (by norm_num)]; exact hN)
    · exact not_lieOrd_eq_twin (by decide) hp hu3.admissible.2.1 (by decide) (by decide) rfl
        (Or.inr ⟨hp2, Or.inr ⟨rfl, rfl⟩⟩)
        (by rw [← hu3.card_eq_lieOrd (by norm_num)]; exact hN)

end Model

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
