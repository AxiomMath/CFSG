module

public import CFSG.GH74.GLS.C3.Layer1.Th2V2ss
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.Orders.Sporadic
public import CFSG.GH74.Filter.Sporadic.All
public import CFSG.GH74.Filter.Monster.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverOrders

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.GH74 CFSG.GH74.Filter CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X]

theorem two_mul_card_le_of_lt {A B : Subgroup X} (h : A < B) : 2 * Nat.card A ≤ Nat.card B := by
  have hd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le h.le
  obtain ⟨c, hc⟩ := hd
  have hlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt h
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases c with _ | _ | c
  · simp at hc; omega
  · simp at hc; omega
  · rw [hc]; nlinarith

theorem exists_gen_card_pow_le (P : Subgroup X) :
    ∃ t : Finset X, (t : Set X) ⊆ P ∧ Subgroup.closure (t : Set X) = P ∧ 2 ^ t.card ≤ Nat.card P := by
  classical
  have key : ∀ (n : ℕ) (s : Finset X), Nat.card P - Nat.card (Subgroup.closure (s : Set X)) = n →
      (s : Set X) ⊆ P → 2 ^ s.card ≤ Nat.card (Subgroup.closure (s : Set X)) →
      ∃ t : Finset X, (t : Set X) ⊆ P ∧ Subgroup.closure (t : Set X) = P ∧
        2 ^ t.card ≤ Nat.card P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hn hsP hs
      by_cases hP : Subgroup.closure (s : Set X) = P
      · exact ⟨s, hsP, hP, by simpa [hP] using hs⟩
      · have hle : Subgroup.closure (s : Set X) ≤ P := (Subgroup.closure_le P).2 hsP
        have hlt : Subgroup.closure (s : Set X) < P := lt_of_le_of_ne hle hP
        obtain ⟨g, hgP, hgs⟩ := IsConcreteLE.exists_of_lt hlt
        have hgs' : g ∉ Subgroup.closure (s : Set X) := hgs
        have hgnot : g ∉ s := fun h => hgs' (Subgroup.subset_closure h)
        have hsub : (insert g s : Finset X).card = s.card + 1 := Finset.card_insert_of_notMem hgnot
        have hlt1 : Subgroup.closure (s : Set X) <
            Subgroup.closure ((insert g s : Finset X) : Set X) := by
          refine lt_of_le_of_ne ?_ ?_
          · exact Subgroup.closure_mono (by simp)
          · intro heq
            apply hgs'
            rw [heq]
            exact Subgroup.subset_closure (by simp)
        have h2 := two_mul_card_le_of_lt hlt1
        have hsub' : ((insert g s : Finset X) : Set X) ⊆ P := by
          intro y hy
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact hgP
          · exact hsP hy
        have hle1 : Subgroup.closure ((insert g s : Finset X) : Set X) ≤ P :=
          (Subgroup.closure_le P).2 hsub'
        have hcardle : Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)) ≤ Nat.card P :=
          Subgroup.card_le_of_le hle1
        have hltcard : Nat.card (Subgroup.closure (s : Set X)) <
            Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)) :=
          Subgroup.card_lt_of_lt hlt1
        refine ih (Nat.card P - Nat.card (Subgroup.closure ((insert g s : Finset X) : Set X)))
          ?_ _ rfl hsub' ?_
        · omega
        · rw [hsub, pow_succ]; omega
  exact key _ ∅ rfl (by simp) (by simp)

theorem gen4_of_factorization_two_le (h : (Nat.card X).factorization 2 ≤ 4) : Gen4 X := by
  intro P hP
  obtain ⟨t, -, ht, hcard⟩ := exists_gen_card_pow_le P
  refine ⟨t, ?_, ht⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : 2 ^ m ∣ Nat.card X := hm ▸ Subgroup.card_subgroup_dvd_card P
  have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hm4 : m ≤ 4 :=
    le_trans ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd) h
  rw [hm] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

theorem card_A6_eq_360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem gen4_A7 : Gen4 (alternatingGroup (Fin 7)) := by
  apply gen4_of_factorization_two_le
  rw [card_A7_eq_2520]
  have hfactor : (2520 : ℕ).factorization 2 = 3 := by
    have hprod : 2520 = 2 ^ 3 * 315 := by decide
    rw [hprod, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]
  omega

theorem nonab_A7 : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  by_contra h
  have h : ∀ a b : alternatingGroup (Fin 7), a * b = b * a := fun a b =>
    by_contra fun hne => h ⟨a, b, hne⟩
  have hc : center (alternatingGroup (Fin 7)) = ⊤ := by
    rw [eq_top_iff']
    intro a
    rw [Subgroup.mem_center_iff]
    intro b
    exact h b a
  have hb : center (alternatingGroup (Fin 7)) = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  have h1 : Nat.card (alternatingGroup (Fin 7)) = 1 := by
    rw [← Subgroup.card_top (G := alternatingGroup (Fin 7)), ← hc, hb, Subgroup.card_bot]
  rw [card_A7_eq_2520] at h1
  omega

theorem not_simpleInC2_A7 :
       ¬ SimpleInC2 ↥(alternatingGroup (Fin 7)) := by
  rintro ⟨-, h⟩
  have hnonab := nonab_A7
  have hg := gen4_A7
  have hc := card_A7_eq_2520
  rcases h with ((hE | he | hU) | hL2 | hL33 | hL43 | hU43 | hG2 | hM11 | hM12 | hM22 | hM23 |
    hM24 | hJ2 | hJ3 | hJ4 | hHS | hSuz | hRu | hCo1 | hCo2 | hFi22 | hFi23 | hFi24 | hTh | hB | hM)
  · exact CFSG.QuasithinUnique.Bridge.Over.not_evenLieType_of_card hc hE
  · obtain ⟨e⟩ := he
    have := Nat.card_congr e.toEquiv
    rw [hc, card_A6_eq_360] at this
    omega
  · have h1 := card_of_lieModel_PSU (n := 3) (p := 3) (f := 1) (by norm_num) (by norm_num) hU
    rw [hc] at h1
    revert h1; decide
  · obtain ⟨p, f, hp, hf, hfm, hmodel⟩ := hL2
    have h1 := card_of_lieModel_PSL (n := 2) (by norm_num) hmodel
    rw [hc] at h1
    exact ordA_one_ne_2520_aux (p ^ f) (by simpa using h1.symm)
  · have h1 := card_of_lieModel_PSL (n := 3) (p := 3) (f := 1) (by norm_num) hL33
    rw [hc] at h1
    revert h1; decide
  · have h1 := card_of_lieModel_PSL (n := 4) (p := 3) (f := 1) (by norm_num) hL43
    rw [hc] at h1
    revert h1; decide
  · have h1 := card_of_lieModel_PSU (n := 4) (p := 3) (f := 1) (by norm_num) (by norm_num) hU43
    rw [hc] at h1
    revert h1; decide
  · have h1 := card_of_lieModel_G2 (n := 0) (p := 3) (f := 1) (by norm_num) hG2
    rw [hc] at h1
    revert h1; decide
  · have h1 := card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hM11
    omega
  · have h1 := card_of_isSporadic_M12 hM12
    rw [hc] at h1
    norm_num at h1
  · have h1 := card_of_isSporadic_M22 hM22
    rw [hc] at h1
    norm_num at h1
  · have h1 := card_of_isSporadic_M23 hM23
    rw [hc] at h1
    norm_num at h1
  · exact t_sporadic_M24 _ hnonab hM24 hg
  · have h1 := card_of_isSporadic_J2 hJ2
    rw [hc] at h1
    norm_num at h1
  · have h1 := card_of_isSporadic_J3 hJ3
    rw [hc] at h1
    norm_num at h1
  · exact t_sporadic_J4 _ hnonab hJ4 hg
  · exact t_sporadic_HS _ hnonab hHS hg
  · exact t_sporadic_Suz _ hnonab hSuz hg
  · exact t_sporadic_Ru _ hnonab hRu hg
  · exact t_sporadic_Co1 _ hnonab hCo1 hg
  · exact t_sporadic_Co2 _ hnonab hCo2 hg
  · exact t_sporadic_Fi22 _ hnonab hFi22 hg
  · exact t_sporadic_Fi23 _ hnonab hFi23 hg
  · exact t_sporadic_Fi24Prime _ hnonab hFi24 hg
  · exact t_sporadic_Th _ hnonab hTh hg
  · exact t_sporadic_B _ hnonab hB hg
  · exact t_sporadic_M _ hnonab hM hg

theorem not_inC2_A7 :
       ¬ InC2 ↥(alternatingGroup (Fin 7)) := by
  rintro ⟨-, -, hS, -⟩
  have hbot : center (alternatingGroup (Fin 7)) = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  have e : alternatingGroup (Fin 7) ⧸ center (alternatingGroup (Fin 7)) ≃*
      alternatingGroup (Fin 7) :=
    (QuotientGroup.congr (center (alternatingGroup (Fin 7))) (⊥ : Subgroup (alternatingGroup (Fin 7)))
      (MulEquiv.refl _) (by rw [hbot]; simp)).trans QuotientGroup.quotientBot
  exact not_simpleInC2_A7 (CFSG.GH74.E2.simpleInC2_of_mulEquiv e hS)

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

theorem b_A7_notC2 :
       B_A7_notC2 :=
  Th2.not_inC2_A7

end CFSG.GH74.GLS
