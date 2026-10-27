module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv CFSG.Assembly.LowTwoRank

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [CFSG.IsElementaryAbelian p G] : CFSG.IsElementaryAbelian p H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

theorem exists_elementary_eight_of_commute {H : Type*} [Group H] [Finite H] {x y c : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hc : orderOf c = 2) (hxy : x * y = y * x)
    (hne : x ≠ y) (hcx : Commute c x) (hcy : Commute c y) (K : Subgroup H) (hxK : x ∈ K)
    (hyK : y ∈ K) (hcK : c ∉ K) :
    ∃ E : Subgroup H, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨V, hVcl, hVel, hVcard⟩ :=
    LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hx hy
      hxy hne
  have hVK : V ≤ K := hVcl.trans ((Subgroup.closure_le K).mpr (by
    rintro g (rfl | rfl)
    · exact hxK
    · exact hyK))
  have hcV : c ∉ V := fun h => hcK (hVK h)
  have hVc : V ≤ Subgroup.centralizer (Subgroup.zpowers c : Set H) := by
    refine hVcl.trans ((Subgroup.closure_le _).mpr ?_)
    have hcomm : ∀ g ∈ ({x, y} : Set H), Commute c g := by
      rintro g (rfl | rfl)
      · exact hcx
      · exact hcy
    intro g hg
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((hcomm g hg).zpow_left k).eq
  obtain ⟨E, -, -, hE, hEcard, -⟩ :=
    LargeEvenClassification.Helpers.commuting_disjoint_elementary_product (firstRank := 2)
      (secondRank := 1) V (Subgroup.zpowers c)
      ((SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVel)
      (ProperTwoGeneratedCore.involution_zpowers_elementary c hc) (by rw [hVcard]; norm_num)
      (by rw [Nat.card_zpowers, hc, pow_one]) hVc
      (ProperTwoGeneratedCore.involution_zpowers_disjoint V c hc hcV)
  exact ⟨E, (SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hE, by
    rw [hEcard]; norm_num⟩

theorem swap_mul_swap_mem_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) : swap a b * swap c d ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

theorem exists_elementary_eight_alternating_eight :
    ∃ E : Subgroup (alternatingGroup (Fin 8)), CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_elementary_eight_of_commute
    (x := ⟨swap 0 1 * swap 2 3, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩)
    (y := ⟨swap 0 2 * swap 1 3, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩)
    (c := ⟨swap 4 5 * swap 6 7, swap_mul_swap_mem_alternatingGroup (by decide) (by decide)⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ((MulAction.stabilizer (Perm (Fin 8)) (4 : Fin 8)).comap
      (alternatingGroup (Fin 8)).subtype) ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by decide) (by decide)
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by decide) (by decide)
  · rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by decide) (by decide)
  · exact Subtype.ext (show (swap (0 : Fin 8) 1 * swap 2 3) * (swap 0 2 * swap 1 3) =
      (swap 0 2 * swap 1 3) * (swap 0 1 * swap 2 3) by decide)
  · intro h
    have h' := congrArg Subtype.val h
    exact absurd (show swap (0 : Fin 8) 1 * swap 2 3 = swap 0 2 * swap 1 3 from h') (by decide)
  · exact Subtype.ext (show (swap (4 : Fin 8) 5 * swap 6 7) * (swap 0 1 * swap 2 3) =
      (swap 0 1 * swap 2 3) * (swap 4 5 * swap 6 7) by decide)
  · exact Subtype.ext (show (swap (4 : Fin 8) 5 * swap 6 7) * (swap 0 2 * swap 1 3) =
      (swap 0 2 * swap 1 3) * (swap 4 5 * swap 6 7) by decide)
  · exact (show (swap (0 : Fin 8) 1 * swap 2 3 : Perm (Fin 8)) 4 = 4 by decide)
  · exact (show (swap (0 : Fin 8) 2 * swap 1 3 : Perm (Fin 8)) 4 = 4 by decide)
  · exact (show ¬ (swap (4 : Fin 8) 5 * swap 6 7 : Perm (Fin 8)) 4 = 4 by decide)

theorem exists_elementary_eight_alternating {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h8 : 8 ≤ Fintype.card Ω) :
    ∃ E : Subgroup (alternatingGroup Ω), CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 8) (β := Ω)
    (by rw [Fintype.card_fin]; exact h8)
  obtain ⟨E, hE, hEcard⟩ := exists_elementary_eight_alternating_eight
  let κ₀ : Perm (Fin 8) →* Perm Ω := Perm.extendDomainHom ι.toEquivRange
  have hκmem : ∀ g : alternatingGroup (Fin 8),
      (κ₀.comp (alternatingGroup (Fin 8)).subtype) g ∈ alternatingGroup Ω := fun g => by
    rw [MonoidHom.comp_apply, Perm.mem_alternatingGroup, Perm.extendDomainHom_apply,
      Perm.sign_extendDomain]
    exact g.2
  let κ : alternatingGroup (Fin 8) →* alternatingGroup Ω :=
    (κ₀.comp (alternatingGroup (Fin 8)).subtype).codRestrict _ hκmem
  have hκ : Function.Injective κ := fun a b h =>
    Subtype.ext (Perm.extendDomainHom_injective _ (congrArg Subtype.val h))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨E.map κ, CFSG.IsElementaryAbelian.map κ, by
    rw [Subgroup.card_map_of_injective hκ, hEcard]⟩

theorem le_twenty_of_mul_sq_sub_one {q N : ℕ} (hq : q * (q ^ 2 - 1) = N) (hN : N ≤ 5040) :
    q ≤ 20 := by
  by_contra h
  push Not at h
  have hsq : 441 ≤ q ^ 2 := by nlinarith
  have hmul : 21 * 440 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul (Nat.succ_le_of_lt h) (by omega)
  omega

theorem prime_pow_eq_prime {p f r : ℕ} (hp : p.Prime) (hr : r.Prime) (h : p ^ f = r) :
    p = r ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact hr.one_lt.ne h
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (h ▸ dvd_pow_self p hf)
  subst hpr
  exact ⟨rfl, Nat.pow_right_injective hp.two_le (h.trans (pow_one p).symm)⟩

theorem prime_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact absurd h (by decide)
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h]
      exact dvd_pow_self p hf
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 2 by rw [h])⟩

theorem alternating_psl_two_parameters_and_degree_seven_stated {X : Type} [Group X]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hm : 5 ≤ Fintype.card Ω)
    (hX : Nonempty (X ≃* alternatingGroup Ω)) :
    (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel X .PSL 2 p f →
      (Fintype.card Ω = 5 ∧ p = 5 ∧ f = 1) ∨ (Fintype.card Ω = 6 ∧ p = 3 ∧ f = 2)) ∧
    (Nonempty (X ≃* alternatingGroup (Fin 7)) → Fintype.card Ω = 7) := by
  obtain ⟨e⟩ := hX
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hAlt : 2 * Nat.card (alternatingGroup Ω) = (Fintype.card Ω).factorial := by
    have h := two_mul_card_alternatingGroup (α := Ω)
    rwa [Fintype.card_perm, ← Nat.card_eq_fintype_card] at h
  refine ⟨fun p f hp2 hmodel => ?_, fun h7 => ?_⟩
  · obtain ⟨⟨hp, -, -⟩, K, hKfield, hKfin, hKcard, ⟨φ⟩⟩ := hmodel
    have : Fact p.Prime := ⟨hp⟩
    have hqodd : Odd (Nat.card K) := by
      rw [hKcard]
      exact (hp.odd_of_ne_two hp2).pow
    have hEl := (OutcomeLocal.odd_projective_linear_two_elementary_two_sections hqodd).2.2.1
    have hcardS := (SectionRank.OddCover.odd_psl_two_sylow_data (K := K) hp2 hKcard).2.2.1
    set ψ : alternatingGroup Ω ≃* StatedProj (StatedSL 2 K) := e.symm.trans φ with hψ
    have hm7 : Fintype.card Ω ≤ 7 := by
      by_contra h8
      push Not at h8
      obtain ⟨E, hE, hEcard⟩ := exists_elementary_eight_alternating (Ω := Ω) (by omega)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hAel : CFSG.IsElementaryAbelian 2 (E.map ψ.toMonoidHom) :=
        CFSG.IsElementaryAbelian.map ψ.toMonoidHom
      have hAcard : Nat.card (E.map ψ.toMonoidHom) = 8 := by
        rw [Subgroup.card_map_of_injective ψ.injective, hEcard]
      have hbound := hEl (E.map ψ.toMonoidHom) ⊥
        (isElementaryAbelian_of_mulEquiv QuotientGroup.quotientBot.symm)
      rw [Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hAcard] at hbound
      omega
    have hq : p ^ f * ((p ^ f) ^ 2 - 1) = (Fintype.card Ω).factorial := by
      have hS : Nat.card (alternatingGroup Ω) = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
        rw [← hcardS]
        exact Nat.card_congr ψ.toEquiv
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      have heven : Even ((p ^ f) ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
      rw [← hAlt, hS, mul_left_comm, Nat.two_mul_div_two_of_even heven]
    set q := p ^ f with hqdef
    set m := Fintype.card Ω with hmdef
    have hq20 : q ≤ 20 := le_twenty_of_mul_sq_sub_one hq (by
      rw [show (5040 : ℕ) = Nat.factorial 7 from rfl]
      exact Nat.factorial_le hm7)
    interval_cases m
    · have hq5 : q = 5 := by
        rw [show Nat.factorial 5 = 120 from rfl] at hq
        interval_cases q <;> first | rfl | (norm_num at hq)
      obtain ⟨hp5, hf1⟩ := prime_pow_eq_prime hp Nat.prime_five hq5
      exact Or.inl ⟨rfl, hp5, hf1⟩
    · have hq9 : q = 9 := by
        rw [show Nat.factorial 6 = 720 from rfl] at hq
        interval_cases q <;> first | rfl | (norm_num at hq)
      obtain ⟨hp3, hf2⟩ := prime_pow_eq_nine hp hq9
      exact Or.inr ⟨rfl, hp3, hf2⟩
    · rw [show Nat.factorial 7 = 5040 from rfl] at hq
      exfalso
      interval_cases q <;> norm_num at hq
  · obtain ⟨e7⟩ := h7
    have h7card : 2 * Nat.card (alternatingGroup (Fin 7)) = Nat.factorial 7 := by
      have h := two_mul_card_alternatingGroup (α := Fin 7)
      rwa [Fintype.card_perm, ← Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have heq : Nat.card (alternatingGroup Ω) = Nat.card (alternatingGroup (Fin 7)) :=
      Nat.card_congr (e.symm.trans e7).toEquiv
    rw [heq, h7card] at hAlt
    exact ((Nat.factorial_inj (by omega)).mp hAlt).symm

theorem alternating_psl_two_parameters_and_degree_seven {X : Type} [Group X]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hm : 5 ≤ Fintype.card Ω)
    (hX : Nonempty (X ≃* alternatingGroup Ω)) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → Assembly.ComponentType.ClassicalModel X .PSL 2 p f →
      (Fintype.card Ω = 5 ∧ p = 5 ∧ f = 1) ∨ (Fintype.card Ω = 6 ∧ p = 3 ∧ f = 2)) ∧
    (Nonempty (X ≃* alternatingGroup (Fin 7)) → Fintype.card Ω = 7) := by
  obtain ⟨h1, h2⟩ := alternating_psl_two_parameters_and_degree_seven_stated hm hX
  exact ⟨fun p f _ hp2 hmodel => h1 p f hp2
    (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hmodel), h2⟩

theorem small_standard_source_alternating_degree_and_parameters_stated {X : Type} [Group X]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hm : 5 ≤ Fintype.card Ω)
    (hX : Nonempty (X ≃* alternatingGroup Ω)) :
    (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel X .PSL 2 p f →
      (Fintype.card Ω = 5 ∧ p = 5 ∧ f = 1) ∨ (Fintype.card Ω = 6 ∧ p = 3 ∧ f = 2)) ∧
    (Nonempty (X ≃* alternatingGroup (Fin 7)) → Fintype.card Ω = 7) ∧
    ¬ StatedClassicalModel X .PSL 3 2 2 := by
  obtain ⟨h1, h2⟩ := alternating_psl_two_parameters_and_degree_seven_stated hm hX
  refine ⟨h1, h2, fun h322 => ?_⟩
  obtain ⟨e⟩ := hX
  exact (PSL3Four.excludes_alternating_models_stated X h322).2.2 Ω hm |>.false e

theorem small_standard_source_alternating_degree_and_parameters {X : Type} [Group X]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hm : 5 ≤ Fintype.card Ω)
    (hX : Nonempty (X ≃* alternatingGroup Ω)) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → Assembly.ComponentType.ClassicalModel X .PSL 2 p f →
      (Fintype.card Ω = 5 ∧ p = 5 ∧ f = 1) ∨ (Fintype.card Ω = 6 ∧ p = 3 ∧ f = 2)) ∧
    (Nonempty (X ≃* alternatingGroup (Fin 7)) → Fintype.card Ω = 7) ∧
    ¬ Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 := by
  obtain ⟨h1, h2⟩ := alternating_psl_two_parameters_and_degree_seven hm hX
  refine ⟨h1, h2, fun h322 => ?_⟩
  obtain ⟨e⟩ := hX
  exact (PSL3Four.excludes_alternating_models X h322).2.2 Ω hm |>.false e

end CFSG.ComponentClassification.SymmetricLocal
