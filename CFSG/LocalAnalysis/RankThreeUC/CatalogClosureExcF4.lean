module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LieType.Chevalley.CharTwoRank
import CFSG.LieType.Chevalley.ParabolicRadicalLevi
import CFSG.Quasithin.Background.A318PCRank
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Certified

set_option linter.unusedSectionVars false


section Parabolic

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem parabolic_le_twoLocalClosure {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (adjointGroup τ K)}
    (hE : ∀ e ∈ E, ((e : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J)
    {x : adjointGroup τ K} (hx : (x : ModGL τ K) ∈ parabolicSubgroup τ K J) :
    x ∈ twoLocalClosure E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQP, -, -, -, -, -, -, -, -, -, -, -, hpg⟩ := parabolic_root_radical_Levi_factors τ K J
  obtain ⟨-, hQr, hQne⟩ := hpg 2
  have hPJN := parabolicSubgroup_le_normalizer_parabolicRadical (τ := τ) (K := K) J
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K :=
    hQP.trans (parabolicSubgroup_le_adjointGroup τ K J)
  set R₀ : Subgroup (adjointGroup τ K) :=
    (parabolicRadical τ K J).subgroupOf (adjointGroup τ K) with hR₀
  have hR₀ne : R₀ ≠ ⊥ := by
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hQne hJ)
    intro h
    have hq : (⟨(q : ModGL τ K), hQC q.2⟩ : adjointGroup τ K) ∈ R₀ :=
      Subgroup.mem_subgroupOf.2 q.2
    rw [h, Subgroup.mem_bot] at hq
    have hq' : (q : ModGL τ K) = 1 := congrArg Subtype.val hq
    exact hq1 (Subtype.ext hq')
  have hR₀r : IsPGroup 2 R₀ := hQr.comap_subtype
  have hN : ∀ y : adjointGroup τ K, (y : ModGL τ K) ∈ parabolicSubgroup τ K J →
      y ∈ Subgroup.normalizer (R₀ : Set (adjointGroup τ K)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hR₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hPJN hy) z
  have hloc : IsTwoLocal (Subgroup.normalizer (R₀ : Set (adjointGroup τ K))) :=
    ⟨R₀, hR₀ne, hR₀r, rfl⟩
  have hle : Subgroup.normalizer (R₀ : Set (adjointGroup τ K)) ≤ twoLocalClosure E :=
    le_iSup₂_of_le (Subgroup.normalizer (R₀ : Set (adjointGroup τ K)))
      ⟨hloc, fun e he => hN e (hE e he)⟩ (le_refl _)
  exact hle (hN x hx)

theorem parabolic_sup_eq_adjointGroup {J J' : Set (Fin τ.rank)} (h : ∀ i, i ∈ J ∨ i ∈ J') :
    parabolicSubgroup τ K J ⊔ parabolicSubgroup τ K J' = adjointGroup τ K := by
  refine le_antisymm (sup_le (parabolicSubgroup_le_adjointGroup τ K J)
    (parabolicSubgroup_le_adjointGroup τ K J')) ?_
  rw [(borel_weyl_generation τ K).1]
  refine sup_le (le_sup_of_le_left (borelGroup_le_parabolicSubgroup J)) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  rcases h i with hi | hi
  · exact Subgroup.mem_sup_left (weylElt_mem_parabolicSubgroup hi)
  · exact Subgroup.mem_sup_right (weylElt_mem_parabolicSubgroup hi)

theorem coe_rankOneZ (j : Fin τ.rank) :
    ((rankOneZ (K := K) j : adjointGroup τ K) : ModGL τ K) = xUnit τ K j 1 * yUnit τ K j 1 := by
  apply Units.ext
  simp only [rankOneZ, Subgroup.coe_mul, Units.val_mul]
  rw [← CFSG.LieType.Steinberg.Adjoint.endHom_apply,
    ← CFSG.LieType.Steinberg.Adjoint.endHom_apply,
    CFSG.LieType.Steinberg.Adjoint.endHom_xElt, CFSG.LieType.Steinberg.Adjoint.endHom_yElt]
  rfl

theorem rankOneZ_mem_parabolic {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) :
    ((rankOneZ (K := K) j : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := by
  rw [coe_rankOneZ]
  exact mul_mem (borelGroup_le_parabolicSubgroup J (xUnit_mem_borelGroup j 1))
    (parabolicLevi_le_parabolicSubgroup J (yUnit_mem_parabolicLevi hj 1))

end Parabolic

private def witnessF4Simple : RootWitness .F4 2 where
  word := ![([] : List (Fin 4)), ([] : List (Fin 4))]
  simple := ![(0 : Fin 4), (2 : Fin 4)]

private theorem witnessF4Simple_check : witnessF4Simple.check = true := by decide +kernel

private theorem witnessF4Simple_orthoCheck : witnessF4Simple.orthoCheck = true := by
  decide +kernel

section F4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_rankTwo_closure_top_F4 :
    ∃ E : Subgroup (adjointGroup Tag.F4 K), IsPGroup 3 E ∧ 2 ≤ CFSG.Open.pRank 3 E ∧
      twoLocalClosure E = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, hZA, hZZ⟩ := RootWitness.charTwo_facts witnessF4Simple_check
    witnessF4Simple_orthoCheck (![1, 3] : Fin 2 → Fin 4) (by decide) (K := K)
  let J₁ : Set (Fin 4) := {i | i ≠ 3}
  let J₂ : Set (Fin 4) := {i | i ≠ 1}
  have hJ₁ : J₁ ≠ Set.univ := fun h => by
    have : (3 : Fin 4) ∈ J₁ := h ▸ Set.mem_univ _
    exact this rfl
  have hJ₂ : J₂ ≠ Set.univ := fun h => by
    have : (1 : Fin 4) ∈ J₂ := h ▸ Set.mem_univ _
    exact this rfl
  let H : Subgroup (adjointGroup Tag.F4 K) :=
    (parabolicSubgroup Tag.F4 K J₁ ⊓ parabolicSubgroup Tag.F4 K J₂).subgroupOf
      (adjointGroup Tag.F4 K)
  have hZeq : ∀ i, witnessF4Simple.elemZ K i = rankOneZ (witnessF4Simple.simple i) := by
    intro i
    have hw : witnessF4Simple.word i = [] := by fin_cases i <;> rfl
    simp only [RootWitness.elemZ, hw, CoxeterSystem.wordProd_nil, nrep_one, one_mul, inv_one,
      mul_one]
  have hHZ : ∀ i, witnessF4Simple.elemZ K i ∈ H := by
    intro i
    rw [hZeq]
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨rankOneZ_mem_parabolic ?_,
      rankOneZ_mem_parabolic ?_⟩)
    · fin_cases i
      · exact (by decide : (0 : Fin 4) ≠ 3)
      · exact (by decide : (2 : Fin 4) ≠ 3)
    · fin_cases i
      · exact (by decide : (0 : Fin 4) ≠ 1)
      · exact (by decide : (2 : Fin 4) ≠ 1)
  obtain ⟨E, hEH, hEab, hEcard⟩ := CFSG.Quasithin.A318P.exists_elemAbelian_three
    (fun i => witnessF4Simple.elemZ K i) (fun i => witnessF4Simple.elemA K i)
    (fun i => (hZ i).1) (fun i => (hZ i).2.1) (fun i => (hZ i).2.2) hZA hZZ hHZ
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x
    refine ⟨1, ?_⟩
    have := hEab.2 x x.2
    apply Subtype.ext
    simpa using this
  · have := CFSG.SectionRank.le_pRank (Nat.prime_three.one_lt) (le_refl E) hEab hEcard
    omega
  · have hE1 : ∀ e ∈ E, ((e : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
        parabolicSubgroup Tag.F4 K J₁ := fun e he =>
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hEH he))).1
    have hE2 : ∀ e ∈ E, ((e : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
        parabolicSubgroup Tag.F4 K J₂ := fun e he =>
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hEH he))).2
    refine top_le_iff.mp fun x _ => ?_
    have hcov : ∀ i : Fin 4, i ∈ J₁ ∨ i ∈ J₂ := by
      intro i
      by_cases h : i = 3
      · exact Or.inr (by simp [J₂, h])
      · exact Or.inl h
    have hsup := parabolic_sup_eq_adjointGroup (τ := Tag.F4) (K := K) (J := J₁) (J' := J₂) hcov
    have hx : (x : ModGL Tag.F4 K) ∈ parabolicSubgroup Tag.F4 K J₁ ⊔
        parabolicSubgroup Tag.F4 K J₂ := by
      rw [hsup]
      exact x.2
    have hP₁ := parabolicSubgroup_le_adjointGroup Tag.F4 K J₁
    have hP₂ := parabolicSubgroup_le_adjointGroup Tag.F4 K J₂
    have hxs : x ∈ (parabolicSubgroup Tag.F4 K J₁).subgroupOf (adjointGroup Tag.F4 K) ⊔
        (parabolicSubgroup Tag.F4 K J₂).subgroupOf (adjointGroup Tag.F4 K) := by
      rw [← Subgroup.subgroupOf_sup hP₁ hP₂]
      exact hx
    exact (sup_le (fun y hy => parabolic_le_twoLocalClosure hJ₁ hE1 hy)
      (fun y hy => parabolic_le_twoLocalClosure hJ₂ hE2 hy) : _ ≤ twoLocalClosure E) hxs

theorem exists_closure_top_of_F4_iso {G : Type} [Group G] [Finite G]
    (e : G ≃* adjointGroup Tag.F4 K) :
    ∃ E : Subgroup G, IsPGroup 3 E ∧ 2 ≤ CFSG.Open.pRank 3 E ∧ twoLocalClosure E = ⊤ := by
  obtain ⟨E, hE, hr, hc⟩ := exists_rankTwo_closure_top_F4 (K := K)
  refine ⟨E.map e.symm.toMonoidHom, hE.map _, ?_, ?_⟩
  · exact hr.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three e.symm.toMonoidHom e.symm.injective E)
  · refine top_le_iff.mp ?_
    have := map_twoLocalClosure_le e.symm E
    rw [hc, Subgroup.map_top] at this
    have hr : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.symm.toEquiv.surjective
    rw [hr] at this
    exact this

end F4

theorem not_pow_three_dvd_ordF4_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ CFSG.Open.ordF4 2 := by
  intro h
  have e : CFSG.Open.ordF4 2 = 2 ^ 24 * (3 ^ 6 * (5 ^ 2 * (7 ^ 2 * (13 * 17)))) := by
    simp [CFSG.Open.ordF4]
  rw [e] at h
  have hpd : p ∣ 2 ^ 24 * (3 ^ 6 * (5 ^ 2 * (7 ^ 2 * (13 * 17)))) :=
    (dvd_pow_self p three_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h3)
        norm_num at h
      · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1
            (hp.dvd_of_dvd_pow h4)
          norm_num at h
        · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
          · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h5
            norm_num at h
          · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h5
            norm_num at h

theorem three_mem_rankThreeSigmaA_of_F4Two {G : Type} [Group G] [Finite G] (hS : Standing G)
    (h : UntwistedChevalleyModel G .F4 2) : 3 ∈ rankThreeSigmaA G := by
  have hrank : CFSG.Assembly.evenRank G = 3 := (CFSG.Assembly.evenRank_eq_open G).trans hS.rank
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 h
  have hsig : CFSG.Assembly.RankThreeEven.sigmaA G = {3} := by
    refine (CFSG.RankThree.LocalRank.rank_three_selector_eq_three_iff hrank).2 ?_
    intro q hq h3q
    have hq5 : 5 ≤ q := by
      have : q ≠ 4 := by
        rintro rfl
        norm_num at hq
      omega
    have h2 := localRank_le_two_of_no_cube (X := G) hq fun E _ hcardE =>
      not_pow_three_dvd_ordF4_two hq hq5 (hcard ▸ hcardE ▸ Subgroup.card_subgroup_dvd_card E)
    omega
  have h3 : (3 : ℕ) ∈ CFSG.Assembly.RankThreeEven.sigmaA G := by
    rw [hsig]
    exact Set.mem_singleton 3
  exact h3

theorem not_rankThreeUC_of_F4Two {G : Type} [Group G] [Finite G] (hS : Standing G) {f : ℕ}
    (hf : f = 1) (h : ChevalleyExceptionalModel G .F4 2 f) : ¬ rankThreeUC G := by
  subst hf
  obtain ⟨-, hm⟩ := h
  have hm2 : UntwistedChevalleyModel G .F4 2 := by simpa using hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 2 := charP_two_of_card (f := 1) (by simpa using hK)
  intro hUC
  let e2 : AdjointQuotient .F4 K ≃* adjointGroup .F4 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  obtain ⟨E, hE, hr, hc⟩ := exists_closure_top_of_F4_iso (e.trans e2)
  exact twoLocalClosure_ne_top hS hUC (three_mem_rankThreeSigmaA_of_F4Two hS hm2) hE hr hc

end Certified

end CFSG.LocalAnalysis.RankThreeUC
