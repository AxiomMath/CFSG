module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryF1
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOddCenter

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

@[expose] def DeltaAlphaTwo (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = fam → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → D.q = 2 →
      ∀ p : G, D.IsAlphaClass p → DeltaCentral A p (D.alpha p)

@[expose] def SymplecticJ23Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      D.q = 2 → ∀ (p : G) (ℓ : ℕ), (1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨ D.SuzukiType p .c ℓ →
        ∃ a b : G, (∃ k, D.SuzukiType a .a k) ∧ D.SuzukiType b .b 1 ∧
          DeltaCentral A p (D.alpha a ⊔ D.alpha b) ∧ D.alpha b ≤ centralizer (D.alpha a : Set G)

@[expose] def OrthJ4Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    (D.family = .orthPlus ∨ D.family = .orthMinus) → CFSG.Open.IsQuasisimple ↥A →
      Odd (Nat.card (center A)) → D.q = 2 → ∀ (p : G) (ℓ : ℕ), D.SuzukiType p .c ℓ →
        ∃ Z : Subgroup G, DeltaCentral A p Z ∧ Nat.card Z ≤ 2

namespace ClassicalModel

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def ExcTwo : ClassicalModel A → Prop
  | @linear .. => False
  | @unitary _ _ _ n m _ _ _ _ _ _ _ => (n = 4 ∨ n = 6) ∧ m = 1
  | @symplectic _ _ _ n m _ _ _ _ _ _ _ _ => n = 3 ∧ m = 1
  | @orthPlus _ _ _ n m _ _ _ _ _ _ _ => n = 4 ∧ m = 1
  | @orthMinus .. => False

end ClassicalModel

@[expose] def Classical222TwoExcCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.ExcTwo → Hyp221 A T → Odd (Nat.card (center A))

@[expose] def Classical222TwoB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.q = 2 → Hyp221 A T → Odd (Nat.card (center A)) →
      ¬ (∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤ centralizer (T : Set G)) →
        ∃ t ∈ T, t ≠ 1 ∧ CaseQTwo D T t

theorem ClassicalModel.odd_card_center_of_not_excTwo {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (D : ClassicalModel A) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hD : ¬ D.ExcTwo) : Odd (Nat.card (center ↥A)) := by
  have hA' : commutator ↥A = ⊤ := hA.1
  cases D with
  | linear n m hn hm hnm K hK e =>
    exact ClassicalModel.odd_card_center_of_linear (.linear n m hn hm hnm K hK e) rfl hA
  | unitary n m hn hm K hK e =>
    simp only [ClassicalModel.ExcTwo, not_and] at hD
    refine odd_card_center_of_psu hA' hn ⟨⟨Nat.prime_two, hm, by omega, ?_⟩, K, inferInstance,
      inferInstance, hK, ⟨e⟩⟩ (fun h => hD (Or.inl h.1) h.2) (fun h => hD (Or.inr h.1) h.2)
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  | symplectic n m hn hm hnm K hK e =>
    simp only [ClassicalModel.ExcTwo, not_and] at hD
    refine odd_card_center_of_psp_pomega hA' (Or.inl rfl)
      ⟨⟨Nat.prime_two, hm, hn, hnm⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩ ?_
    intro h
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq,
      false_and, true_and] at h
    exact hD h.1 h.2
  | orthPlus n m hn hm K hK e =>
    simp only [ClassicalModel.ExcTwo, not_and] at hD
    refine odd_card_center_of_psp_pomega hA' (Or.inr (Or.inl rfl))
      ⟨⟨Nat.prime_two, hm, hn⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩ ?_
    intro h
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq,
      false_and, false_or, true_and] at h
    exact hD h.1 h.2
  | orthMinus n m hn hm K hK b c hbc e =>
    refine odd_card_center_of_psp_pomega hA' (Or.inr (Or.inr rfl))
      ⟨⟨Nat.prime_two, hm, hn⟩, K, inferInstance, inferInstance, hK, b, c, hbc, ⟨e⟩⟩
      (by simp)

private theorem eq_zero_or_eq_one_of_card_eq_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  classical
  rcases eq_or_ne a 0 with h0 | h0
  · exact Or.inl h0
  rcases eq_or_ne a 1 with h1 | h1
  · exact Or.inr h1
  exfalso
  have : Fintype K := Fintype.ofFinite K
  have h3 : ({a, 0, 1} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h0, h1]), Finset.card_pair zero_ne_one]
  have h4 := Finset.card_le_univ ({a, 0, 1} : Finset K)
  rw [h3, Fintype.card_eq_nat_card, hK] at h4
  omega

theorem exists_alphaHom_unitary {G : Type} [Group G] {A : Subgroup G} {n m : ℕ} {K : Type}
    [Field K] (hU : UnitaryFieldData 2 m K)
    {e : rankTwoQuot A ≃* StatedProj (StatedSU n (2 ^ m) K)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} {M : GL (Fin n) K} (hpM : Represents e p M) (hM2 : orderOf M = 2) :
    ∃ φ : Multiplicative hU.fixedField →* G, Function.Injective φ ∧
      φ.range = alphaGroup e p := by
  have : CharP K 2 := hU.charP
  set σ := hU.bar with hσdef
  have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
  have hσq : ∀ x, σ x = x ^ 2 ^ m := hU.bar_apply
  have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hpM.2.1
  have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
    rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
    calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
        adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
      (M : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  have hN := sub_one_mul_self_eq_zero hM2
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM2
    omega
  have hN0 := sub_one_ne_zero hM1
  set F := hU.fixedField with hF
  let ιF : F →+* K := F.subtype
  have hιF : ∀ a : F, σ (ιF a) = ιF a := fun a => (hU.mem_fixedField).mp a.2
  have hunip : ∀ a : F, unipGL ((M : Matrix (Fin n) (Fin n) K) - 1) hN (ιF a) ∈
      StatedSU n (2 ^ m) K := by
    intro a
    refine mem_statedSU_of hσq (det_unipGL hN _) ?_
    have h1 : adjM σ (unipGL _ hN (ιF a) : Matrix (Fin n) (Fin n) K) =
        unipGL _ hN (ιF a) := by
      rw [coe_unipGL, adjM_add, adjM_one, adjM_smul, hιF, hNh]
    rw [h1, ← Units.val_mul, ← sq, unipGL_sq, Units.val_one]
  have hσF : ∀ N ∈ StatedSU n (2 ^ m) K, ∀ a : K,
      (N : Matrix (Fin n) (Fin n) K) - 1 = a • ((M : Matrix (Fin n) (Fin n) K) - 1) →
        ∃ d : F, ιF d = a := by
    intro N hN' a ha
    have hNu := adjM_mul_self_of_mem_statedSU hσ hσq hN'
    have hNeq : (N : Matrix (Fin n) (Fin n) K) =
        1 + a • ((M : Matrix (Fin n) (Fin n) K) - 1) := by
      rw [← ha, add_sub_cancel]
    rw [hNeq, adjM_add, adjM_one, adjM_smul, hNh, add_mul, one_mul, mul_add, mul_one,
      smul_mul_smul_comm, hN, smul_zero, add_zero, add_assoc, ← add_smul, add_eq_left,
      smul_eq_zero] at hNu
    have hσa : σ a = a := by
      rcases hNu with h | h
      · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
        exact h.symm
      · exact absurd h hN0
    exact ⟨⟨a, (hU.mem_fixedField).mpr hσa⟩, rfl⟩
  obtain ⟨φ, hinj, hrange, -⟩ := exists_alphaHom_of hZ ιF hpM hM2 hN hunip hσF
  exact ⟨φ, hinj, hrange⟩

theorem ClassicalModel.card_alpha_le_two {G : Type} [Group G] {A : Subgroup G}
    (D : ClassicalModel A) (hq : D.q = 2) (hZ : Odd (Nat.card (center ↥A))) {x : G}
    (hx : x ∈ A) (hx2 : orderOf x = 2) : Nat.card (D.alpha x) ≤ 2 := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hm1 : ∀ m : ℕ, 2 ^ m = 2 → m = 1 := fun m h =>
    Nat.pow_right_injective (le_refl 2) (by simpa using h)
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    have hMsq : M ^ 2 = 1 := by have h := pow_orderOf_eq_one M; rwa [hM2] at h
    have hE := sub_one_mul_self hMsq
    have h := card_alphaGroup hZ hxM hM2 hE (fun a => subset_closure (det_unipGL hE a))
    show Nat.card (alphaGroup e x) ≤ 2
    rw [h, hK, hm1 m hq, pow_one]
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    have hMsq : M ^ 2 = 1 := by have h := pow_orderOf_eq_one M; rwa [hM2] at h
    have hE := sub_one_mul_self hMsq
    have h := card_alphaGroup hZ hxM hM2 hE (fun a => unipGL_mem_statedSp hxM.2.1 hMsq hE a)
    show Nat.card (alphaGroup e x) ≤ 2
    rw [h, hK, hm1 m hq, pow_one]
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    have hMsq : M ^ 2 = 1 := by have h := pow_orderOf_eq_one M; rwa [hM2] at h
    have hE := sub_one_mul_self hMsq
    have hK2 : Nat.card K = 2 := by rw [hK, hm1 m hq, pow_one]
    have h := card_alphaGroup hZ hxM hM2 hE (fun a => by
      rcases eq_zero_or_eq_one_of_card_eq_two hK2 a with rfl | rfl
      · rw [unipGL_zero]
        exact one_mem _
      · rw [show unipGL _ hE 1 = M from Units.ext (by rw [coe_unipGL, one_smul,
          add_sub_cancel])]
        exact hxM.2.1)
    show Nat.card (alphaGroup e x) ≤ 2
    rw [h, hK2]
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    have hMsq : M ^ 2 = 1 := by have h := pow_orderOf_eq_one M; rwa [hM2] at h
    have hE := sub_one_mul_self hMsq
    have hK2 : Nat.card K = 2 := by rw [hK, hm1 m hq, pow_one]
    have h := card_alphaGroup hZ hxM hM2 hE (fun a => by
      rcases eq_zero_or_eq_one_of_card_eq_two hK2 a with rfl | rfl
      · rw [unipGL_zero]
        exact one_mem _
      · rw [show unipGL _ hE 1 = M from Units.ext (by rw [coe_unipGL, one_smul,
          add_sub_cancel])]
        exact hxM.2.1)
    show Nat.card (alphaGroup e x) ≤ 2
    rw [h, hK2]
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : CharP K 2 := hU.charP
    have : Finite K := hU.finite
    obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    obtain ⟨φ, hinj, hrange⟩ := exists_alphaHom_unitary hU hZ hxM hM2
    show Nat.card (alphaGroup e x) ≤ 2
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    show Nat.card hU.fixedField ≤ 2
    rw [hU.card_fixedField, hm1 m hq, pow_one]

theorem deltaAlphaTwo_linear : DeltaAlphaTwo .linear := fun _ _ _ _ D hD _ hZ _ _ hp =>
  deltaCentral_alpha_linear D hD hZ hp

theorem deltaAlphaTwo_unitary : DeltaAlphaTwo .unitary := by
  intro G _ _ A D hD _ hZ hq p hp
  cases D with
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : CharP K 2 := hU.charP
    have : Finite K := hU.finite
    have hm1 : m = 1 := Nat.pow_right_injective (le_refl 2) (show 2 ^ m = 2 ^ 1 from hq)
    have hK4 : Nat.card K = 4 := by rw [hK, hm1]; norm_num
    obtain ⟨ℓ0, hpℓ⟩ := hp
    obtain ⟨ω, hω0, hω1⟩ := exists_scalar_ne_zero_ne_one (K := K) (by omega)
    have hω3 : ω * ω * ω = 1 := by
      have : Fintype K := Fintype.ofFinite K
      have h := FiniteField.pow_card_sub_one_eq_one ω hω0
      rw [Fintype.card_eq_nat_card, hK4] at h
      rw [← h]
      ring
    have hσω : hU.bar ω = ω * ω := by
      rw [hU.bar_apply, hm1]
      ring
    exact deltaCentral_unitary hn hK hU hZ (quadSep_of_cube hσω hω3 hω1) hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem deltaAlphaTwo_of (hSp : DeltaAlphaTwo .symplectic) (hP : DeltaAlphaTwo .orthPlus)
    (hM : DeltaAlphaTwo .orthMinus) : ∀ fam : Family, DeltaAlphaTwo fam
  | .linear => deltaAlphaTwo_linear
  | .unitary => deltaAlphaTwo_unitary
  | .symplectic => hSp
  | .orthPlus => hP
  | .orthMinus => hM

namespace Hyp221

variable {G : Type} [Group G] [Finite G] {A T : Subgroup G}

theorem false_of_cond_two (H : Hyp221 A T) (D : ClassicalModel A) (hq : D.q = 2)
    (hZ : Odd (Nat.card (center ↥A))) (hDA : DeltaAlphaTwo D.family) (hJ23 : SymplecticJ23Two)
    (hJ4 : OrthJ4Two)
    (h212 : ∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤ centralizer (T : Set G)) :
    False := by
  have hA := H.quasisimple
  have h4 := H.four_le
  have hsmall : ∀ t ∈ T, t ≠ 1 → ∀ p : G, IsAPart A t p → ∀ Z : Subgroup G,
      DeltaCentral A p Z → Nat.card Z ≤ 2 → False := by
    intro t ht ht1 p hp Z hC hZ2
    have hle := H.card_le_of_forall_mem hZ fun t' ht' p' hp' =>
      H.aPart_mem_of_deltaCentral hZ h212 ht ht1 hp hC ht' hp'
    omega
  have halpha : ∀ t ∈ T, t ≠ 1 → ∀ p : G, IsAPart A t p → D.IsAlphaClass p → False :=
    fun t ht ht1 p hp hcls => hsmall t ht ht1 p hp _ (hDA G A D rfl hA hZ hq p hcls)
      (D.card_alpha_le_two hq hZ hp.1 (H.orderOf_aPart hZ ht ht1 hp))
  have hT : T ≠ ⊥ := by
    intro h
    rw [h, card_bot] at h4
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := (ne_bot_iff_exists_ne_one).mp hT
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
  have hp2 := H.orderOf_aPart hZ ht ht1' hp
  cases hfam : D.family with
  | linear =>
    refine halpha t ht ht1' p hp ?_
    simp only [ClassicalModel.IsAlphaClass, hfam]
    exact D.exists_hasRank hZ hp.1 hp2
  | unitary =>
    refine halpha t ht ht1' p hp ?_
    simp only [ClassicalModel.IsAlphaClass, hfam]
    exact D.exists_hasRank hZ hp.1 hp2
  | symplectic =>
    have hJ : (∃ ℓ, (1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨ D.SuzukiType p .c ℓ) → False := by
      rintro ⟨ℓ, h⟩
      obtain ⟨a, b, ⟨k, hak⟩, hb, hC, hba⟩ := hJ23 G A D hfam hA hZ hq p ℓ h
      by_cases hin : ∃ t' ∈ T, t' ≠ 1 ∧ ∃ v : G, IsAPart A t' v ∧ (v ∈ D.alpha a ∨ v ∈ D.alpha b)
      · obtain ⟨t', ht', ht'1, v, hv, hva | hvb⟩ := hin
        · refine halpha t' ht' ht'1 v hv ?_
          simp only [ClassicalModel.IsAlphaClass, hfam]
          exact Or.inl ⟨k, D.suzukiType_of_mem_alpha hfam hZ hak hva (H.aPart_ne_one ht' ht'1 hv)⟩
        · refine halpha t' ht' ht'1 v hv ?_
          simp only [ClassicalModel.IsAlphaClass, hfam]
          exact Or.inr (D.suzukiType_of_mem_alpha hfam hZ hb hvb (H.aPart_ne_one ht' ht'1 hv))
      · have hle := H.card_le_of_sup hZ (hba.trans (centralizer_le_normalizer _))
          (fun t' ht' p' hp' => H.aPart_mem_of_deltaCentral hZ h212 ht ht1' hp hC ht' hp')
          (fun t' ht' ht'1 p' hp' hpa => hin ⟨t', ht', ht'1, p', hp', Or.inl hpa⟩)
        obtain ⟨hbA, hb2⟩ := D.mem_of_suzukiType hb
        have := D.card_alpha_le_two hq hZ hbA hb2
        omega
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inl hfam) hZ hp.1 hp2
    cases L with
    | a =>
      refine halpha t ht ht1' p hp ?_
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact Or.inl ⟨ℓ, hL⟩
    | b =>
      have hpos := D.pos_of_hasRank (D.hasRank_of_suzukiType hL)
      rcases Nat.lt_or_ge 1 ℓ with h1 | h1
      · exact hJ ⟨ℓ, Or.inl ⟨h1, hL⟩⟩
      · obtain rfl : ℓ = 1 := by omega
        refine halpha t ht ht1' p hp ?_
        simp only [ClassicalModel.IsAlphaClass, hfam]
        exact Or.inr hL
    | c => exact hJ ⟨ℓ, Or.inr hL⟩
  | orthPlus =>
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inr (Or.inl hfam)) hZ hp.1 hp2
    cases L with
    | a =>
      refine halpha t ht ht1' p hp ?_
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact ⟨ℓ, hL⟩
    | b => exact orthTypeAC G A D (Or.inl hfam) p ℓ hL
    | c =>
      obtain ⟨Z, hC, hZ2⟩ := hJ4 G A D (Or.inl hfam) hA hZ hq p ℓ hL
      exact hsmall t ht ht1' p hp Z hC hZ2
  | orthMinus =>
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inr (Or.inr hfam)) hZ hp.1 hp2
    cases L with
    | a =>
      refine halpha t ht ht1' p hp ?_
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact ⟨ℓ, hL⟩
    | b => exact orthTypeAC G A D (Or.inr hfam) p ℓ hL
    | c =>
      obtain ⟨Z, hC, hZ2⟩ := hJ4 G A D (Or.inr hfam) hA hZ hq p ℓ hL
      exact hsmall t ht ht1' p hp Z hC hZ2

end Hyp221

theorem classical222Two_of (hExc : Classical222TwoExcCenter) (hSp : DeltaAlphaTwo .symplectic)
    (hP : DeltaAlphaTwo .orthPlus) (hM : DeltaAlphaTwo .orthMinus) (hJ23 : SymplecticJ23Two)
    (hJ4 : OrthJ4Two) (hB : Classical222TwoB) : Classical222Two := by
  intro G _ _ A T D hq H
  have hZ : Odd (Nat.card (center ↥A)) := by
    by_cases hE : D.ExcTwo
    · exact hExc G A T D hE H
    · exact D.odd_card_center_of_not_excTwo H.quasisimple hE
  by_cases h212 : ∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤
      centralizer (T : Set G)
  · exact (H.false_of_cond_two D hq hZ (deltaAlphaTwo_of hSp hP hM D.family) hJ23 hJ4
      h212).elim
  · exact hB G A T D hq H hZ h212

end CFSG.ComponentClassification.RankTwoClassical
