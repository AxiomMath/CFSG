module

public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.LieType.Ree (ReeTag)

theorem card_outer_eq_of_ker_eq_inner {C Q : Type*} [Group C] [Group Q] (Θ : MulAut C →* Q)
    (hs : Function.Surjective Θ) (hker : Θ.ker = inner C) :
    Nat.card (Outer C) = Nat.card Q :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hs)).toEquiv

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem card_sq_dvd_card_adjointGroup
    {τ : Tag} (hτ : 2 ≤ τ.rank) :
    Nat.card K ^ 2 ∣ Nat.card (adjointGroup τ K) := by
  have hU := Subgroup.card_dvd_of_le (posUnipotent_le_adjointGroup (τ := τ) (K := K))
  rw [card_posUnipotent] at hU
  refine (pow_dvd_pow _ ?_).trans hU
  have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot τ).subset fun _ h => h.1
  have hsub : ({Pi.single ⟨0, by omega⟩ 1, Pi.single ⟨1, hτ⟩ 1} : Set (Fin τ.rank → ℤ)) ⊆
      {α | IsRoot τ α ∧ 0 < height α} := by
    rintro _ (rfl | rfl) <;> exact ⟨isRoot_single τ _, by simp [height]⟩
  have hne : (Pi.single (⟨0, by omega⟩ : Fin τ.rank) (1 : ℤ) : Fin τ.rank → ℤ) ≠
      (Pi.single (⟨1, hτ⟩ : Fin τ.rank) (1 : ℤ) : Fin τ.rank → ℤ) := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  calc 2 = ({Pi.single ⟨0, by omega⟩ 1, Pi.single ⟨1, hτ⟩ 1} :
        Set (Fin τ.rank → ℤ)).ncard := (Set.ncard_pair hne).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

theorem card_SL_dvd_card_adjointGroup
    (hK : ringChar K ≠ 2) (τ : Tag) :
    Nat.card K * (Nat.card K ^ 2 - 1) ∣ Nat.card (adjointGroup τ K) := by
  have hinj := rankOneRep_injective (τ := τ) hK ⟨0, τ.rank_pos⟩
  have h := Subgroup.card_subgroup_dvd_card (rankOneRep τ K ⟨0, τ.rank_pos⟩).range
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    LinearFlag.card_SL_eq (n := 2) (by norm_num)] at h
  simpa using h

theorem ordProj_two_card_adjointGroup_bounds
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {τ : Tag} (hτ : 2 ≤ τ.rank) :
    (p = 2 → (p ^ f) ^ 2 ≤ ordProj[2] (Nat.card (adjointGroup τ K))) ∧
      (p ≠ 2 → 8 * ordProj[2] f ≤ ordProj[2] (Nat.card (adjointGroup τ K))) := by
  have hC0 : Nat.card (adjointGroup τ K) ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, fun hp2 => ?_⟩
  · rintro rfl
    have h := card_sq_dvd_card_adjointGroup (K := K) hτ
    rw [hK, ← pow_mul] at h
    rw [← pow_mul]
    exact pow_le_ordProj_two hC0 h
  · have : CharP K p := finite_field_prime_power_characteristic hp hf hK
    have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h := card_SL_dvd_card_adjointGroup (K := K) hchar τ
    rw [hK] at h
    have hq0 : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
    have hq1 : (p ^ f) ^ 2 - 1 ≠ 0 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have hqodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hdvd := Nat.ordProj_dvd_ordProj_of_dvd hC0 h 2
    rw [Nat.ordProj_mul 2 hq0 hq1, ordProj_two_of_odd hqodd, one_mul] at hdvd
    exact (((lie_order_two_adic_arithmetic).1 p f hp hp2 hf).2).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (by positivity)) hdvd)

theorem ordinary_exceptional_model_outer_two_part_bound
    (T : Type) [Group T] (t : StatedLieTag)
    (p f : ℕ) (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hT : ChevalleyExceptionalModel T t p f) :
    ordProj[2] (Nat.card (Outer T)) ≤ 2 * ordProj[2] f ∧ 4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) ∧
      (p = 2 → (p ^ f) ^ 2 ≤ ordProj[2] (Nat.card T)) ∧
      (p ≠ 2 → 8 * ordProj[2] f ≤ ordProj[2] (Nat.card T)) := by
  obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := hT
  have hf0 : f ≠ 0 := by omega
  have hfpos : 1 ≤ ordProj[2] f := Nat.ordProj_pos f 2
  have hf2 := ((lie_order_two_adic_arithmetic).2.2 f hf).1
  have hof : ∀ n : ℕ, (n = f ∨ n = 2 * f) → ordProj[2] n ≤ 2 * ordProj[2] f := by
    rintro n (rfl | rfl)
    · omega
    · rw [ordProj_two_two_mul hf0]
  have hfinal : ∀ o a : ℕ, o ≤ 2 * ordProj[2] f → (p = 2 → (p ^ f) ^ 2 ≤ a) →
      (p ≠ 2 → 8 * ordProj[2] f ≤ a) → o ≤ 2 * ordProj[2] f ∧ 4 ≤ a ∧ o < a ∧
        (p = 2 → (p ^ f) ^ 2 ≤ a) ∧ (p ≠ 2 → 8 * ordProj[2] f ≤ a) := by
    intro o a ho h2 hodd
    refine ⟨ho, ?_, ?_, h2, hodd⟩ <;> rcases eq_or_ne p 2 with rfl | hp2
    · have h := h2 rfl
      have : 4 ≤ (2 ^ f) ^ 2 := by
        calc 4 = (2 ^ 1) ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hf) 2
      omega
    · have h := hodd hp2
      omega
    · have h := h2 rfl
      have hlt : 2 * ordProj[2] f < (2 ^ f) ^ 2 := by
        calc 2 * ordProj[2] f < 2 * 2 ^ f := by omega
          _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 2)
          _ = (2 ^ f) ^ 2 := (sq _).symm
      omega
    · have h := hodd hp2
      omega
  have key : ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      2 ≤ τ.rank ∧ Nat.card T = Nat.card (adjointGroup τ K) ∧
      ordProj[2] (Nat.card (Outer T)) ≤ 2 * ordProj[2] f := by
    have hmodel : ∀ τ : Tag, UntwistedChevalleyModel T τ (p ^ f) → 2 ≤ τ.rank →
        (∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
          ordProj[2] (Nat.card (Outer (adjointGroup τ K))) ≤ 2 * ordProj[2] f) →
        ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
          2 ≤ τ.rank ∧ Nat.card T = Nat.card (adjointGroup τ K) ∧
          ordProj[2] (Nat.card (Outer T)) ≤ 2 * ordProj[2] f := by
      intro τ h hτ hout
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ h
      refine ⟨τ, K, inferInstance, inferInstance, hK, hτ, Nat.card_congr e.toEquiv, ?_⟩
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact hout K hK
    rcases ht with rfl | rfl | rfl | rfl | rfl
    ·
      refine hmodel .G2 hm (by decide) fun K _ _ hK => ?_
      rcases eq_or_ne p 3 with rfl | hp3
      · have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic hp hf hK
        obtain ⟨-, -, ⟨Θ, -, hs, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
        have h := card_outer_eq_of_ker_eq_inner Θ hs hker
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
        exact h ▸ hof _ (Or.inr rfl)
      · rcases eq_or_ne p 2 with rfl | hp2
        · have hf2' : 2 ≤ f := by
            by_contra hcon
            have : f = 1 := by omega
            subst this
            exact absurd hadm.2 (by norm_num)
          obtain ⟨-, Θ, -, hs, hker, -⟩ :=
            CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
              hf2' K hK
          rw [card_outer_eq_of_ker_eq_inner Θ hs hker,
            (card_ringAut_and_isCyclic Nat.prime_two K hK).1]
          exact hof _ (Or.inl rfl)
        · obtain ⟨-, Θ, -, hs, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
            hp hp2 hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
          rw [card_outer_eq_of_ker_eq_inner Θ hs hker, (card_ringAut_and_isCyclic hp K hK).1]
          exact hof _ (Or.inl rfl)
    ·
      refine hmodel .F4 hm (by decide) fun K _ _ hK => ?_
      rcases eq_or_ne p 2 with rfl | hp2
      · have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic hp hf hK
        obtain ⟨-, -, ⟨Θ, -, hs, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
        have h := card_outer_eq_of_ker_eq_inner Θ hs hker
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
        exact h ▸ hof _ (Or.inr rfl)
      · obtain ⟨-, Θ, -, hs, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
          hp hp2 hf K hK .F4 (Or.inl rfl)
        rw [card_outer_eq_of_ker_eq_inner Θ hs hker, (card_ringAut_and_isCyclic hp K hK).1]
        exact hof _ (Or.inl rfl)
    ·
      exact hmodel .E6 hm (by decide) fun K _ _ hK =>
        (ordinary_E_outer_order_Cartan_divisor .E6 (Or.inl rfl) hp hf K hK 3 2
          (Or.inl ⟨rfl, rfl, rfl⟩)).2
    ·
      exact hmodel .E7 hm (by decide) fun K _ _ hK =>
        (ordinary_E_outer_order_Cartan_divisor .E7 (Or.inr (Or.inl rfl)) hp hf K hK 2 1
          (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))).2
    ·
      exact hmodel .E8 hm (by decide) fun K _ _ hK =>
        (ordinary_E_outer_order_Cartan_divisor .E8 (Or.inr (Or.inr rfl)) hp hf K hK 1 1
          (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))).2
  obtain ⟨τ, K, _, _, hK, hτ, hcT, hout⟩ := key
  obtain ⟨h2, hodd⟩ := ordProj_two_card_adjointGroup_bounds hp hf hK hτ
  rw [hcT]
  exact hfinal _ _ hout h2 hodd

end CFSG.LieType.Chevalley
