module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.G2Moves
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.G2Weyl
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.JunkKill

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

private theorem mulAut_conj_chain {G : Type*} [Group G] (a b x : MulAut G) :
    a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  simp only [mul_assoc, mul_inv_rev]


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exists_conj_to_top_of_longForm {s r r' : K} (hs : σ s = s) (hr : σ r = r) (hr' : σ r' = r')
    (hne : ¬ (s = 0 ∧ r = 0 ∧ r' = 0)) :
    ∃ (ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (c : K) (hc : σ c = c), c ≠ 0 ∧
      ε * (MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs *
          longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
          fieldActor (t := TwistTag.D4) σ σ) * ε⁻¹ =
        MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
          fieldActor (t := TwistTag.D4) σ σ := by
  have hsign : ∀ e : K, (e = 1 ∨ e = -1) → σ e = e := by
    rintro e (rfl | rfl) <;> simp
  have hsign0 : ∀ e : K, (e = 1 ∨ e = -1) → e ≠ 0 := by
    rintro e (rfl | rfl)
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  by_cases hs0 : s = 0
  · subst hs0
    by_cases hr0 : r = 0
    ·
      subst hr0
      have hr'0 : r' ≠ 0 := fun h => hne ⟨rfl, rfl, h⟩
      refine ⟨1, r', hr', hr'0, ?_⟩
      rw [longElt_zero hf hK σ hσ (Or.inl rfl) hs,
        longElt_zero hf hK σ hσ (Or.inr (Or.inl rfl)) hr]
      simp only [one_mul, mul_one, inv_one]
    ·
      obtain ⟨j, hj, hjC⟩ := exists_conj_kill_D_of_C hf hK σ hσ hr hr' hr0
      obtain ⟨n, e, hn, he, hnC⟩ := exists_weyl_rootC_to_rootD hf hK σ hσ
      have hc : σ (e * r) = e * r := by rw [map_mul, hsign e he, hr]
      have hc0 : e * r ≠ 0 := mul_ne_zero (hsign0 e he) hr0
      have hY : longElt hf hK σ hσ (Or.inl rfl) 0 hs *
          longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' =
          longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' := by
        rw [longElt_zero hf hK σ hσ (Or.inl rfl) hs, one_mul]
      have hnC' : n * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr * n⁻¹ =
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) (e * r) hc := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_longElt]
        exact hnC r
      have H1 : MulAut.conj j * (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
          fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj j)⁻¹ =
          MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr) *
            fieldActor (t := TwistTag.D4) σ σ := by
        rw [conj_mul_fieldActor_of_fixed hf hK σ hσ j _ hj, hjC]
      have H2 : MulAut.conj n * (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr) *
          fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj n)⁻¹ =
          MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) (e * r) hc) *
            fieldActor (t := TwistTag.D4) σ σ := by
        rw [conj_mul_fieldActor_of_fixed hf hK σ hσ n _ hn, hnC']
      refine ⟨MulAut.conj n * MulAut.conj j, e * r, hc, hc0, ?_⟩
      rw [hY, mulAut_conj_chain, H1, H2]
  ·
    obtain ⟨w, r'', hr'', hw⟩ :=
      exists_twistedConj_kill_C hf hK σ hσ hs hr hr' hs0 (map_zero σ)
    obtain ⟨j, hj, hjB⟩ := exists_conj_kill_D_of_B hf hK σ hσ hs hr'' hs0
    obtain ⟨n, e, hn, he, hnB⟩ := exists_weyl_rootB_to_rootD hf hK σ hσ
    have hc : σ (e * s) = e * s := by rw [map_mul, hsign e he, hs]
    have hc0 : e * s ≠ 0 := mul_ne_zero (hsign0 e he) hs0
    have H0 : MulAut.conj w⁻¹ * (MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs *
        longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
        fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj w⁻¹)⁻¹ =
        MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'') *
          fieldActor (t := TwistTag.D4) σ σ := by
      rw [conj_mul_twisted hf hK σ hσ (fieldActor (t := TwistTag.D4) σ σ) _ w, hw,
        longElt_zero hf hK σ hσ (Or.inr (Or.inl rfl)) (map_zero σ), mul_one]
    have H1 : MulAut.conj j * (MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'') *
        fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj j)⁻¹ =
        MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs) *
          fieldActor (t := TwistTag.D4) σ σ := by
      rw [conj_mul_fieldActor_of_fixed hf hK σ hσ j _ hj, hjB]
    have hnB' : n * longElt hf hK σ hσ (Or.inl rfl) s hs * n⁻¹ =
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) (e * s) hc := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_longElt]
      exact hnB s
    have H2 : MulAut.conj n * (MulAut.conj (longElt hf hK σ hσ (Or.inl rfl) s hs) *
        fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj n)⁻¹ =
        MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) (e * s) hc) *
          fieldActor (t := TwistTag.D4) σ σ := by
      rw [conj_mul_fieldActor_of_fixed hf hK σ hσ n _ hn, hnB']
    refine ⟨MulAut.conj n * MulAut.conj j * MulAut.conj w⁻¹, e * s, hc, hc0, ?_⟩
    rw [mulAut_conj_chain, mulAut_conj_chain, H0, H1, H2]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
