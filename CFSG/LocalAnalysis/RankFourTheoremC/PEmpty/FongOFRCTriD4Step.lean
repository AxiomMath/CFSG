module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwDefs
import CFSG.RankThree.PartOne.KLC.TriTorus
import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors
  pow_sub_one_eq_prod_exhaustionPhi exists_dvd_exhaustionPhi_of_dvd_prod
  plus_factors_eq_prod_exhaustionPhi)


theorem dvd_twelve_nat {p x : ℕ} (hx : 1 ≤ x)
    (h : (p : ℤ) ∣ (exhaustionPhi 12).eval (x : ℤ)) : p ∣ x ^ 4 - x ^ 2 + 1 := by
  have hle : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right hx (by norm_num)
  have e : (exhaustionPhi 12).eval (x : ℤ) = ((x ^ 4 - x ^ 2 + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
    simp [exhaustionPhi] <;> ring
  rw [e] at h
  exact Int.natCast_dvd_natCast.1 h

theorem exists_mem_row_triD4 {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (hq1 : 1 ≤ q)
    (h : p ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) :
    ∃ m ∈ ({1, 2, 3, 6, 12} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
  have hrow : ∀ M : List ℕ, (∀ m ∈ M, m ∈ ({1, 2, 3, 6, 12} : Finset ℕ)) →
      ∀ n : ℕ, (n : ℤ) = (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod → p ∣ n →
      ∃ m ∈ ({1, 2, 3, 6, 12} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) :=
    fun M hM n hn hpn => by
      have h1 : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod := by
        rw [← hn]
        exact Int.natCast_dvd_natCast.mpr hpn
      obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
      exact ⟨m, hM m hm, hpm⟩
  have hcast : ∀ d, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow, Nat.cast_one]
  obtain ⟨-, -, h8⟩ := plus_factors_eq_prod_exhaustionPhi (q : ℤ)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpq
      · exact hrow (exhaustionMinusFactors 2) (by decide) _
          (by rw [hcast]; exact pow_sub_one_eq_prod_exhaustionPhi _ (by decide)) h
    · exact hrow (exhaustionMinusFactors 6) (by decide) _
        (by rw [hcast]; exact pow_sub_one_eq_prod_exhaustionPhi _ (by decide)) h
  · exact hrow [3, 6, 12] (by decide) _ (by push_cast; exact h8) h

section


theorem pRank_top_graphFixedRootGroup_D4_orient {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hp : p.Prime) (k : Type) [Field k] [Finite k] (hk : Nat.card k = (ℓ ^ d) ^ 3)
    (σ₀ : k ≃+* k)
    (hσ₀ : (∀ c, σ₀ c = c ^ ℓ ^ d) ∨ (∀ c, σ₀ c = c ^ (ℓ ^ d) ^ 2)) :
    ∃ σ₁ : k ≃+* k, (∀ c, σ₁ c = c ^ ℓ ^ d) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom)) =
        CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 k σ₁.toRingHom)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * d) (by rw [hk, ← pow_mul, mul_comm] : Nat.card k = ℓ ^ (3 * d))
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : k ≃+* k, ∀ c, σ₁ c = c ^ ℓ ^ d :=
    ⟨fr ^ d, fun c => ringAut_pow_apply_of_frobenius hfr d c⟩
  refine ⟨σ₁, hσ₁, ?_⟩
  haveI : Finite (ModGL TwistTag.D4.tag k) := finite_modGL
  rcases hσ₀ with h | h
  · have hσe : σ₀ = σ₁ := RingEquiv.ext fun c => by rw [h, hσ₁]
    subst hσe
    rfl
  · obtain ⟨e⟩ := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4
      k hk σ₀ σ₁ h hσ₁
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e

theorem triD4CrossRankStep (h1 : TriPhi1Rank) : TriD4CrossRankStep := by
  intro ℓ d p hℓ hd hp hp5 hne K k _ _ _ _ σ σ₀ hK hk hσ hσ₀ hrk
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hp1 : 1 < p := hp.one_lt
  have hpd1 : 1 ≤ p * d := by nlinarith [hp.two_le]
  have hpK : ¬ p ∣ ℓ ^ (p * d) := OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hq1 : 1 ≤ ℓ ^ (p * d) := Nat.one_le_pow _ _ hℓ.pos
  have hcong : ((ℓ ^ (p * d) : ℕ) : ZMod p) = ((ℓ ^ d : ℕ) : ZMod p) := by
    rw [pow_mul', OFRC.natCast_pow_prime]
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hdvd : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    obtain ⟨E, -, -, hcardE⟩ := CFSG.SectionRank.exists_pRank hp1
      (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    have h0 : CFSG.Open.pRank p
        (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ 0 := by
      omega
    exact (hcardE ▸ dvd_pow_self p h0).trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨hC, -⟩ := CFSG.LieType.Chevalley.triality_both_orientations_exact_finite_order ℓ (p * d)
    hℓ hpd1 K hK 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  rw [hC] at hdvd
  obtain ⟨m, hm, hpm⟩ := exists_mem_row_triD4 hp hpK hq1 hdvd
  obtain ⟨σ₁, hσ₁, hpeq⟩ := pRank_top_graphFixedRootGroup_D4_orient hℓ hd hp k hk σ₀ hσ₀
  rw [hpeq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  ·
    have hdiv : (p : ℤ) ∣ ((ℓ ^ d : ℕ) : ℤ) - 1 := by
      have e : ((ℓ ^ d : ℕ) : ℤ) - 1 = (exhaustionPhi 1).eval ((ℓ ^ d : ℕ) : ℤ) := by
        simp [exhaustionPhi]
      rw [e]
      exact (dvd_eval_iff_of_natCast_eq (exhaustionPhi 1) hcong).1 hpm
    have := h1 hd hk σ₁ hσ₁ hp hp5 hdiv
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  ·
    have hdiv : (p : ℤ) ∣ ((ℓ ^ d : ℕ) : ℤ) + 1 := by
      have e : ((ℓ ^ d : ℕ) : ℤ) + 1 = (exhaustionPhi 2).eval ((ℓ ^ d : ℕ) : ℤ) := by
        simp [exhaustionPhi]
      rw [e]
      exact (dvd_eval_iff_of_natCast_eq (exhaustionPhi 2) hcong).1 hpm
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi2 hd hk σ₁ hσ₁ hp (by omega) hdiv
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  ·
    have hdiv : (p : ℤ) ∣ ((ℓ ^ d : ℕ) : ℤ) ^ 2 + (1 : ℤ) * ((ℓ ^ d : ℕ) : ℤ) + 1 := by
      have e : ((ℓ ^ d : ℕ) : ℤ) ^ 2 + (1 : ℤ) * ((ℓ ^ d : ℕ) : ℤ) + 1 =
          (exhaustionPhi 3).eval ((ℓ ^ d : ℕ) : ℤ) := by
        simp [exhaustionPhi] <;> ring
      rw [e]
      exact (dvd_eval_iff_of_natCast_eq (exhaustionPhi 3) hcong).1 hpm
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 hd hk σ₁ hσ₁
      (ε := 1) (Or.inl rfl) hp hdiv
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  ·
    have hdiv : (p : ℤ) ∣ ((ℓ ^ d : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * ((ℓ ^ d : ℕ) : ℤ) + 1 := by
      have e : ((ℓ ^ d : ℕ) : ℤ) ^ 2 + (-1 : ℤ) * ((ℓ ^ d : ℕ) : ℤ) + 1 =
          (exhaustionPhi 6).eval ((ℓ ^ d : ℕ) : ℤ) := by
        simp [exhaustionPhi] <;> ring
      rw [e]
      exact (dvd_eval_iff_of_natCast_eq (exhaustionPhi 6) hcong).1 hpm
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 hd hk σ₁ hσ₁
      (ε := -1) (Or.inr rfl) hp hdiv
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  ·
    exfalso
    have hfin := dvd_twelve_nat hq1 hpm
    obtain ⟨T, -, -, hall⟩ :=
      CFSG.RankThree.Chevalley.triality_cyclotomic_twelve_torus_and_prime_centralizers hℓ hpd1 K
        hK σ hσ
    obtain ⟨-, hcyc, -⟩ := hall p hp (by omega) hfin
    have := pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
