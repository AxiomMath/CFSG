module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwDefs
import CFSG.RankThree.PartOne.KLC.EigTwE6
import CFSG.RankThree.PartOne.KE.CTTwistedEight
import CFSG.RankThree.PartOne.KE.CTTwistedTwelve
import CFSG.RankThree.PartOne.KE.CTTwistedEighteen
import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Ten
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors small_prime_geom_sum_guard
  exists_mem_row_of_dvd_pow_sub_one exists_dvd_exhaustionPhi_of_dvd_prod
  plus_factors_eq_prod_exhaustionPhi)

open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)

open CFSG.RankThree.PartOne.KE.CTCyclo (key_data cycloIdx)


theorem twE6_zmod7_phi10_ne : ∀ x : ZMod 7, x ^ 4 - x ^ 3 + x ^ 2 - x + 1 ≠ 0 := by
  decide

theorem twE6_p_eq_five_or_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : ¬ 7 < p) :
    p = 5 ∨ p = 7 := by
  have : p ≤ 7 := by omega
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num) | simp

theorem twE6_phi10_small {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : ¬ 7 < p)
    (hpq : ¬ p ∣ q) (h : (p : ℤ) ∣ (exhaustionPhi 10).eval (q : ℤ)) :
    (p : ℤ) ∣ (exhaustionPhi 2).eval (q : ℤ) := by
  rcases twE6_p_eq_five_or_seven hp hp5 hp7 with rfl | rfl
  · have hsum_eq : ∑ j ∈ Finset.range 5, (-1 * (q : ℤ)) ^ j = (exhaustionPhi 10).eval (q : ℤ) := by
      simp only [exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, zero_add]
      ring
    have hsum : ((5 : ℕ) : ℤ) ∣ ∑ j ∈ Finset.range 5, (-1 * (q : ℤ)) ^ j := by
      rw [hsum_eq]
      exact h
    obtain ⟨-, hq⟩ := small_prime_geom_sum_guard hp (by norm_num)
      (fun h' => hpq (Int.natCast_dvd_natCast.1 h')) (r := 5) (Or.inl rfl) (δ := -1)
      (Or.inr rfl) hsum le_rfl
    simpa [exhaustionPhi] using (Int.ModEq.dvd hq.symm)
  · exfalso
    have hz : (((exhaustionPhi 10).eval (q : ℤ) : ℤ) : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).2 h
    simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Int.cast_add, Int.cast_sub, Int.cast_pow,
      Int.cast_one] at hz
    exact twE6_zmod7_phi10_ne _ hz

theorem exists_mem_row_twE6 {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (h : p ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)) :
    ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => hpq (by rw [h0]; exact dvd_zero p)
  have hminus : ∀ d ∈ ([12, 8, 6, 2] : List ℕ), p ∣ q ^ d - 1 →
      ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) :=
    fun d hd hpd => exists_mem_row_of_dvd_pow_sub_one hp hq1 (D := [12, 8, 6, 2]) (by decide)
      (by decide) ⟨d, hd, hpd⟩
  have hplus : ∀ M : List ℕ, (∀ m ∈ M, m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ)) →
      ∀ n : ℕ, (n : ℤ) = (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod → p ∣ n →
      ∃ m ∈ ({1, 2, 3, 4, 6, 8, 10, 12, 18} : Finset ℕ), (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) :=
    fun M hM n hn hpn => by
      have h1 : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod := by
        rw [← hn]
        exact Int.natCast_dvd_natCast.mpr hpn
      obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
      exact ⟨m, hM m hm, hpm⟩
  obtain ⟨h9, h5, -⟩ := plus_factors_eq_prod_exhaustionPhi (q : ℤ)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · exact absurd (hp.dvd_of_dvd_pow h) hpq
            · exact hminus 12 (by decide) h
          · exact hplus [2, 6, 18] (by decide) _ (by push_cast; exact h9) h
        · exact hminus 8 (by decide) h
      · exact hminus 6 (by decide) h
    · exact hplus [2, 10] (by decide) _ (by push_cast; exact h5) h
  · exact hminus 2 (by decide) h

section


theorem card_graphFixedRootGroup_E6_dvd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∣
      (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨-, -, hder, -, -, hRcard, -⟩ := twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ
    hσ Ω (iterateFrobenius Ω ℓ f) (fun c => iterateFrobenius_def ℓ f c)
  have hle : (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) ≤
      twistedFixedGroup TwistTag.E6 Ω (iterateFrobenius Ω ℓ f) := by
    rw [← hder]
    exact Subgroup.commutator_le_self _
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (baseChangeGL_injective _), hRcard] at hdvd
  exact hdvd

theorem twE6CrossRankStep : TwE6CrossRankStep := by
  intro ℓ d p hℓ hd hp hp5 hne K k _ _ _ _ σ σ₀ hK hk hσ hσ₀ hrk
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  haveI : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  haveI : Finite (graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom) := Subtype.finite
  have hf : 1 ≤ p * d := Nat.mul_le_mul hp.one_lt.le hd
  have hpq : ¬ p ∣ ℓ ^ (p * d) := OFRC.not_dvd_pow_of_ne hp hℓ hne
  have hcong : ((ℓ ^ (p * d) : ℕ) : ZMod p) = ((ℓ ^ d : ℕ) : ZMod p) := by
    rw [pow_mul']
    exact OFRC.natCast_pow_prime _
  have hdvd : p ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    obtain ⟨E, -, -, hcardE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    have h0 : CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        ≠ 0 := by
      omega
    exact (hcardE ▸ dvd_pow_self p h0).trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨m, hm, hpm⟩ := exists_mem_row_twE6 hp hpq
    (hdvd.trans (card_graphFixedRootGroup_E6_dvd hℓ hf K hK σ hσ))
  have hlow : ∀ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) →
      (p : ℤ) ∣ (exhaustionPhi e).eval ((ℓ ^ (p * d) : ℕ) : ℤ) →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom)) := by
    intro e he h
    have h' := (dvd_eval_iff_of_natCast_eq (exhaustionPhi e) hcong).1 h
    have := CFSG.RankThree.PartOne.KLC.two_le_pRank_twistedE6_of_sector hℓ hd k hk σ₀ hσ₀ hp hp5
      hne.symm he h'
    rwa [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank] at this
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 18 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlow 1 (by simp) hpm
  · exact hlow 2 (by simp) hpm
  · exact hlow 3 (by simp) hpm
  · exact hlow 4 (by simp) hpm
  · exact hlow 6 (by simp) hpm
  ·
    obtain ⟨-, -, kk, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.twisted_E6_eight_cyclic_sylow hℓ hf K hK σ hσ hp (by omega) hpm
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        ≤ 1 :=
      pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    by_cases hp7 : 7 < p
    · have he := (key_data hp hp7 (by simp [cycloIdx]) hpm).1
      have h1 : CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
          ≤ 1 :=
        CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum
          (CFSG.LieType.SeitzGeneration.sylowTorus_twistedE6_ten hℓ hf K hK σ hσ hp he) hp
      omega
    · exact hlow 2 (by simp) (twE6_phi10_small hp hp5 hp7 hpq hpm)
  ·
    obtain ⟨-, -, kk, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.twisted_E6_twelve_cyclic_sylow hℓ hf K hK σ hσ hp (by omega) hpm
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        ≤ 1 :=
      pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega
  ·
    obtain ⟨-, -, kk, T, -, -, -, -, hcyc, -⟩ :=
      CFSG.RankThree.PartOne.KE.twisted_E6_eighteen_cyclic_sylow hℓ hf K hK σ hσ hp (by omega) hpm
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        ≤ 1 :=
      pRank_le_one_of_cyclic_p_subgroups hp hcyc
    omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
