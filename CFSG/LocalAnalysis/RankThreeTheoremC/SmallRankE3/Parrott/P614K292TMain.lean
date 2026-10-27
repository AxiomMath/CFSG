module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292TBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292 P614K292T
open scoped Matrix

theorem kD292TwoFrame3_holds : KD292TwoFrame3 := by
  intro π p f K _ y hK hq _ hT R hRsl hR2 hRne hRgen hyR
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨ℓ, hY3, hℓ⟩ := hT.not_cube hK hq
  have hcent : ∀ g : GL (Fin 3) K, y ^ 3 * g = g * y ^ 3 := fun g => Units.ext (by
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hY3, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have hyR' : ∀ r ∈ R, y⁻¹ * r * y ∈ R := by
    intro r hr
    have h1 : y⁻¹ * r * y = y * (y * r * y⁻¹) * y⁻¹ := by
      calc y⁻¹ * r * y = y⁻¹ * (r * y ^ 3) * (y ^ 2)⁻¹ := by group
        _ = y⁻¹ * (y ^ 3 * r) * (y ^ 2)⁻¹ := by rw [hcent r]
        _ = y ^ 2 * r * (y ^ 2)⁻¹ := by group
        _ = y * (y * r * y⁻¹) * y⁻¹ := by rw [sq, mul_inv_rev]; simp only [mul_assoc]
    rw [h1]
    exact hyR _ (hyR r hr)
  obtain ⟨v, hv0, hv⟩ := exists_fixed_line hR2
  have hli : LinearIndependent K (yFrame y v) := by
    rw [yFrame_eq]
    exact linearIndependent_cyclic hℓ hY3 hv0
  have hpow : ∀ n : ℕ, ∀ r ∈ R, ∃ c : K, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((y : Matrix (Fin 3) (Fin 3) K) ^ n *ᵥ v) = c • ((y : Matrix (Fin 3) (Fin 3) K) ^ n *ᵥ v)
        := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa only [pow_succ', ← Matrix.mulVec_mulVec] using eig_mulVec hyR' ih
  have heig : ∀ r ∈ R, ∀ i, ∃ c : K,
      (r : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i = c • yFrame y v i := fun r hr i =>
    hpow i r hr
  have hle : R ≤ twoFrame y v := by
    refine hRgen.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro r ⟨hr, hr2⟩
    show r ∈ twoFrame y v
    refine mem_frameGroupOf.2 ⟨((mem_slPi_iff hπ).1 (hRsl hr)).2, fun i => ?_⟩
    obtain ⟨c, hc⟩ := heig r hr i
    refine ⟨c, ?_, hc⟩
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i)
      hr2
    simp only [pow_two, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, smul_smul,
      Units.val_one, Matrix.one_mulVec] at h
    have h' : (c ^ 2 - 1) • yFrame y v i = 0 := by rw [sub_smul, one_smul, pow_two, h, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right (hli.ne_zero i))
  have h2 : (2 : K) ≠ 0 := by
    intro h20
    apply hRne
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨-, hrE⟩ := mem_frameGroupOf.1 (hle hr)
    choose c hc2 hc using hrE
    have hc1 : ∀ i, c i = 1 := fun i => by
      have h : (c i - 1) ^ 2 = 0 := by linear_combination hc2 i + (1 - c i) * h20
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
    exact Subgroup.mem_bot.2 (eq_of_eig hli hc fun i => by
      rw [hc1, Units.val_one, Matrix.one_mulVec, one_smul])
  obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨hrdet, hrE⟩ := mem_frameGroupOf.1 (hle hrR)
  choose c hc2 hc using hrE
  have hd : ∀ k, ∃ d ∈ R, ∀ i, (d : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i =
      (sgnAt k i : K) • yFrame y v i := by
    rcases eig_cases h2 hc2 ((det_eq_of_eig hli hc).symm.trans hrdet) with hc1 | ⟨k₀, rfl⟩
    · exact absurd (eq_of_eig hli hc fun i => by
        rw [hc1, Units.val_one, Matrix.one_mulVec, one_smul]) hr1'
    have hstep : ∀ k, (∃ d ∈ R, ∀ i, (d : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i =
        (sgnAt k i : K) • yFrame y v i) → ∃ d ∈ R, ∀ i,
          (d : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v i =
            (sgnAt (k + 1) i : K) • yFrame y v i := by
      rintro k ⟨d, hdR, hdk⟩
      refine ⟨y * d * y⁻¹, hyR d hdR, ?_⟩
      rw [← sgnAt_rot]
      exact conj_eig ℓ.ne_zero hY3 hdk
    have hk : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 1 + 1 := by decide
    intro k
    rcases hk k k₀ with rfl | rfl | rfl
    · exact ⟨r, hrR, hc⟩
    · exact hstep _ ⟨r, hrR, hc⟩
    · exact hstep _ (hstep _ ⟨r, hrR, hc⟩)
  refine ⟨h2, v, hv0, le_antisymm hle fun g hg => ?_, fun hπf i j hij => ?_⟩
  ·
    obtain ⟨hgdet, hgE⟩ := mem_frameGroupOf.1 hg
    choose e he2 he using hgE
    rcases eig_cases h2 he2 ((det_eq_of_eig hli he).symm.trans hgdet) with he1 | ⟨k, rfl⟩
    · rw [eq_of_eig hli he fun i => by rw [he1, Units.val_one, Matrix.one_mulVec, one_smul]]
      exact one_mem R
    · obtain ⟨d, hdR, hdk⟩ := hd k
      rw [eq_of_eig hli he hdk]
      exact hdR
  ·
    subst hπf
    have hU := hK.unitary
    obtain ⟨d, hdR, hdi⟩ := hd i
    have key := herm_mulVec hU ((mem_slPi_false hU).1 (hRsl hdR)).2 (yFrame y v i)
      (yFrame y v j)
    rw [hdi i, hdi j] at key
    have hii : sgnAt i i = (1 : K) := if_pos rfl
    have hij' : sgnAt i j = (-1 : K) := if_neg (Ne.symm hij)
    rw [hii, hij'] at key
    simp only [one_smul, neg_smul, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at key
    have h2S : (2 : K) * ∑ k, yFrame y v i k ^ p ^ f * yFrame y v j k = 0 := by
      linear_combination -key
    exact (mul_eq_zero.1 h2S).resolve_left h2

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
