module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSplitMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QNsqMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QL2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Assembly.LowTwoRank CatalogueBProjectiveInvolution
  CatalogueBProjectiveCoordinates

theorem two_ne_zero_of_odd_natCard {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have hchar : ringChar K = 2 := by
    have hdvd : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h2)
    obtain ⟨n, hn, -⟩ := FiniteField.card K (ringChar K)
    exact (Nat.prime_dvd_prime_iff_eq hn Nat.prime_two).mp hdvd
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [hchar] at hn
  rw [Nat.card_eq_fintype_card, hn] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' n.ne_zero).mpr even_two)

theorem fAt_psl_of_three_le {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e₀ : X ≃* ProjectiveSpecialLinearGroup (Fin n) K) {z : X} (hz : orderOf z = 2) :
    FAt X z := by
  have htwo := two_ne_zero_of_odd_natCard hodd
  have hπ := pslCover_surjective e₀
  have hker := pslCover_eq_one_iff e₀
  obtain ⟨a, rfl⟩ := hπ z
  set π := pslCover e₀
  set A := Matrix.SpecialLinearGroup.toGL a with hAdef
  have ha : a ∉ center (Matrix.SpecialLinearGroup (Fin n) K) := fun h => by
    rw [(hker a).mpr h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have ha2 : a ^ 2 ∈ center (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [← hker, map_pow, ← hz, pow_orderOf_eq_one]
  obtain ⟨c, hc, hca⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ha2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by simp; omega)] at hc
    exact zero_ne_one hc
  set lam := Units.mk0 c hc0
  have hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lam := by
    apply Units.ext
    rw [hAdef, ← map_pow, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← hca]
    rfl
  have hnonscalar : ∀ c' : K, splitMatrixOperator A ≠ c' • (1 : Module.End K (Fin n → K)) :=
    fun c' h => ha (mem_center_of_mulVec_eq_smul (c := c') fun v => by
      have := congrArg (fun T : Module.End K (Fin n → K) => T v) h
      exact this)
  by_cases hsqr : IsSquare lam.val
  · obtain ⟨b, hb⟩ := exists_unit_square_root lam hsqr
    have hsq' : A ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2) := by rw [hb]; exact hsq
    obtain ⟨hr, hs⟩ := splitMatrixDimension_pos A b htwo hsq' hnonscalar
    have hsum := splitMatrixDimension_sum A b htwo hsq'
    rw [Fintype.card_fin] at hsum
    by_cases hs2 : 2 ≤ negativeMatrixDimension A b.val
    · obtain ⟨h1, h2⟩ := evenCent_split htwo h4 π hπ hker a b hsq' hr hs2
      exact fAt_of_evenCent h1 h2
    · have hb' : A ^ 2 = GeneralLinearGroup.scalar (Fin n) ((-b) ^ 2) := by
        rw [neg_sq]
        exact hsq'
      have hr' : 1 ≤ positiveMatrixDimension A (-b).val := by
        change 1 ≤ Module.finrank K ((splitMatrixOperator A).eigenspace ((-b : Kˣ) : K))
        rw [Units.val_neg]
        exact hs
      have hs' : 2 ≤ negativeMatrixDimension A (-b).val := by
        change 2 ≤ Module.finrank K ((splitMatrixOperator A).eigenspace (-((-b : Kˣ) : K)))
        rw [Units.val_neg, neg_neg]
        change 2 ≤ positiveMatrixDimension A b.val
        omega
      obtain ⟨h1, h2⟩ := evenCent_split htwo h4 π hπ hker a (-b) hb' hr' hs'
      exact fAt_of_evenCent h1 h2
  · obtain ⟨h1, h2⟩ := evenCent_nonsq htwo hodd π hπ hker a lam hsqr hsq hn
    exact fAt_of_evenCent h1 h2

theorem famF_psl : FamF .PSL := by
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  have hadm : StatedLieAdmissible .PSL n p f := by
    rcases hX with ⟨-, h⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
    · exact h.1
    all_goals exact absurd hc (by decide)
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hX
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card K) := hK ▸ hpodd.pow
  have h5 : 5 ≤ p ^ f := by
    have h3 : 3 ≤ p ^ f := (show 3 ≤ p by have := hp.two_le; omega).trans
      (Nat.le_self_pow (by omega) p)
    obtain ⟨t, ht⟩ : Odd (p ^ f) := hpodd.pow
    omega
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have : Fact p.Prime := ⟨hp⟩
    exact fAt_psl_two hK hpodd (by omega) h5 e₀ hz
  · exact fAt_psl_of_three_le hodd (by omega) hn3 e₀ hz

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
