module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatAlt
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeA7
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.GenAlt

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

theorem center_of_alt_three (hPC : GL83.I243.PCoverList) {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hOp : CFSG.pPrimeCore 3 K = ⊥) {n : ℕ} (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Subgroup.center K = ⊥ ∨ ((n = 6 ∨ n = 7) ∧ Nat.card (Subgroup.center K) = 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center K) inferInstance inferInstance hOp
  by_cases hZ : Subgroup.center K = ⊥
  · exact Or.inl hZ
  right
  have hdvd : 3 ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  rcases hPC K (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq) 3 Nat.prime_three (by norm_num)
    hdvd (.alternating n hn) ⟨e⟩ with ⟨d, hd, -⟩ | ⟨-, hcov | ⟨hsmall, h9⟩⟩
  · cases hd
  · exfalso
    rcases hcov with h | h | h | h | h | h | ⟨q, hv, -, h⟩ | ⟨q, hv, -, h⟩ | ⟨q, hv, -, h⟩ <;>
      cases h
  · refine ⟨?_, ?_⟩
    · rcases hsmall with ⟨⟨m, hm, hm67, him⟩ | h⟩ | ⟨d, hd, -⟩
      · cases him
        exact hm67
      · cases h
      · cases hd
    · obtain ⟨k, hk⟩ := hZp.exists_card_eq
      rw [hk] at hdvd h9 ⊢
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · norm_num at hdvd
        · exact h
      have hk2 : k < 2 := by
        by_contra h
        exact h9 (pow_dvd_pow 3 (by omega))
      obtain rfl : k = 1 := by omega
      norm_num

theorem kGroupLowRank24_12_three_of_alt (hPC : GL83.I243.PCoverList) {X : Type} [Group X]
    [Finite X] {K E : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K) (hOp : CFSG.pPrimeCore 3 ↥K = ⊥)
    (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 3 E K) {n : ℕ} (hn : 5 ≤ n)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) :
    KGroupLowRank24_12 3 ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect ↥K := hKq.1
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have h3ge : n / 3 ≤ 3 := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.le_pRank_top hn e hp3 (by norm_num)
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 K :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K).symm
    have h3 : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 (K ⊔ E) :=
      CFSG.SectionRank.pRank_mono hp3.one_lt le_sup_left
    omega
  have hn11 : n ≤ 11 := by omega
  have hiso : Subgroup.center ↥K = ⊥ → Nonempty (↥K ≃* alternatingGroup (Fin n)) := fun hZ =>
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩
  have hZ := center_of_alt_three hPC hKq hOp hn e
  have hgen : n ≠ 6 → n % 3 ≠ 0 → n ≤ 8 → False := by
    intro hn6 hn3 hn8
    have hEN : E ≤ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
      exact le_top
    have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
      rcases hZ with hZ | ⟨-, hZ⟩
      · rw [hZ, Subgroup.card_bot]
        exact odd_one
      · rw [hZ]
        decide
    have hEp : IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hE
    have hR : IsPGroup 3 (GL83.PiGen.permHom hEN hn hn6 e).range :=
      hEp.of_surjective (GL83.PiGen.permHom hEN hn hn6 e).rangeRestrict
        (GL83.PiGen.permHom hEN hn hn6 e).rangeRestrict_surjective
    have hY2 : alternatingGroup (Fin n) ≤
        Subgroup.closure (GL83.PiGen.Y2 3 (GL83.PiGen.permHom hEN hn hn6 e).range) := by
      rcases (show n = 5 ∨ n = 7 ∨ n = 8 by omega) with rfl | rfl | rfl
      · have horb : ∀ ω : Fin 5,
            Nat.card (MulAction.orbit (GL83.PiGen.permHom hEN hn hn6 e).range ω) ≤ 3 := fun ω =>
          card_orbit_le_of_lt_sq hp3 (by norm_num) (hEc ▸ Subgroup.card_range_dvd _) ω
        exact GL83.PiGen.alternatingGroup_le_closure_Y2 le_rfl hR (by simp) (by simp) horb
      · exact GL83.PiGen.alternatingGroup_le_closure_Y2_three_seven hR (by simp)
      · have horb : ∀ ω : Fin 8,
            Nat.card (MulAction.orbit (GL83.PiGen.permHom hEN hn hn6 e).range ω) ≤ 3 := fun ω =>
          card_orbit_le_of_lt_sq hp3 (by norm_num) (hEc ▸ Subgroup.card_range_dvd _) ω
        exact GL83.PiGen.alternatingGroup_le_closure_Y2 le_rfl hR (by simp) (by simp) horb
    exact hΓ ((GL83.PiGen.le_centGenI_of_perm hEN hodd hn hn6 e hY2).trans
      (centGenI_le_gammaOver hp3 hE hEc))
  refine ⟨hp3, by norm_num, hKq, hKcat, ?_⟩
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hgen (by norm_num) (by norm_num) (by norm_num)).elim
  · rcases hZ with hZ | ⟨-, hZ3⟩
    · exact Or.inl (Or.inl (hiso hZ))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hZ3, ⟨e⟩⟩))))))))))))⟩))
  · exact (hgen (by norm_num) (by norm_num) (by norm_num)).elim
  · exact (hgen (by norm_num) (by norm_num) (by norm_num)).elim
  · rcases hZ with hZ | ⟨h, -⟩
    · exact Or.inl (Or.inr (Or.inl (hiso hZ)))
    · omega
  · rcases hZ with hZ | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (hiso hZ))))))⟩))
    · omega
  · rcases hZ with hZ | ⟨h, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (hiso hZ)))))))⟩))
    · omega

end CFSG.LocalAnalysis.AGL81I.Section3
