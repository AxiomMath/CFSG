module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveTwoDDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFivePureSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFivePureTwoB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B.Pinned Subgroup
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Generic

variable {G : Type*} [Group G]

private theorem exists_involution_of_card {W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hW4 : Nat.card W = 2 ^ 4) : ∃ w ∈ W, orderOf w = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hall
    push Not at hall
    rw [(Subgroup.eq_bot_iff_forall W).2 hall, Subgroup.card_bot] at hW4
    norm_num at hW4
  exact ⟨w, hwW, orderOf_eq_prime (hW.2 w hwW) hw1⟩

private theorem le_centralizer_singleton {F W : Subgroup G} {w : G} (hw : w ∈ W)
    (hFW : F ≤ centralizer (W : Set G)) : F ≤ centralizer ({w} : Set G) :=
  hFW.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hw))

private theorem not_five_dvd_of_conj_pow {z g y : G} (hz : orderOf z = 5) {c : ℕ}
    (hcg : g * z ^ c * g⁻¹ = y) (hy : y ≠ 1) : ¬ 5 ∣ c := by
  rintro ⟨m, rfl⟩
  apply hy
  rw [← hcg, pow_mul, ← hz, pow_orderOf_eq_one, one_pow, mul_one, mul_inv_cancel]

end Generic


theorem exists_fiveA_mem_of_le_centralizer_B
    (h : BabyTwoDFiveAFact) {t : NativeSporadic.B}
    (ht : orderOf t = 2) {F : Subgroup NativeSporadic.B}
    (hFt : F ≤ centralizer ({t} : Set NativeSporadic.B)) (hF : Nat.card F = 5 ^ 2) :
    ∃ y ∈ F, Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480 := by
  obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 t ht
  obtain ⟨t₃, y₃, ht₃, hy₃, hc₃, hr₃⟩ := h
  have key : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases key k with rfl | rfl | rfl | rfl
  · obtain ⟨y, hy, -, hr⟩ := exists_fiveA_mem_of_babyInv_zero_B hk hFt hF
    exact ⟨y, hy, hr⟩
  · obtain ⟨y, hy, -, hr⟩ := exists_fiveA_mem_of_babyInv_one_B hk hFt hF
    exact ⟨y, hy, hr⟩
  · obtain ⟨y, hy, -, hr⟩ := exists_fiveA_mem_of_witness_B CFSG.Monster.Existence.babyTableIII
      (by decide) ht₃ hy₃ hr₃ hc₃ hk hFt hF
    exact ⟨y, hy, hr⟩
  · obtain ⟨y, hy, -, hr⟩ := exists_fiveA_mem_of_babyInv_three_B hk hFt hF
    exact ⟨y, hy, hr⟩

theorem babyFiveBPureFact_of_twoDFiveA
    (h : BabyTwoDFiveAFact) : BabyFiveBPureFact := by
  intro F _ _ _ hF hpure W hW hW4 hFW
  obtain ⟨w, hwW, hw⟩ := exists_involution_of_card hW hW4
  obtain ⟨y, hyF, hr⟩ :=
    exists_fiveA_mem_of_le_centralizer_B h hw (le_centralizer_singleton hwW hFW) hF
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, sub_self, Matrix.rank_zero] at hr
    norm_num at hr
  obtain ⟨c, g, hcg⟩ := hpure y hyF hy1
  have hc := not_five_dvd_of_conj_pow (G := NativeSporadic.B) orderOf_zFive hcg hy1
  have hrz := rank_bMat_conj g (zFive ^ c)
  rw [hcg, rank_bMat_pow orderOf_zFive hc, bFiveAK_parts.2.2, hr] at hrz
  norm_num at hrz

end CFSG.LocalAnalysis.GLTheoremA.H1017
