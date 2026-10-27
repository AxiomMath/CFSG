module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem stmtOneLieBlocksFive :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
      {M H R Np Z : Subgroup G}, StmtLemmaBRelCyc → StmtBlockThree → Asc81bEightFive →
      D1NoXBlock → D1OneLieMData p n e P M H R Np Z → 5 ≤ p →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  intro G _ _ p _ n e P M H R Np Z hLB hB3 h85 hD2 h hp5 L hL
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hZK : Z ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
  have hnS := h.ph3.not_isSylowTwoOf_inf h85 hD2 hL
  have hpL : ∀ A : Subgroup G, A ≤ H ⊓ M → (∀ a ∈ A, a ^ p = 1) →
      A ≤ Subgroup.normalizer (L : Set G) := fun A hAK hAp a ha =>
    h.mem_normalizer_block hB3 hp5 hp hp5 (hAK ha)
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hAp a ha)) hL
  rcases Nat.lt_or_ge n 3 with hn | hn
  ·
    have hn2 : n = 2 := by have := h.two_le; omega
    obtain ⟨U, hZU, hUR, hUU, hZc, hUp, hUcard, hppd⟩ := h.pair hn2
    obtain ⟨r, hr, hrdvd, hprim⟩ :=
      CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) (n := 4)
        (by omega) (by norm_num)
    obtain ⟨t, htK, htU, htr, -, htrU, htnt, hirr⟩ := hppd r hr hrdvd hprim
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hprim 1 one_pos (by norm_num) (by
        have := hp.eq_one_or_self_of_dvd 2
        rw [pow_one]; exact (Nat.Prime.even_sub_one hp hp2).two_dvd)
    have hr3 : r ≠ 3 := by
      rintro rfl
      apply hprim 2 (by norm_num) (by norm_num)
      have h3p : ¬ 3 ∣ p := fun h3 => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3; omega
      have : p ^ 2 % 3 = 1 := by
        have : p % 3 = 1 ∨ p % 3 = 2 := by omega
        rcases this with h1 | h1 <;> simp [Nat.pow_mod, h1]
      omega
    have hrp : r ≠ p := by
      rintro rfl
      have h4 : r ∣ r ^ 4 := dvd_pow_self r (by norm_num)
      have h1 : r ∣ 1 := by
        have h5 : r ^ 4 = (r ^ 4 - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hr.pos)).symm
        rw [h5] at h4
        exact (Nat.dvd_add_right hrdvd).mp h4
      exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
    have hrp1 : ¬ r ∣ p - 1 := by simpa using hprim 1 one_pos (by norm_num)
    have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
    have htL := h.mem_normalizer_block hB3 hp5 hr hr5 htK htr hL
    have hUL := hpL U (hUR.trans h.ph3.le_inf) hUp
    have hUpg : IsPGroup p U := h.ph3.isPGroup_R.to_le hUR
    have hrel : Z.relIndex U = p ^ 4 := by
      have h1 := Subgroup.relIndex_mul_card Z U
      rw [inf_of_le_left hZU, h.card_eq, hUcard, hn2] at h1
      have h6 : p ^ 6 = p ^ 4 * p ^ 2 := by rw [← pow_add]
      rw [h6] at h1
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h1
    have hUbar := hLB G M (pCoreOf 2 H) L U Z p r t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
      hnS hp hp2 h.cyc (hKeq ▸ hUR.trans h.ph3.le_inf) hUL hUpg hUU hZc
      (fun u hu => by rw [hUp u hu]; exact Z.one_mem)
      (by rw [hrel]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
      (hKeq ▸ htK) htL htU hr hr2 hr3 hrp hrp1
      (fun u hu => by rw [htrU u hu, mul_inv_cancel]; exact Z.one_mem) htnt hirr
    exact (Subgroup.map_mono (Subgroup.subgroupOf_mono M hZU)).trans hUbar
  ·
    obtain ⟨r, t, hr, hnr, hr2, hr3, hrp, hrp1, htK, htZ, htr, htr1, htnt, hirr⟩ :=
      exists_ppd_torus_element hp2 hn h.torus_sq
    have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
    have htL := h.mem_normalizer_block hB3 hp5 hr hr5 htK htr hL
    have hZL := hpL Z hZK fun z hz => h.isElemAbelian.2 z hz
    exact stmtLemmaBCyc_of_relCyc hLB G M (pCoreOf 2 H) L Z p r t h.ph3.isKGroup.1
      h.ph3.asc81bHyp hL hnot1 hnS hp hp2 h.cyc (hKeq ▸ hZK) hZL h.isElemAbelian
      (by rw [h.card_eq]; exact Nat.pow_le_pow_right hp.pos hn) (hKeq ▸ htK) htL htZ hr hr2
      hr3 hrp hrp1 htr1 htnt
      (fun Y hYZ hYt => hirr 1 (by simpa using hr.one_lt.ne') Y hYZ (by simpa using hYt))

end CFSG.AGLEmbedding
