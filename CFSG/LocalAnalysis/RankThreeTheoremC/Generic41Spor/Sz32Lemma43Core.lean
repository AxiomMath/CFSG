module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Conj
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Solv
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Hall
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Thompson
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Corollary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem szj_not_two_dvd {p r k : ℕ} (hp2' : Nat.Coprime 2 p) (hr : r ≠ 0)
    (hd : 2 ^ (r.factorization 2) * 2 ∣ r * p ^ k) : False := by
  have hcop : Nat.Coprime (2 ^ (r.factorization 2 + 1)) (p ^ k) :=
    Nat.Coprime.pow _ _ hp2'
  have hpow : 2 ^ (r.factorization 2 + 1) ∣ r * p ^ k := by
    rw [pow_succ (2 : ℕ) (r.factorization 2)]
    exact hd
  have h3 : 2 ^ (r.factorization 2 + 1) ∣ r := Nat.Coprime.dvd_of_dvd_mul_right hcop hpow
  exact Nat.pow_succ_factorization_not_dvd hr Nat.prime_two h3

theorem szj_orders {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R V Y : Subgroup G}
    (hVn : V ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hVp : IsPGroup p V) (hYn : Y ≤ normalizer ((V ⊔ R : Subgroup G) : Set G))
    (hY2 : IsPGroup 2 Y) (hYB : CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ R) R) :
    CFSG.ABGLocalTools.IsSylowOf p V ((V ⊔ R) ⊔ Y) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 Y ((V ⊔ R) ⊔ Y) ∧
    ∀ q : ℕ, q.Prime → q ∣ R.relIndex ((V ⊔ R) ⊔ Y) → q = 2 ∨ q = p := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : 0 < p := hp.pos
  have hp2' : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hRp : ¬ p ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd hp).1 hRcop
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hRne : Nat.card R ≠ 0 := hRpos.ne'
  obtain ⟨k, hk⟩ := hVp.exists_card_eq
  obtain ⟨a, ha⟩ := hY2.exists_card_eq
  have hRV_bot : R ⊓ V = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact Nat.Coprime.pow_right k hRcop.symm
  have hRV_card : Nat.card ↥(R ⊓ V) = 1 := Subgroup.card_eq_one.mpr hRV_bot
  have hVR : Nat.card ↥(V ⊔ R) = Nat.card R * p ^ k := by
    have h := Generic49U3.card_sup_mul_card_inf_of_le_normalizer (N := R) (K := V) hVn
    rw [hRV_card, mul_one, hk, sup_comm] at h
    exact h
  have hH := Generic49U3.card_sup_mul_card_inf_of_le_normalizer (N := V ⊔ R) (K := Y) hYn
  rw [hVR, ha] at hH
  have hVle : V ≤ (V ⊔ R) ⊔ Y := le_sup_left.trans le_sup_left
  have hYle : Y ≤ (V ⊔ R) ⊔ Y := le_sup_right
  have hRle : R ≤ (V ⊔ R) ⊔ Y := le_sup_right.trans le_sup_left
  have partA : CFSG.ABGLocalTools.IsSylowOf p V ((V ⊔ R) ⊔ Y) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hVle, hVp, ?_⟩
    intro hdvd
    have hA := Subgroup.relIndex_mul_card V ((V ⊔ R) ⊔ Y)
    rw [inf_eq_left.mpr hVle, hk] at hA
    have hAB : V.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) = Nat.card R * 2 ^ a := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hp0 k)
      calc V.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) * p ^ k
          = (V.relIndex ((V ⊔ R) ⊔ Y) * p ^ k) * Nat.card ↥((V ⊔ R) ⊓ Y) := by ring
        _ = Nat.card ↥((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) := by rw [hA]
        _ = Nat.card R * p ^ k * 2 ^ a := hH
        _ = Nat.card R * 2 ^ a * p ^ k := by ring
    have hd : p ∣ Nat.card R * 2 ^ a := by
      rw [← hAB]
      exact Dvd.dvd.mul_right hdvd _
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
    · exact hRp h1
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  have partB : CFSG.ABGLocalTools.IsSylowOf 2 Y ((V ⊔ R) ⊔ Y) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hYle, hY2, ?_⟩
    have hYr := Subgroup.relIndex_mul_card Y ((V ⊔ R) ⊔ Y)
    rw [inf_eq_left.mpr hYle, ha] at hYr
    have hmB : Y.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) = Nat.card R * p ^ k := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) a)
      calc Y.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) * 2 ^ a
          = (Y.relIndex ((V ⊔ R) ⊔ Y) * 2 ^ a) * Nat.card ↥((V ⊔ R) ⊓ Y) := by ring
        _ = Nat.card ↥((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) := by rw [hYr]
        _ = Nat.card R * p ^ k * 2 ^ a := hH
    have hYR : Y ⊓ R ≤ (V ⊔ R) ⊓ Y :=
      le_inf (le_trans inf_le_right le_sup_right) inf_le_left
    have hYRdvd : Nat.card ↥(Y ⊓ R) ∣ Nat.card ↥((V ⊔ R) ⊓ Y) := Subgroup.card_dvd_of_le hYR
    rw [hYB.card_eq] at hYRdvd
    intro h2
    have hd := mul_dvd_mul hYRdvd h2
    rw [mul_comm (Nat.card ↥((V ⊔ R) ⊓ Y)), hmB] at hd
    exact szj_not_two_dvd hp2' hRne hd
  refine ⟨partA, partB, ?_⟩
  intro q hq hqd
  have hR_card := Subgroup.relIndex_mul_card R ((V ⊔ R) ⊔ Y)
  rw [inf_eq_left.mpr hRle] at hR_card
  have hRB : R.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) = p ^ k * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    calc R.relIndex ((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) * Nat.card R
        = (R.relIndex ((V ⊔ R) ⊔ Y) * Nat.card R) * Nat.card ↥((V ⊔ R) ⊓ Y) := by ring
      _ = Nat.card ↥((V ⊔ R) ⊔ Y) * Nat.card ↥((V ⊔ R) ⊓ Y) := by rw [hR_card]
      _ = Nat.card R * p ^ k * 2 ^ a := hH
      _ = p ^ k * 2 ^ a * Nat.card R := by ring
  have hqd' : q ∣ p ^ k * 2 ^ a := by
    rw [← hRB]
    exact Dvd.dvd.mul_right hqd _
  rcases (Nat.Prime.dvd_mul hq).1 hqd' with h1 | h1
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h1))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools in
theorem szj_final {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M Y S U : Subgroup G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hF : CharTwo (Y ⊔ S)) (hperm : ∀ w ∈ Y ⊔ S, ∃ y ∈ Y, ∃ s ∈ S, w = y * s)
    (hUS : U ≤ S) (hUY : U ≤ normalizer (Y : Set G))
    (hrank : ∀ A B : Subgroup G, A ≤ S → B ≤ S → U ≤ A → U ≤ B →
      (∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) →
      3 ≤ CFSG.Open.pRank p A ∨ 3 ≤ CFSG.Open.pRank p B) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hprod := CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281.glauberman_Q_product p hp h5
    hY2 hSp hperm hF
  have hUA : U ≤ S ⊓ normalizer (thompsonJ Y : Set G) :=
    le_inf hUS (hUY.trans (Generic49U3.normalizer_le_normalizer_thompsonJ' Y))
  have hUB : U ≤ S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
    le_inf hUS (hUY.trans (Generic49U3.normalizer_le_normalizer_omegaOneCenter Y))
  rcases hrank _ _ inf_le_left inf_le_left hUA hUB hprod with hA3 | hB3
  · have hJ2 : IsPGroup 2 (thompsonJ Y) := hY2.to_le (Generic49U3.thompsonJ_le_self Y)
    have hloc : IsTwoLocal (normalizer (thompsonJ Y : Set G)) :=
      ⟨thompsonJ Y, Generic49U3.thompsonJ_ne_bot_of_two_group hY2 hY1, hJ2, rfl⟩
    have hAle : S ⊓ normalizer (thompsonJ Y : Set G) ≤ normalizer (thompsonJ Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (Generic49U3.normalizer_le_normalizer_thompsonJ' Y).trans
      (hD1' _ hloc (hA3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hAle)))
  · have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter Y) :=
      hY2.to_le (Generic49U3.omegaOneCenter_le_self Y)
    have hloc : IsTwoLocal (normalizer (quasithinOmegaOneCenter Y : Set G)) :=
      ⟨quasithinOmegaOneCenter Y, Generic49U3.omegaOneCenter_ne_bot_of_two_group hY2 hY1, hZ2, rfl⟩
    have hBle : S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) ≤
        normalizer (quasithinOmegaOneCenter Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (Generic49U3.normalizer_le_normalizer_omegaOneCenter Y).trans
      (hD1' _ hloc (hB3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hBle)))

open CFSG.QuasithinUnique CFSG.ABGLocalTools in
theorem szj_case1_core {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M R V Y U : Subgroup G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hVM : V ≤ M) (hVp : IsPGroup p V) (hMn : M ≤ normalizer ((V ⊔ R : Subgroup G) : Set G))
    (hUV : U ≤ V)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R)
    (hrank : ∀ l : G, U ≤ V.map (MulAut.conj l).toMonoidHom → ∀ A B : Subgroup G,
      A ≤ V.map (MulAut.conj l).toMonoidHom → B ≤ V.map (MulAut.conj l).toMonoidHom →
      U ≤ A → U ≤ B →
      (∀ s ∈ V.map (MulAut.conj l).toMonoidHom, ∃ a ∈ A, ∃ b ∈ B, s = a * b) →
      3 ≤ CFSG.Open.pRank p A ∨ 3 ≤ CFSG.Open.pRank p B) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hVn : V ≤ normalizer (R : Set G) := hVM.trans hRn
  obtain ⟨c, hcR, hcU, hYB', hVN⟩ :=
    Generic49U3.exists_conj_normalizes_inf hVp hRcop hVn hUV (hYM.trans hRn) hUY hYB
  set Y' : Subgroup G := Y.map (MulAut.conj c).toMonoidHom with hY'
  have hcM : c ∈ M := hRM hcR
  have hY'M : Y' ≤ M := Generic49U3.map_conj_le_of_mem hcM hYM
  have hY'2 : IsPGroup 2 Y' := hY2.map _
  have hUY' : U ≤ normalizer (Y' : Set G) := fun u hu =>
    Generic49U3.mem_normalizer_map_conj_of_commute (hcU u hu) (hUY hu)
  have hY'N : Y' ≤ normalizer ((V ⊔ R : Subgroup G) : Set G) := hY'M.trans hMn
  obtain ⟨hVsyl, hYsyl, hidx⟩ := szj_orders hp2 hVn hRcop hVp hY'N hY'2 hYB'
  set H₁ : Subgroup G := (V ⊔ R) ⊔ Y' with hH₁
  have hH₁M : H₁ ≤ M := sup_le (sup_le hVM hRM) hY'M
  have hRH₁ : R ≤ H₁ := le_sup_right.trans le_sup_left
  have hVH₁ : V ≤ H₁ := hVsyl.le
  have hY'H₁ : Y' ≤ H₁ := hYsyl.le
  have hsolv :=
    Generic49U3.solvable_normalizer_inf_of_sylow hp hp2 hRH₁ (hH₁M.trans hRn) hidx hYB'
  set L : Subgroup G := H₁ ⊓ normalizer ((Y' ⊓ R : Subgroup G) : Set G) with hL
  have hVL : V ≤ L := le_inf hVH₁ hVN
  have hY'L : Y' ≤ L :=
    le_inf hY'H₁ (Generic49U3.le_normalizer_inf_of_le_normalizer (hY'M.trans hRn))
  have hVsylL : IsSylowOf p V L := hVsyl.of_le hVL inf_le_left
  have hYsylL : IsSylowOf 2 Y' L := hYsyl.of_le hY'L inf_le_left
  have hUL : U ≤ L := hUV.trans hVL
  obtain ⟨l, hlL, hUS, hperm⟩ :=
    Generic49U3.exists_permutable_conj_sylow hp2 hsolv hYsylL hVsylL hUL (hVp.to_le hUV) hUY'
  set S : Subgroup G := V.map (MulAut.conj l).toMonoidHom with hS
  have hlM : l ∈ M := hH₁M (Subgroup.mem_inf.1 hlL).1
  have hSM : S ≤ M := Generic49U3.map_conj_le_of_mem hlM hVM
  have hSp : IsPGroup p S := hVp.map _
  have hO2Y' : pCoreOf 2 M ≤ Y' ⊓ R :=
    Generic49U3.le_of_normal_isPGroup_of_isSylowOf hYB' hO2R
      (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hO2Y : pCoreOf 2 M ≤ Y' := hO2Y'.trans inf_le_left
  have hWM : Y' ⊔ S ≤ M := sup_le hY'M hSM
  have hF : CharTwo (Y' ⊔ S) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281.charTwo_of_le hWM hCharM
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2Y.trans le_sup_left)
        (hWM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M))
  have hY'1 : Y' ≠ ⊥ := by
    intro h
    exact hM2 (le_bot_iff.1 (hO2Y.trans h.le))
  exact Generic49U3.normalizer_le_of_normalizer_map_conj_le hcM
    (szj_final h5 hD1' hY'2 hY'1 hSp hSM hF hperm hUS hUY'
      (fun A B hA hB hUA hUB hAB => hrank l hUS A B hA hB hUA hUB hAB))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
