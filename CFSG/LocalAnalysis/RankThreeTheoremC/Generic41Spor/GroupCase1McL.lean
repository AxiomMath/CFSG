module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCase1Heis
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Conj
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Hall
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Orders
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Solv
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Thompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Corollary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools CFSG.Quasithin
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

variable {G : Type} [Group G] [Finite G]

private theorem mcl_mem_normalizer_of_comm {T : Subgroup G} {x : G}
    (hxcT : ∀ t ∈ T, x * t = t * x) : x ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hxcT n hn, mul_inv_cancel_right]
    exact hn
  · intro hn
    have hc := hxcT _ hn
    have e : x * n * x⁻¹ * x = x * n := inv_mul_cancel_right (x * n) x
    have hc' : x * (x * n * x⁻¹) = x * n := hc.trans e
    have key : x * n * x⁻¹ = n := mul_left_cancel hc'
    rw [key] at hn
    exact hn

theorem mcl_zpow_eq_one_of_mem {p : ℕ} (hp : p.Prime) {W : Subgroup G} {x : G} (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) (hxW : x ∉ W) : ∀ k : ℤ, x ^ k ∈ W → x ^ k = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro k hk
  by_contra hne
  apply hxW
  have hord : orderOf (x ^ k) = p := by
    have h1 : orderOf (x ^ k) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hle : zpowers (x ^ k) ≤ W := Subgroup.zpowers_le.2 hk
  have heq : zpowers (x ^ k) = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ?_) ?_
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
    · simp only [Nat.card_zpowers]
      rw [hord, orderOf_eq_prime hxp hx1]
  have : x ∈ zpowers (x ^ k) := by rw [heq]; exact Subgroup.mem_zpowers x
  exact hle this

theorem mcl_card_sup_zpowers {p : ℕ} (hp : p.Prime) {T : Subgroup G} {x : G} (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) (hxT : x ∉ T) (hxcT : ∀ t ∈ T, x * t = t * x) :
    Nat.card ↥(T ⊔ zpowers x) = Nat.card T * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxord : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hbot : T ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.1 hg).2
    rw [Subgroup.mem_bot]
    exact mcl_zpow_eq_one_of_mem hp hxp hx1 hxT k (Subgroup.mem_inf.1 hg).1
  have hzN : zpowers x ≤ normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr (mcl_mem_normalizer_of_comm hxcT)
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_sup_mul_card_inf_of_le_normalizer
    (N := T) (K := zpowers x) hzN
  rw [hbot, hxord, Subgroup.card_bot, mul_one] at h
  exact h

theorem mcl_not_mem_sup {p : ℕ} [Fact p.Prime] {R T : Subgroup G} {x : G}
    (hTn : T ≤ normalizer (R : Set G)) (hTR : T ⊓ R = ⊥) (hRcop : Nat.Coprime p (Nat.card R))
    (hTcard : Nat.card T = p ^ 3) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x) : x ∉ T ⊔ R := by
  intro hx
  have hp : p.Prime := Fact.out
  have hV : T ⊔ zpowers x ≤ T ⊔ R := sup_le le_sup_left (zpowers_le.2 hx)
  have hVcard := mcl_card_sup_zpowers hp hxp hx1 hxT hxcT
  have hTRcard : Nat.card ↥(R ⊔ T) * Nat.card ↥(R ⊓ T) = Nat.card R * Nat.card T :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.card_sup_mul_card_inf_of_le_normalizer hTn
  rw [inf_comm, hTR, Subgroup.card_bot, mul_one, sup_comm] at hTRcard
  have hdvd := Subgroup.card_dvd_of_le hV
  rw [hVcard, hTRcard, hTcard] at hdvd
  have h2 : p ∣ Nat.card R := by
    have h3 : p ^ 3 * p ∣ p ^ 3 * Nat.card R := by
      rwa [mul_comm (Nat.card R)] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) h3
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hRcop h2

theorem mcl_case1_final {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M Y S T : Subgroup G} {x a : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hF : CharTwo (Y ⊔ S)) (hperm : ∀ w ∈ Y ⊔ S, ∃ y ∈ Y, ∃ s ∈ S, w = y * s)
    (hSdef : S = T ⊔ zpowers x) (hTe : ∀ t ∈ T, t ^ p = 1) (hTc : ¬ IsCyclic T)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxcT : ∀ t ∈ T, x * t = t * x) (hxT : x ∉ T)
    (hxY : x ∈ normalizer (Y : Set G)) (haY : a ∈ normalizer (Y : Set G)) (haT : a ∈ T)
    (ha1 : a ≠ 1) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hprod := CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281.glauberman_Q_product p hp h5
    hY2 hSp hperm hF
  have hTS : T ≤ S := hSdef ▸ le_sup_left
  have hxS : x ∈ S := hSdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxA : x ∈ S ⊓ normalizer (thompsonJ Y : Set G) :=
    ⟨hxS, normalizer_le_normalizer_thompsonJ' Y hxY⟩
  have hxB : x ∈ S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
    ⟨hxS, normalizer_le_normalizer_omegaOneCenter Y hxY⟩
  have haA : a ∈ S ⊓ normalizer (thompsonJ Y : Set G) :=
    ⟨hTS haT, normalizer_le_normalizer_thompsonJ' Y haY⟩
  have haB : a ∈ S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
    ⟨hTS haT, normalizer_le_normalizer_omegaOneCenter Y haY⟩
  have hint : (S ⊓ normalizer (thompsonJ Y : Set G)) ⊓
      (S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G)) ⊓ T ≠ ⊥ := by
    intro h
    have hmem : a ∈ (S ⊓ normalizer (thompsonJ Y : Set G)) ⊓
        (S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G)) ⊓ T := ⟨⟨haA, haB⟩, haT⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hrank := three_le_pRank_of_mul_heis hp hSdef hTe hTc hxp hx1 hxcT hxT inf_le_left inf_le_left
    hxA hxB hprod hint
  rcases hrank with hA3 | hB3
  · have hJ2 : IsPGroup 2 (thompsonJ Y) := hY2.to_le (Generic49U3.thompsonJ_le_self Y)
    have hloc : IsTwoLocal (normalizer (thompsonJ Y : Set G)) :=
      ⟨thompsonJ Y, thompsonJ_ne_bot_of_two_group hY2 hY1, hJ2, rfl⟩
    have hAle : S ⊓ normalizer (thompsonJ Y : Set G) ≤ normalizer (thompsonJ Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_thompsonJ' Y).trans
      (hD1' _ hloc (hA3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hAle)))
  · have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter Y) := hY2.to_le (Generic49U3.omegaOneCenter_le_self Y)
    have hloc : IsTwoLocal (normalizer (quasithinOmegaOneCenter Y : Set G)) :=
      ⟨quasithinOmegaOneCenter Y, omegaOneCenter_ne_bot_of_two_group hY2 hY1, hZ2, rfl⟩
    have hBle : S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) ≤
        normalizer (quasithinOmegaOneCenter Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_omegaOneCenter Y).trans
      (hD1' _ hloc (hB3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hBle)))

theorem mcl_case1_core {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {M R T Y U : Subgroup G} {x : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime p (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hTcard : Nat.card T = p ^ 3) (hTexp : ∀ t ∈ T, t ^ p = 1)
    (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x)
    (hVp : IsPGroup p (T ⊔ zpowers x : Subgroup G))
    (hUV : U ≤ T ⊔ zpowers x) (hxU : x ∈ U) (haU : ∃ a ∈ U ⊓ T, a ≠ 1)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R) :
    normalizer (Y : Set G) ≤ M := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hVM : T ⊔ zpowers x ≤ M := sup_le hTM (zpowers_le.2 hxM)
  have hTR : T ⊓ R = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [hTcard]; exact Nat.Coprime.pow_left 3 hRcop))
  obtain ⟨c, hcR, hcU, hYB', hVN⟩ :=
    exists_conj_normalizes_inf hVp hRcop (hVM.trans hRn) hUV (hYM.trans hRn) hUY hYB
  set Y' : Subgroup G := Y.map (MulAut.conj c).toMonoidHom with hY'
  have hcM : c ∈ M := hRM hcR
  have hY'M : Y' ≤ M := map_conj_le_of_mem hcM hYM
  have hY'2 : IsPGroup 2 Y' := hY2.map _
  have hUY' : U ≤ normalizer (Y' : Set G) := fun u hu =>
    mem_normalizer_map_conj_of_commute (hcU u hu) (hUY hu)
  have hxY' : x ∈ normalizer (Y' : Set G) := hUY' hxU
  obtain ⟨hVsyl, hYsyl, hidx⟩ := case1_orders hp2 hRM hRn hRcop hNn hTM hTcard hxM hxp hx1 hxT hxcT
    hY'M hY'2 hxY' hYB'
  set H₁ : Subgroup G := (T ⊔ R) ⊔ (Y' ⊔ zpowers x) with hH₁
  have hH₁M : H₁ ≤ M := sup_le (sup_le hTM hRM) (sup_le hY'M (zpowers_le.2 hxM))
  have hRH₁ : R ≤ H₁ := le_sup_right.trans le_sup_left
  have hVH₁ : T ⊔ zpowers x ≤ H₁ := hVsyl.le
  have hY'H₁ : Y' ≤ H₁ := hYsyl.le
  have hsolv := solvable_normalizer_inf_of_sylow hp hp2 hRH₁ (hH₁M.trans hRn) hidx hYB'
  set L : Subgroup G := H₁ ⊓ normalizer ((Y' ⊓ R : Subgroup G) : Set G) with hL
  have hVL : T ⊔ zpowers x ≤ L := le_inf hVH₁ hVN
  have hY'L : Y' ≤ L :=
    le_inf hY'H₁ (le_normalizer_inf_of_le_normalizer (hY'M.trans hRn))
  have hVsylL : IsSylowOf p (T ⊔ zpowers x) L := hVsyl.of_le hVL inf_le_left
  have hYsylL : IsSylowOf 2 Y' L := hYsyl.of_le hY'L inf_le_left
  have hUL : U ≤ L := hUV.trans hVL
  obtain ⟨l, hlL, hUS, hperm⟩ :=
    exists_permutable_conj_sylow hp2 hsolv hYsylL hVsylL hUL (hVp.to_le hUV) hUY'
  set S : Subgroup G := (T ⊔ zpowers x).map (MulAut.conj l).toMonoidHom with hS
  have hlM : l ∈ M := hH₁M (Subgroup.mem_inf.1 hlL).1
  have hSM : S ≤ M := map_conj_le_of_mem hlM hVM
  have hSp : IsPGroup p S := hVp.map _
  have hxS : x ∈ S := hUS hxU
  have hxc : ∀ s ∈ S, x * s = s * x := by
    intro s hs
    have hw : l⁻¹ * x * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 hxS
    have hcomm := conj_commutes_of_hnorm hRM hRn hNn hTM hTR hxM hxcT hlM hxM hxcT rfl hw
    have hv : l⁻¹ * s * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 hs
    have h := hcomm _ hv
    calc x * s = l * ((l⁻¹ * x * l) * (l⁻¹ * s * l)) * l⁻¹ := by group
      _ = l * ((l⁻¹ * s * l) * (l⁻¹ * x * l)) * l⁻¹ := by rw [h]
      _ = s * x := by group
  set T' : Subgroup G := T.map (MulAut.conj l).toMonoidHom with hT'
  have hT'S : T' ≤ S := Subgroup.map_mono le_sup_left
  have hT'TR : T' ≤ T ⊔ R := by
    rintro y ⟨t, ht, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hNn hlM) t).1 (Subgroup.mem_sup_left ht)
    simpa [MulAut.conj_apply] using this
  have hxTR : x ∉ T ⊔ R :=
    mcl_not_mem_sup (hTM.trans hRn) hTR hRcop hTcard hxp hx1 hxT hxcT
  have hxT' : x ∉ T' := fun h => hxTR (hT'TR h)
  have hT'card : Nat.card T' = p ^ 3 := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj l).injective, hTcard]
  have hScard : Nat.card S = p ^ 4 := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj l).injective,
      mcl_card_sup_zpowers hp hxp hx1 hxT hxcT, hTcard]
    ring
  have hxcT' : ∀ t ∈ T', x * t = t * x := fun t ht => hxc t (hT'S ht)
  have hSdef : S = T' ⊔ zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hT'S (zpowers_le.2 hxS)) ?_).symm
    rw [mcl_card_sup_zpowers hp hxp hx1 hxT' hxcT', hT'card, hScard]
    exact le_of_eq (by ring)
  have hT'exp : ∀ t ∈ T', t ^ p = 1 := by
    rintro y ⟨t, ht, rfl⟩
    rw [← map_pow, hTexp t ht, map_one]
  have hT'c : ¬ IsCyclic T' := by
    intro hcyc
    have h1 : Monoid.exponent ↥T' = Nat.card ↥T' := IsCyclic.exponent_eq_card
    have h2 : Monoid.exponent ↥T' ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hT'exp g.1 g.2)
    rw [h1, hT'card] at h2
    have h3 := Nat.le_of_dvd hp.pos h2
    have h4 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hSTR : S ⊓ (T ⊔ R) = T' := by
    have hDS : S ⊓ (T ⊔ R) ≤ S := inf_le_left
    have hT'D : T' ≤ S ⊓ (T ⊔ R) := le_inf hT'S hT'TR
    symm
    refine Subgroup.eq_of_le_of_card_ge hT'D ?_
    have hdvd : Nat.card ↥(S ⊓ (T ⊔ R)) ∣ p ^ 4 := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le hDS
    obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hT'card, hDi]
    by_contra hlt
    have hi4 : i = 4 := by
      by_contra hne
      apply hlt
      exact Nat.pow_le_pow_right hp.pos (by omega)
    subst hi4
    have hDeq : S ⊓ (T ⊔ R) = S := Subgroup.eq_of_le_of_card_ge hDS (by rw [hDi, hScard])
    have hxD : x ∈ S ⊓ (T ⊔ R) := by rw [hDeq]; exact hxS
    exact hxTR hxD.2
  obtain ⟨a, haUT, ha1⟩ := haU
  have haT' : a ∈ T' := by
    rw [← hSTR]
    exact ⟨hUS haUT.1, Subgroup.mem_sup_left haUT.2⟩
  have hO2Y' : pCoreOf 2 M ≤ Y' ⊓ R :=
    le_of_normal_isPGroup_of_isSylowOf hYB' hO2R
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
  exact normalizer_le_of_normalizer_map_conj_le hcM
    (mcl_case1_final h5 hD1' hY'2 hY'1 hSp hSM hF hperm hSdef hT'exp hT'c hxp hx1 hxcT' hxT' hxY'
      (hUY' haUT.1) haT' ha1)

theorem mcl_le_sup_of_card {p : ℕ} (hp : p.Prime) {U T : Subgroup G} {x : G}
    (hUc : IsMulCommutative U) (hUcard : Nat.card U = p ^ 2) (hUT : Nat.card ↥(U ⊓ T) = p)
    (hxU : x ∈ U) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxT : x ∉ T) : U ≤ T ⊔ zpowers x := by
  have hxA : x ∉ U ⊓ T := fun h => hxT h.2
  have hxcA : ∀ t ∈ U ⊓ T, x * t = t * x := by
    intro t ht
    exact congrArg Subtype.val (hUc.is_comm.comm (⟨x, hxU⟩ : U) ⟨t, ht.1⟩)
  have hcard := mcl_card_sup_zpowers hp hxp hx1 hxA hxcA
  have hle : (U ⊓ T) ⊔ zpowers x ≤ U := sup_le inf_le_left (zpowers_le.2 hxU)
  have heq : (U ⊓ T) ⊔ zpowers x = U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hUT, hUcard]; exact le_of_eq (by ring))
  rw [← heq]
  exact sup_le_sup_right inf_le_right _

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
