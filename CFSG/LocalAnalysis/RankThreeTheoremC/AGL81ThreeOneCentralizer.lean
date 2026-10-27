module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneReductions
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeStepsRank
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Main
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
public import CFSG.LocalAnalysis.RankFourTheoremC.NongenerationMonster

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration (barAct)

private theorem normalizer_le_weakCore_of_central {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime)
    {P K : Subgroup G} {c : G} (hcP : c ∈ P) (hcC : c ∈ Subgroup.centralizer (K : Set G))
    (hcK : c ∉ K) (hcp : orderOf c = p) {T Q : Subgroup K} (hTP : T.map K.subtype ≤ P)
    (hQT : Q ≤ T) {s : K} (hsQ : s ∈ Q) (hsp : orderOf s = p)
    (h2 : 2 ≤ Open.pRank p (Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set K)))) :
    Subgroup.normalizer (Q : Set K) ≤ (GLBWeakCore p P).comap K.subtype := by
  set Q₁ : Subgroup G := Q.map K.subtype ⊔ Subgroup.zpowers c
  have hcQ₁ : c ∈ Q₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hQ₁P : Q₁ ≤ P := sup_le ((Subgroup.map_mono hQT).trans hTP) (Subgroup.zpowers_le.2 hcP)
  have hrank2 : 2 ≤ Open.pRank p Q₁ := by
    refine CFSG.AGLEmbeddingD2.two_le_pRank_of_commute hp (a := (s : G)) (b := c)
      (by rw [Subgroup.orderOf_coe, hsp]) hcp
      (Subgroup.centralizer_le (Subgroup.zpowers_le.2 s.2) hcC)
      (fun h => hcK (Subgroup.zpowers_le.2 s.2 h)) (Subgroup.mem_sup_left ⟨s, hsQ, rfl⟩) hcQ₁
  have hrank3 : 3 ≤ Open.pRank p (Q₁ ⊔ (P ⊓ Subgroup.centralizer (Q₁ : Set G))) := by
    obtain ⟨A, hAle, hA, hAcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
    have hA'card : Nat.card (A.map K.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hAcard]
    refine three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp (hA.map K.subtype) hA'card
      hcp (fun h => hcK (Subgroup.map_subtype_le A h))
      (Subgroup.centralizer_le (Subgroup.map_subtype_le A) hcC) ?_ (Subgroup.mem_sup_left hcQ₁)
    refine (Subgroup.map_mono hAle).trans ?_
    rw [Subgroup.map_sup]
    refine sup_le_sup le_sup_left ?_
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 ht
    refine Subgroup.mem_inf.2 ⟨hTP ⟨t, htT, rfl⟩, ?_⟩
    rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 htC q hq)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le (Subgroup.zpowers_le.2 t.2) hcC
  intro n hn
  have h1 : (n : G) ∈ Subgroup.normalizer ((Q.map K.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map (H := Q) K.subtype (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)
  have h2' : (n : G) ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.le_centralizer_iff.1 (Subgroup.zpowers_le.2 hcC) n.2)
  exact CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hQ₁P hrank2 hrank3
    (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2'⟩)

theorem le_weakCore_of_gammaOne {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P K : Subgroup G} {c : G} (hcP : c ∈ P) (hcC : c ∈ Subgroup.centralizer (K : Set G))
    (hcK : c ∉ K) (hcp : orderOf c = p) (T : Sylow p K)
    (hTP : (T : Subgroup K).map K.subtype ≤ P) (h2 : 2 ≤ Open.pRank p (T : Subgroup K))
    (hΓ : GLBCore p 1 (T : Subgroup K) = ⊤) : K ≤ GLBWeakCore p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTne : (T : Subgroup K) ⊓ ⊤ ≠ ⊥ := by
    rw [inf_top_eq]
    intro hbot
    obtain ⟨A, hAT, -, hAcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
    rw [hbot, le_bot_iff] at hAT
    rw [hAT, Subgroup.card_bot] at hAcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨z, hzT', hzp, hzc⟩ :=
    RankFourTheoremC.Nongeneration.exists_central_orderOf T (N := ⊤) hTne
  have hzT : z ∈ (T : Subgroup K) := (Subgroup.mem_inf.1 hzT').1
  have hcomm : ∀ x ∈ (T : Subgroup K), x ∈ Subgroup.centralizer
      ((Subgroup.zpowers z : Subgroup K) : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute z x from (hzc x hx).symm) j).eq
  have key : ∀ Q : Subgroup K, Q ≤ T → 1 ≤ Open.pRank p Q →
      Subgroup.normalizer (Q : Set K) ≤ (GLBWeakCore p P).comap K.subtype := by
    intro Q hQT hQ1
    have hQne : Q ≠ ⊥ := by
      rintro rfl
      obtain ⟨A, hA, -, hAcard⟩ :=
        GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp hQ1
      rw [le_bot_iff] at hA
      rw [hA, Subgroup.card_bot, pow_one] at hAcard
      exact hp.one_lt.ne hAcard
    obtain ⟨s, hsQ, hsp⟩ :=
      RankFourTheoremC.exists_mem_orderOf_eq_of_isPGroup_ne_bot (T.isPGroup'.to_le hQT) hQne
    by_cases hQ2 : 2 ≤ Open.pRank p (Q ⊔ ((T : Subgroup K) ⊓ Subgroup.centralizer (Q : Set K)))
    · exact normalizer_le_weakCore_of_central hp hcP hcC hcK hcp hTP hQT hsQ hsp hQ2
    have hzCQ : z ∈ Subgroup.centralizer (Q : Set K) :=
      Subgroup.mem_centralizer_iff.2 fun h hh => hzc h (hQT hh)
    have hsub : ∀ x ∈ Q, orderOf x = p → x ∈ Subgroup.zpowers z := by
      intro x hxQ hxp
      by_contra hxz
      exact hQ2 (CFSG.AGLEmbeddingD2.two_le_pRank_of_commute hp hzp hxp (hcomm x (hQT hxQ)) hxz
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hzT, hzCQ⟩)) (Subgroup.mem_sup_left hxQ))
    have hzQ : z ∈ Q := by
      have heq : Subgroup.zpowers s = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (hsub s hsQ hsp))
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hsp, hzp])
      have hzs : z ∈ Subgroup.zpowers s := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact Subgroup.zpowers_le.2 hsQ hzs
    have hZ₀ : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup K) : Set K) ≤
        (GLBWeakCore p P).comap K.subtype :=
      normalizer_le_weakCore_of_central hp hcP hcC hcK hcp hTP (Subgroup.zpowers_le.2 hzT)
        (Subgroup.mem_zpowers z) hzp (h2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
          (le_sup_of_le_right (le_inf le_rfl hcomm))))
    refine le_trans (fun n hn => ?_) hZ₀
    refine Subgroup.mem_normalizer_fintype fun h hh => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    refine Subgroup.zpow_mem _ (hsub _ ((Subgroup.mem_normalizer_iff.1 hn z).1 hzQ) ?_) j
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hzp]
  have hW : (GLBWeakCore p P).comap K.subtype = ⊤ := by
    rw [eq_top_iff, ← hΓ]
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQ1, rfl⟩
    exact key Q hQT hQ1
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ (GLBWeakCore p P).comap K.subtype := hW ▸ Subgroup.mem_top _
  exact this

theorem le_weakCore_of_closure_fixed {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R K : Subgroup G} [K.Normal] (hperf : commutator ↥K = ⊤)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥K)) {A : Subgroup G} (hAR : A ≤ R)
    (hA : IsElemAbelian p A) {c : G} (hcR : c ∈ R) (hcK : c ∈ Subgroup.centralizer (K : Set G))
    (hcp : orderOf c = p) (hcA : ∀ a ∈ A, a * c = c * a)
    (h3 : 3 ≤ Open.pRank p (A ⊔ Subgroup.zpowers c))
    {E : Subgroup (MulAut (K ⧸ Subgroup.center K))} (hE : E ≤ A.map (barAct K))
    (hgen : Subgroup.closure {kb : K ⧸ Subgroup.center K | ∃ e ∈ E, e ≠ 1 ∧ e kb = kb} = ⊤) :
    K ≤ GLBWeakCore p R := by
  classical
  have hp : p.Prime := Fact.out
  have hcpow : c ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one c
  have hAc : IsElemAbelian p (A ⊔ Subgroup.zpowers c) :=
    IsElemAbelian.sup_of_commute hA (CFSG.Open.isElemAbelian_zpowers hcpow) fun a ha b hb => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a c from hcA a ha) j).eq
  have hAcR : A ⊔ Subgroup.zpowers c ≤ R := sup_le hAR (Subgroup.zpowers_le.2 hcR)
  set π : ↥K →* K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set W : Subgroup ↥K := (GLBWeakCore p R).comap K.subtype with hW
  have hsub : {kb : K ⧸ Subgroup.center K | ∃ e ∈ E, e ≠ 1 ∧ e kb = kb} ⊆
      (W.map π : Set (K ⧸ Subgroup.center K)) := by
    rintro kb ⟨e, heE, he1, hek⟩
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.1 (hE heE)
    have hap : a ^ p = 1 := hA.2 a haA
    have hnc : ∃ k ∈ K, a * k ≠ k * a := by
      by_contra hcon
      push Not at hcon
      exact he1 (RankFourTheoremC.Nongeneration.barAct_eq_one_of_commute hcon)
    obtain ⟨k₁, hk₁, hne⟩ := hnc
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hne (by simp)
    have hao : orderOf a = p := orderOf_eq_prime hap ha1
    obtain ⟨k, hkmk, hkfix⟩ := RankFourTheoremC.Nongeneration.exists_fixed_lift hZ hap hek
    have hca : c ∉ Subgroup.zpowers a := by
      intro hc
      have hle : Subgroup.zpowers c ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hc
      have heq : Subgroup.zpowers c = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hcp, hao])
      have hamem : a ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers a
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hamem
      apply hne
      rw [← hj]
      exact ((Commute.zpow_right (show Commute k₁ c from
        Subgroup.mem_centralizer_iff.1 hcK k₁ hk₁) j).eq).symm
    obtain ⟨hel, hcard⟩ := GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hap hcpow ha1
      hca (hcA a haA)
    have hrank : 2 ≤ Open.pRank p (Subgroup.zpowers a ⊔ Subgroup.zpowers c) :=
      GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hel hcard
    have hB := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_commutative_overgroup
      p hp hAcR (sup_le_sup_right (Subgroup.zpowers_le.2 haA) _) hAc.1 hrank h3
    have hQle : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤
        Subgroup.centralizer ({((k : K) : G)} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : a * (k : G) * a⁻¹ = (k : G) := congrArg Subtype.val hkfix
        calc a * (k : G) = a * (k : G) * a⁻¹ * a := by group
          _ = (k : G) * a := by rw [h1]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hcK k k.2).symm
    have hkc : ((k : K) : G) ∈
        Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.1 (hQle hq)
    have hkW : k ∈ W := hB (Subgroup.centralizer_le_normalizer _ hkc)
    exact Subgroup.mem_map.2 ⟨k, hkW, hkmk⟩
  have hmap : W.map π = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).2 hsub
  have hsup : W ⊔ Subgroup.center ↥K = ⊤ := by
    have h1 := Subgroup.comap_map_eq π W
    rw [hmap, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hWtop : W = ⊤ := RankFourTheoremC.Nongeneration.eq_top_of_sup_center hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ W := hWtop ▸ Subgroup.mem_top _
  exact this

section HypB

variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

private theorem Hyp.prime_dvd_card (H : Hyp p K P E) : p ∣ Nat.card K := by
  by_contra hnd
  have hcop : p.Coprime (Nat.card (⊤ : Subgroup K)) := by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd H.prime).2 hnd
  have hle := normal_coprime_le_primeComplementCore p (⊤ : Subgroup K) inferInstance hcop
  rw [H.core, le_bot_iff] at hle
  have hall : ∀ x : K, x = 1 := by
    intro x
    have hx := Subgroup.mem_top x
    rw [hle] at hx
    exact Subgroup.mem_bot.1 hx
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := H.quasi.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  exact hab (by rw [hall a, hall b])

theorem Hyp.card_le_of_le_centralizer (H : Hyp p K P E)
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hZ : Subgroup.center K = ⊥) {B : Subgroup G}
    (hBP : B ≤ P) (hBC : B ≤ Subgroup.centralizer (K : Set G)) (hB : IsElemAbelian p B) :
    Nat.card B ≤ p := by
  have hp := H.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := H.normal
  set T := CFSG.QuasiDihedralFusion.sylowInfNormal P K
  obtain ⟨u, huT, hup⟩ := RankFourTheoremC.exists_mem_orderOf_eq_of_isPGroup_ne_bot T.isPGroup'
    (Sylow.ne_bot_of_dvd_card T (Hyp.prime_dvd_card H))
  have huP : (u : G) ∈ (P : Subgroup G) := by
    rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe] at huT
    exact huT
  have hunc : ∃ g ∈ K, (u : G) * g ≠ g * (u : G) := by
    by_contra hcon
    push Not at hcon
    have hu1 : u ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcon g g.2).symm
    rw [hZ, Subgroup.mem_bot] at hu1
    rw [hu1, orderOf_one] at hup
    exact hp.one_lt.ne hup
  have hrank := pRank_inf_centralizer_component_le_one hp (R := (P : Subgroup G))
    (X₀ := GLBWeakCore p (P : Subgroup G))
    (fun A hAP hA hAcard h3 => (Subgroup.centralizer_le_normalizer _).trans
      (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hAP
        (GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl hA hAcard)
        (h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_right))))
    hnot huP u.2 (by rw [Subgroup.orderOf_coe, hup]) hunc
  obtain ⟨k, hk⟩ := GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hB
  have hk1 : k ≤ 1 :=
    (GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt (le_inf hBP hBC) hB hk).trans hrank
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

end HypB

section CentralizerCert


variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

private theorem Hyp.exists_central_of_ne_bot
    (H : Hyp p K P E) (hZ : Subgroup.center K = ⊥)
    (hC : Subgroup.centralizer (K : Set G) ≠ ⊥) :
    ∃ c ∈ (P : Subgroup G), c ∈ Subgroup.centralizer (K : Set G) ∧ c ∉ K ∧ orderOf c = p ∧
      ∀ g ∈ (P : Subgroup G), g * c = c * g := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  haveI := H.normal
  have hPC : (P : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
    rwa [inf_eq_right.2 H.centralizer_le]
  obtain ⟨c, hc, hcp, hcc⟩ := RankFourTheoremC.Nongeneration.exists_central_orderOf P
    (N := Subgroup.centralizer (K : Set G)) hPC
  obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.1 hc
  refine ⟨c, hcP, hcC, fun hcK => ?_, hcp, hcc⟩
  have hmem : (⟨c, hcK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hcC g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  have hc1 : c = 1 := congrArg Subtype.val hmem
  rw [hc1, orderOf_one] at hcp
  exact H.prime.one_lt.ne hcp

theorem Hyp.threeOne_centralizer_two
    (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hZ : Subgroup.center K = ⊥)
    (hC : Subgroup.centralizer (K : Set G) ≠ ⊥) (h2 : 2 ≤ Open.pRank p (⊤ : Subgroup K)) :
    OnThreeOneList p K := by
  have hp := H.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := H.normal
  obtain ⟨hsimple, hnonab, hcat⟩ := H.isCatalogGroup hZ
  obtain ⟨c, hcP, hcC, hcK, hcp, -⟩ := Hyp.exists_central_of_ne_bot H hZ hC
  set T := CFSG.QuasiDihedralFusion.sylowInfNormal P K
  have hTP : (T : Subgroup K).map K.subtype ≤ P := by
    rw [CFSG.QuasiDihedralFusion.sylowInfNormal_coe, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hT2 : 2 ≤ Open.pRank p (T : Subgroup K) := by
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp T]
    exact h2
  have hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤ := fun hΓ =>
    hnot (le_weakCore_of_gammaOne hp hcP hcC hcK hcp T hTP hT2 hΓ)
  have hTnc := RankFourTheoremC.Nongeneration.not_isCyclic_sylow_of_two_le_pRank h2 T
  by_cases hle : Open.pRank p (⊤ : Subgroup K) ≤ 2
  · exact onThreeOneList_of_isSmallStrongP hp H.ne_two
      (UniquenessCase.UCK.kFactSmallIdent_holds _ hsimple hnonab hcat p hp H.ne_two T hTnc hΓ
        ((RankFourTheoremC.Nongeneration.pRank_top_subgroup_top hp).trans_le hle))
  · refine onThreeOneList_of_oneLie (UniquenessCase.UCK.kFactOneLieIdent_holds _ hsimple hnonab
      hcat p hp H.ne_two T hTnc hΓ fun h => hle ?_)
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt _
      (RankFourTheoremC.Nongeneration.conj_injective_of_center_eq_bot hZ)).trans h

theorem Hyp.threeOne_centralizer_one
    (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hZ : Subgroup.center K = ⊥)
    (hC : Subgroup.centralizer (K : Set G) ≠ ⊥) (h1 : Open.pRank p (⊤ : Subgroup K) ≤ 1) :
    OnThreeOneList p K := by
  have hp := H.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := H.normal
  have hperf : commutator ↥K = ⊤ := H.quasi.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := H.quasi.2
  have hnonab := RankFourTheoremC.Nongeneration.exists_noncomm_center_quotient hperf
  have hcatK : IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    H.catalog K (Subgroup.center ↥K) inferInstance H.quasi.2 hnonab
  have eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center ↥K) := by
    rw [hZ, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hrk1 : Open.pRank p (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤ 1 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt eK.toMonoidHom eK.injective).trans h1
  obtain ⟨c, hcP, hcC, -, hcp, hcc⟩ := Hyp.exists_central_of_ne_bot H hZ hC
  obtain ⟨A, hAP, hAel, hAcard⟩ :=
    GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp (H := (P : Subgroup G)) (k := 3) h3
  have hcen : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    H.card_le_of_le_centralizer hnot hZ (inf_le_left.trans hAP) inf_le_right
      (hAel.mono inf_le_left)
  obtain ⟨F, hFel, hFcard, hFnot, hFA⟩ :=
    RankFourTheoremC.Nongeneration.exists_outer_plane hperf hAel hAcard hcen hrk1
  have hA3 : 3 ≤ Open.pRank p (A ⊔ Subgroup.zpowers c) :=
    GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_sup_left hAel hAcard
  have hgen : Subgroup.closure
      {kb : ↥K ⧸ Subgroup.center ↥K | ∃ e ∈ F, e ≠ 1 ∧ e kb = kb} ≠ ⊤ := fun hgen =>
    hnot (le_weakCore_of_closure_fixed hperf hZ' hAP hAel hcP hcC hcp (fun a ha => hcc a (hAP ha))
      hA3 hFA hgen)
  have hpdvd : p ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Nat.card_congr eK.toEquiv]
    exact Hyp.prime_dvd_card H
  obtain ⟨T⟩ : Nonempty (Sylow p (↥K ⧸ Subgroup.center ↥K)) := inferInstance
  have hTcyc := RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one H.ne_two hrk1 T
  exact (onThreeOneList_of_isCaseTwoGroup
    (kFactSeitzCyc_of_seitz CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds _ inferInstance
      hnonab hcatK p hp H.ne_two T (Sylow.ne_bot_of_dvd_card T hpdvd) hTcyc F hFel hFcard hFnot
      hgen)).of_mulEquiv eK.symm

theorem Hyp.threeOne_of_centralizer_ne_bot
    (H : Hyp p K P E)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup G)) (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G))
    (hZ : Subgroup.center K = ⊥) (hC : Subgroup.centralizer (K : Set G) ≠ ⊥) :
    OnThreeOneList p K := by
  by_cases h2 : 2 ≤ Open.pRank p (⊤ : Subgroup K)
  · exact H.threeOne_centralizer_two h3 hnot hZ hC h2
  · exact H.threeOne_centralizer_one h3 hnot hZ hC (by omega)

end CentralizerCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
