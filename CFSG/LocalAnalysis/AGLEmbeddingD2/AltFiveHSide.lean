module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestConj
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtThree
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveThreeRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.Closure
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem pRank_le_map_of_coprime_ker {V W : Type*} [Group V] [Finite V] [Group W] [Finite W]
    {q : ℕ} [hq : Fact q.Prime] (f : V →* W) (hf : ¬ q ∣ Nat.card f.ker) (Y : Subgroup V) :
    Open.pRank q Y ≤ Open.pRank q (Y.map f) := by
  obtain ⟨E, hEY, hE, hcard⟩ := SectionRank.exists_pRank hq.out.one_lt Y
  have hcop : Nat.Coprime (Nat.card E) (Nat.card f.ker) := by
    rw [hcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hf)
  have hdisj : Disjoint E f.ker := Subgroup.disjoint_of_coprime_natCard hcop
  have hinj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 hx)
  have := hE.1
  refine SectionRank.le_pRank_of_injective hq.out.one_lt (A := ↥E) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hcard (f.comp E.subtype) hinj ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x, hEY x.2, rfl⟩

theorem le_pRank_of_alt_section {W : Type*} [Group W] [Finite W] {N : Subgroup W} [N.Normal]
    {n : ℕ} (hn : 9 ≤ n) (K : Subgroup (W ⧸ N)) (e : K ≃* alternatingGroup (Fin n))
    (c : Fin 3 → alternatingGroup (Fin n)) (hc : ∀ i, (c i : Equiv.Perm (Fin n)).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (c i : Equiv.Perm (Fin n)).support (c j : Equiv.Perm (Fin n)).support) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup W) ∧ (3 ∣ Nat.card N → 4 ≤ Open.pRank 3 (⊤ : Subgroup W)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h31 : 1 < 3 := by norm_num
  obtain ⟨T⟩ : Nonempty (Sylow 3 N) := Sylow.nonempty
  set T' : Subgroup W := (T : Subgroup N).map N.subtype with hT'
  by_cases hT3 : Open.pRank 3 T' ≤ 3
  swap
  · have h4 : 4 ≤ Open.pRank 3 (⊤ : Subgroup W) :=
      (by omega : 4 ≤ Open.pRank 3 T').trans (SectionRank.pRank_mono h31 le_top)
    exact ⟨by omega, fun _ => h4⟩
  obtain ⟨L, ψ, hψ, hπ, hLC, U, hU⟩ :=
    AltSevenPrime.exists_central_sylow_cover_centralizer (by omega) K e T hT3
  have hL : ∀ (Z : Subgroup L) (k : ℕ), k ≤ Open.pRank 3 Z → k ≤ Open.pRank 3 (⊤ : Subgroup W) :=
    fun Z k hk => (hk.trans (SectionRank.pRank_le_map h31 L.subtype L.subtype_injective Z)).trans
      (SectionRank.pRank_mono h31 le_top)
  by_cases hU1 : (U : Subgroup ψ.ker) = ⊥
  swap
  · have h4 := hL _ 4 (four_le_pRank_comap_of_central_sylow_three ψ hψ U hU hU1 c hc hdisj)
    exact ⟨by omega, fun _ => h4⟩
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := fun hd => Sylow.ne_bot_of_dvd_card U hd hU1
  have hAn : 3 ≤ Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    three_le_pRank_alternatingGroup Nat.prime_three (by norm_num) (by omega)
  have hL3 : 3 ≤ Open.pRank 3 ((⊤ : Subgroup (alternatingGroup (Fin n))).comap ψ) :=
    hAn.trans (AltSevenPrime.pRank_le_pRank_comap ψ hψ hker3 ⊤)
  refine ⟨hL _ 3 hL3, fun h3N => ?_⟩
  have hTne : (T : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card T h3N
  have h3T : 3 ∣ Nat.card (T : Subgroup N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hTne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 h3T
  set z : W := ((t : N) : W) with hz
  have hzT : z ∈ T' := ⟨t, t.2, rfl⟩
  have hzN : z ∈ N := (t : N).2
  have ht3 : t ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht] at h1
  have hz3 : z ^ 3 = 1 := by
    have h1 : (((t ^ 3 : (T : Subgroup N)) : N) : W) = 1 := by rw [ht3]; rfl
    simpa [hz] using h1
  have hz1 : z ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext (Subtype.ext (by simpa [hz] using h1))
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hzL : z ∈ Subgroup.centralizer (L : Set W) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLC hl) z hzT).symm
  have hdisjz : Subgroup.zpowers z ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxz, hxL⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hxN : z ^ m ∈ N := N.zpow_mem hzN m
    have hxk : (⟨z ^ m, hxL⟩ : L) ∈ ψ.ker := by
      obtain ⟨k, hk1, hk2⟩ := hπ ⟨z ^ m, hxL⟩
      rw [MonoidHom.mem_ker, ← hk2]
      have hk : k = 1 := by
        apply Subtype.ext
        rw [hk1, OneMemClass.coe_one]
        exact (QuotientGroup.eq_one_iff _).mpr hxN
      rw [hk, map_one]
    set y : ψ.ker := ⟨⟨z ^ m, hxL⟩, hxk⟩
    have hy3 : y ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (z ^ m) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · have : y = 1 := orderOf_eq_one_iff.mp h1
      exact Subgroup.mem_bot.mpr (congrArg (fun w : ψ.ker => ((w : L) : W)) this)
    · exact absurd (h1 ▸ orderOf_dvd_natCard y) hker3
  have hLW : 3 ≤ Open.pRank 3 L := by
    have h := SectionRank.pRank_le_map h31 L.subtype L.subtype_injective (⊤ : Subgroup L)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [Subgroup.comap_top] at hL3
    exact hL3.trans h
  have h4 := pRank_succ_le_sup_zpowers L hz3 hz1 hzL hdisjz
  exact ((by omega : 4 ≤ Open.pRank 3 (L ⊔ Subgroup.zpowers z))).trans
    (SectionRank.pRank_mono h31 le_top)

section AltTen

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.pRank_three_H_of_alt (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p)
      Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p) :
    3 ≤ Open.pRank 3 H ∧
      (3 ∣ Nat.card (primeComplementCore (G := H) p) → 4 ≤ Open.pRank 3 H) := by
  obtain ⟨Mo⟩ := hK.nonempty_altModel hp5 e
  obtain ⟨c, hc, hdisj, -⟩ := Mo.exists_three_cycles hp5
  rw [SectionRank.pRank_eq_pRank_top_subgroup H]
  exact le_pRank_of_alt_section (by omega) K e c hc hdisj

theorem D2Escape.not_three_dvd_card_of_alt (h : D2Escape p P M A H A)
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p)
      Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p) (h3 : 3 ∉ GLBBetaFour G) :
    ¬ 3 ∣ Nat.card (primeComplementCore (G := H) p) := by
  intro h3N
  have h4 := (D2Escape.pRank_three_H_of_alt hK e hp5).2 h3N
  exact h3 ⟨Nat.prime_three, by norm_num,
    prime_dvd_card_of_positive_rank 3 Nat.prime_three H (by omega),
    h4.trans (le_csSup (twoLocalRank_bddAbove 3 Nat.prime_three) ⟨H, h.maxTwoLocal_H.1, rfl⟩)⟩

theorem D2Escape.pRank_three_inf_le_two_of_alt_five [Fact p.Prime] (h : D2Escape p P M A H A)
    (hglob : AGLGlobal G) (hD1 : D1For G)
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : p = 5) :
    Open.pRank 3 (H ⊓ M) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair : AGLPair p M H A := (h.altData_of_alt hglob hRbar hK e (by omega)).pair
  by_cases h3 : 3 ∈ GLBBetaFour G
  · exact hpair.pRank_inf_le_two_of_mem_betaFour hD1 h3
  have hN3 := h.not_three_dvd_card_of_alt hK e (by omega) h3
  set N : Subgroup H := primeComplementCore (G := H) p with hN
  have hY : ((H ⊓ M).subgroupOf H).map H.subtype = H ⊓ M := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left inf_le_left
  rw [← hY, pRank_map_of_injective 3 Nat.prime_three H.subtype H.subtype_injective]
  refine (pRank_le_map_of_coprime_ker (QuotientGroup.mk' N) (by rwa [QuotientGroup.ker_mk'])
    ((H ⊓ M).subgroupOf H)).trans ?_
  obtain ⟨Mo⟩ := hK.nonempty_altModel (by omega) e
  subst hp5
  exact Mo.pRank_three_le_two

theorem D2Escape.pRank_three_M_le_two_of_alt (h : D2Escape p P M A H A) (hglob : AGLGlobal G)
    (hD1 : D1For G)
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p) (hβ : p ∈ GLBBetaFour G)
    (h3 : 3 ∈ GLBBetaFour G) : Open.pRank 3 M ≤ 2 := by
  by_contra hlt
  exact h.false_of_three_le_pRank_both hglob.pre hβ h3 (hD1 3 h3)
    (D2Escape.pRank_three_H_of_alt hK e hp5).1 (by omega)

end AltTen

end CFSG.AGLEmbeddingD2
