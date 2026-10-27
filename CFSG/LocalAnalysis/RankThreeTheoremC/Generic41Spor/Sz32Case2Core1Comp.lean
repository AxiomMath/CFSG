module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (CentSeries)

theorem szh1c_mem_normalizer_of_pow_coprime {Y : Type*} [Group Y] {H : Subgroup Y} {y : Y} {n : ℕ}
    (hy : y ^ n = 1) {m : ℕ} (hm : Nat.Coprime m n) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hn
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using hym
    · have hy1 : y = 1 := by simpa using hy
      subst hy1
      exact one_mem _

theorem szh1c_pow_mul_mem_of_conj_mem {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) (n : Y) (hn : n ∈ N) (m : ℕ) :
    ∃ n' ∈ N, (a * n) ^ m = a ^ m * n' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨a⁻¹ * n' * a * n, N.mul_mem (ha n' hn') hn, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem szh1c_pow_mul_mem_of_pow_eq_one {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) {m : ℕ} (hm : a ^ m = 1) (n : Y) (hn : n ∈ N) :
    (a * n) ^ m ∈ N := by
  obtain ⟨n', hn', h⟩ := szh1c_pow_mul_mem_of_conj_mem ha n hn m
  rw [h, hm, one_mul]
  exact hn'

theorem szh1c_not_isPGroup_quotient_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hc : commutator G = ⊤)
    [hs : IsSimpleGroup (G ⧸ Subgroup.center G)] :
    ¬ IsPGroup p (G ⧸ Subgroup.center G) := by
  intro hpg
  have hbot : (⊥ : Subgroup (G ⧸ Subgroup.center G)) < Subgroup.center (G ⧸ Subgroup.center G) :=
    hpg.bot_lt_center
  have htop : Subgroup.center (G ⧸ Subgroup.center G) = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G))).resolve_left hbot.ne'
  have hcomm_bot : commutator (G ⧸ Subgroup.center G) = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top _).mpr htop
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (Subgroup.center G) : G →* G ⧸ Subgroup.center G) :=
    QuotientGroup.mk'_surjective _
  have key : (commutator G).map (QuotientGroup.mk' (Subgroup.center G)) =
      commutator (G ⧸ Subgroup.center G) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, _root_.commutator_def]
  have hcomm_top : commutator (G ⧸ Subgroup.center G) = ⊤ := by
    rw [← key, hc]
    exact Subgroup.map_top_of_surjective _ hsurj
  have h1 : (⊤ : Subgroup (G ⧸ Subgroup.center G)) = ⊥ := hcomm_top.symm.trans hcomm_bot
  obtain ⟨z, hz⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
  have hz' : z ∈ (⊥ : Subgroup (G ⧸ Subgroup.center G)) := by
    rw [← h1]
    exact Subgroup.mem_top z
  exact hz (Subgroup.mem_bot.mp hz')

variable {Y : Type} [Group Y] [Finite Y]

theorem szh1_mem_normalizer_of_pElement
    (hcore : primeComplementCore (G := Y) 5 = ⊥) (hrank : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 3)
    {g : Y} (hg : ∃ k : ℕ, g ^ (5 ^ k) = 1) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    g ∈ Subgroup.normalizer (L : Set Y) := by
  classical
  obtain ⟨k, hk⟩ := hg
  by_contra hyL
  set f : ℕ → Subgroup Y := fun i => L.map (MulAut.conj (g ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (g ^ i)) L).mpr hL
  have hinj : Set.InjOn f (Finset.range 4 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 4 → f i ≠ f j := by
      intro i j hij hj hfij
      apply hyL
      refine szh1c_mem_normalizer_of_pow_coprime hk (m := j - i) ?_ ?_
      · have hcop : Nat.Coprime (j - i) 5 :=
          (Nat.coprime_of_lt_prime (by omega) (by omega) Nat.prime_five).symm
        exact Nat.Coprime.pow_right k hcop
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : f j = (f (j - i)).map (MulAut.conj (g ^ i)).toMonoidHom := by
          simp only [hf]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hfij
        exact (map_injective (MulAut.conj (g ^ i)).injective hfij).symm
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd hfij (key i j hlt hj)
    · exact heq
    · exact absurd hfij.symm (key j i hlt hi)
  have hcard := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf Nat.prime_five
    (by omega) hcore ((Finset.range 4).image f) (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hfK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  omega

theorem szh1_not_le_of_centSeries
    (hcore : primeComplementCore (G := Y) 5 = ⊥) (S : Sylow 5 Y) {W N : Subgroup Y}
    (hser : CentSeries 5 W (S : Subgroup Y) N) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ¬ L ≤ W := by
  intro hLW
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hS⟩ : ∃ P : Subgroup Y, (S : Subgroup Y) = P := ⟨_, rfl⟩
  rw [hS] at hser
  obtain ⟨t, htmem, hto, htc⟩ :=
    exists_mem_sylow_inf_component Nat.prime_five (by omega) hcore S hL
  rw [hS] at htmem
  obtain ⟨htP, htL⟩ := Subgroup.mem_inf.mp htmem
  have ht_pow : t ^ 5 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto] at this
  have hPp : ∀ a ∈ P, ∃ k : ℕ, a ^ 5 ^ k = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨a, by rw [hS]; exact ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPW : P ≤ W := hser.P_le
  have hPN : P ≤ Subgroup.normalizer N := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hser.N_norm g (hPW hg) n hn
    · intro hn
      have := hser.N_norm g⁻¹ (W.inv_mem (hPW hg)) _ hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this
  have hdecomp : ∀ q ∈ P ⊔ N, ∃ a ∈ P, ∃ n ∈ N, q = a * n := by
    intro q hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P N hPN, Set.mem_mul] at hq
    obtain ⟨a, ha, n, hn, hq'⟩ := hq
    exact ⟨a, ha, n, hn, hq'.symm⟩
  have hconj : ∀ a ∈ P, ∀ n ∈ N, a⁻¹ * n * a ∈ N := by
    intro a ha n hn
    have := hser.N_norm a⁻¹ (W.inv_mem (hPW ha)) n hn
    rwa [inv_inv] at this
  have hPNpow : ∀ q ∈ P ⊔ N, ∃ k : ℕ, q ^ 5 ^ k ∈ N := by
    intro q hq
    obtain ⟨a, ha, n, hn, rfl⟩ := hdecomp q hq
    obtain ⟨k, hk⟩ := hPp a ha
    exact ⟨k, szh1c_pow_mul_mem_of_pow_eq_one (hconj a ha) hk n hn⟩
  obtain ⟨hcomm, hsimp⟩ := hL.2.2
  haveI := hsimp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : L →* L ⧸ Subgroup.center L, ρ = QuotientGroup.mk' (Subgroup.center L) :=
    ⟨_, rfl⟩
  have hρsurj : Function.Surjective ρ := by
    rw [hρ]
    exact QuotientGroup.mk'_surjective _
  have hker : ∀ a : L, ρ a = 1 ↔ a ∈ Subgroup.center L := by
    intro a
    rw [hρ]
    exact QuotientGroup.eq_one_iff a
  have hK₁ : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.N_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  have hK₂ : ((P ⊔ N).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.PN_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t' : L, (t' : Y) = t := ⟨⟨t, htL⟩, rfl⟩
  have ht'_pow : t' ^ 5 = 1 := by
    apply Subtype.ext
    simp [ht', ht_pow]
  have hρt_pow : ρ t' ^ 5 = 1 := by
    rw [← map_pow, ht'_pow, map_one]
  have hρt : ρ t' ≠ 1 := by
    intro h1
    apply htc
    have hcen := Subgroup.mem_center_iff.mp ((hker t').mp h1)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (hcen ⟨l, hl⟩)
    rw [← ht']
    simpa using this
  have htPN : t ∈ P ⊔ N := (le_sup_left : P ≤ P ⊔ N) htP
  haveI hK₁map : ((N.subgroupOf L).map ρ).Normal := hK₁.map ρ hρsurj
  rcases hsimp.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map ρ) with hA₁ | hA₁
  ·
    haveI hK₂map : (((P ⊔ N).subgroupOf L).map ρ).Normal := hK₂.map ρ hρsurj
    have hB : ((P ⊔ N).subgroupOf L).map ρ = ⊤ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (((P ⊔ N).subgroupOf L).map ρ) with hB | hB
      · exfalso
        have hmem : ρ t' ∈ ((P ⊔ N).subgroupOf L).map ρ :=
          Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr (by rw [ht']; exact htPN))
        rw [hB, Subgroup.mem_bot] at hmem
        exact hρt hmem
      · exact hB
    have hPG : IsPGroup 5 (L ⧸ Subgroup.center L) := by
      intro q
      have hq : q ∈ ((P ⊔ N).subgroupOf L).map ρ := by
        rw [hB]
        exact Subgroup.mem_top q
      obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hq
      obtain ⟨k, hk⟩ := hPNpow (ℓ : Y) (Subgroup.mem_subgroupOf.mp hℓ)
      refine ⟨k, ?_⟩
      have hmem : ℓ ^ 5 ^ k ∈ N.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hk
      have h1 : ρ (ℓ ^ 5 ^ k) ∈ (N.subgroupOf L).map ρ := Subgroup.mem_map_of_mem ρ hmem
      rw [hA₁, Subgroup.mem_bot] at h1
      rw [← map_pow]
      exact h1
    exact szh1c_not_isPGroup_quotient_center hcomm hPG
  ·
    have hmem : ρ t' ∈ (N.subgroupOf L).map ρ := by
      rw [hA₁]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hmem
    have hnN : (n : Y) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hkn : n ^ orderOf (n : Y) = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    have hρk : ρ t' ^ orderOf (n : Y) = 1 := by
      rw [← hρn, ← map_pow, hkn, map_one]
    have hgcd : orderOf (ρ t') ∣ Nat.gcd 5 (orderOf (n : Y)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hρt_pow) (orderOf_dvd_of_pow_eq_one hρk)
    have hcop : Nat.gcd 5 (orderOf (n : Y)) = 1 := hser.N_cop (n : Y) hnN
    rw [hcop] at hgcd
    exact hρt (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
