module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneDisc
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveOfRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace RankOne

def centModTwo (J : Subgroup G) : Subgroup G where
  carrier := {b | b ∈ Subgroup.normalizer (J : Set G) ∧
    ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp [(pCoreOf 2 J).one_mem]⟩
  mul_mem' := by
    rintro b c ⟨hb, hbJ⟩ ⟨hc, hcJ⟩
    refine ⟨Subgroup.mul_mem _ hb hc, fun x hx => ?_⟩
    have hbO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hb
    have h1 := (Subgroup.mem_normalizer_iff.mp hbO _).mp (hcJ x hx)
    have e : b * c * x * (b * c)⁻¹ * x⁻¹ =
        b * (c * x * c⁻¹ * x⁻¹) * b⁻¹ * (b * x * b⁻¹ * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 J).mul_mem h1 (hbJ x hx)
  inv_mem' := by
    rintro b ⟨hb, hbJ⟩
    refine ⟨Subgroup.inv_mem _ hb, fun x hx => ?_⟩
    have hy : b⁻¹ * x * b ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) x).mp hx
      simpa using this
    have h1 := hbJ _ hy
    have e : b * (b⁻¹ * x * b) * b⁻¹ * (b⁻¹ * x * b)⁻¹ = (b⁻¹ * x * b⁻¹⁻¹ * x⁻¹)⁻¹ := by group
    rw [e] at h1
    exact inv_inv (b⁻¹ * x * b⁻¹⁻¹ * x⁻¹) ▸ (pCoreOf 2 J).inv_mem h1

theorem mem_centModTwo {J : Subgroup G} {b : G} (hb : b ∈ Subgroup.normalizer (J : Set G))
    (hbJ : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) : b ∈ centModTwo J := ⟨hb, hbJ⟩

theorem comm_of_mem_centModTwo {J : Subgroup G} {b : G} (hb : b ∈ centModTwo J) :
    ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J := hb.2

theorem le_normalizer_inf {H M L : Subgroup G} (hML : M ≤ Subgroup.normalizer (L : Set G)) :
    H ⊓ M ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun b hb => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hb.1) y
  have h2 := Subgroup.mem_normalizer_iff.mp (hML hb.2) y
  exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩

theorem pow_inv_mul_mem {X Y : Subgroup G} (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    {u a : G} (hu : u ∈ X) (ha : a ∈ Y) {n : ℕ} (han : a ^ n ∈ X) : (u⁻¹ * a) ^ n ∈ X := by
  let u' : Y := ⟨u, hXY hu⟩
  let a' : Y := ⟨a, ha⟩
  have hu' : (QuotientGroup.mk (s := X.subgroupOf Y) u' : Y ⧸ X.subgroupOf Y) = 1 :=
    (QuotientGroup.eq_one_iff u').mpr (Subgroup.mem_subgroupOf.mpr hu)
  have han' : a' ^ n ∈ X.subgroupOf Y := Subgroup.mem_subgroupOf.mpr (by simpa using han)
  have h : ((u'⁻¹ * a') ^ n : Y) ∈ X.subgroupOf Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hu', inv_one, one_mul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact han'
  simpa using Subgroup.mem_subgroupOf.mp h

theorem exists_conj_le_of_maximal {p : ℕ} [Fact p.Prime] {Y W S : Subgroup G} (hWY : W ≤ Y)
    (hW : IsPGroup p W) (hmax : ∀ W' : Subgroup G, IsPGroup p W' → W' ≤ Y → W ≤ W' → W' = W)
    (hSY : S ≤ Y) (hS : IsPGroup p S) : ∃ h ∈ Y, ∀ s ∈ S, h * s * h⁻¹ ∈ W := by
  obtain ⟨Q, hQ⟩ := (hW.comap_subtype (K := Y)).exists_le_sylow
  have hQW : (Q : Subgroup Y).map Y.subtype = W := by
    refine hmax _ (Q.isPGroup'.map _) (Subgroup.map_subtype_le _) fun w hw => ?_
    exact ⟨⟨w, hWY hw⟩, hQ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  obtain ⟨Q', hQ'⟩ := (hS.comap_subtype (K := Y)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y Q' Q
  refine ⟨c, c.2, fun s hs => ?_⟩
  have h1 : (⟨s, hSY hs⟩ : Y) ∈ (Q' : Subgroup Y) := hQ' (Subgroup.mem_subgroupOf.mpr hs)
  have h2 : c * (⟨s, hSY hs⟩ : Y) * c⁻¹ ∈ (Q : Subgroup Y) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact ⟨_, h1, rfl⟩
  rw [← hQW]
  exact ⟨_, h2, rfl⟩

theorem index_ne_three_alt (N : Subgroup (alternatingGroup (Fin 10))) [hN : N.Normal] :
    N.index ≠ 3 := by
  intro h3
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot, nat_card_alternatingGroup, Nat.card_fin] at h3
    revert h3
    decide
  · rw [h, Subgroup.index_top] at h3
    omega

theorem index_ne_three_perm (N : Subgroup (Equiv.Perm (Fin 10))) [hN : N.Normal] :
    N.index ≠ 3 := by
  intro h3
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (N.subgroupOf (alternatingGroup (Fin 10))).Normal).eq_bot_or_eq_top
    with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    have hinj : Function.Injective (Equiv.Perm.sign.comp N.subtype) := by
      rw [injective_iff_map_eq_one]
      intro n hn
      have hnA : (n : Equiv.Perm (Fin 10)) ∈ alternatingGroup (Fin 10) := hn
      have : (n : Equiv.Perm (Fin 10)) ∈ N ⊓ alternatingGroup (Fin 10) := ⟨n.2, hnA⟩
      rw [h.eq_bot] at this
      exact Subtype.ext this
    have hcard : Nat.card N ≤ 2 := by
      have := Nat.card_le_card_of_injective _ hinj
      simpa [Nat.card_eq_fintype_card, Fintype.card_units_int] using this
    have hmul := Subgroup.card_mul_index N
    rw [h3, Nat.card_perm, Nat.card_fin] at hmul
    have : (10 : ℕ).factorial = 3628800 := by decide
    omega
  · rw [Subgroup.subgroupOf_eq_top] at h
    have hd := Subgroup.index_dvd_of_le h
    rw [alternatingGroup.index_eq_two, h3] at hd
    omega

theorem not_hasNormalIndex_three {M : Subgroup G}
    (h : Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* alternatingGroup (Fin 10)) ∨
      Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* Equiv.Perm (Fin 10))) :
    ¬ HasNormalIndex M 3 := by
  rintro ⟨N, -, hNn, hNi⟩
  have key : ∀ N₀ : Subgroup (M ⧸ primeComplementCore (G := M) 3), N₀.Normal →
      N₀.index ≠ 3 := by
    intro N₀ hN₀
    rcases h with h | h
    · obtain ⟨e⟩ := h
      have h2 := Subgroup.index_map_equiv N₀ e
      haveI := hN₀.map
        (e : M ⧸ primeComplementCore (G := M) 3 →* alternatingGroup (Fin 10)) e.surjective
      exact h2 ▸ index_ne_three_alt _
    · obtain ⟨e⟩ := h
      have h2 := Subgroup.index_map_equiv N₀ e
      haveI := hN₀.map
        (e : M ⧸ primeComplementCore (G := M) 3 →* Equiv.Perm (Fin 10)) e.surjective
      exact h2 ▸ index_ne_three_perm _
  set O := primeComplementCore (G := M) 3 with hO
  set N' := N.subgroupOf M with hN'
  have hq := QuotientGroup.mk'_surjective O
  haveI : (N'.map (QuotientGroup.mk' O)).Normal := hNn.map _ hq
  have hdvd : (N'.map (QuotientGroup.mk' O)).index ∣ 3 := by
    have := Subgroup.index_map_dvd N' hq
    rwa [hNi] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · rw [Subgroup.index_eq_one] at h1
    have htop : O ⊔ N' = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' O)) h1
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top, sup_comm] at this
    have hrel := Subgroup.relIndex_sup_right (H := O) (K := N')
    rw [htop, Subgroup.relIndex_top_right, hNi] at hrel
    have hd : 3 ∣ Nat.card O := hrel ▸ Subgroup.index_dvd_card (N'.subgroupOf O)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (primeComplementCore_coprime (G := M) 3) hd
  · exact key _ inferInstance h3

end RankOne

variable {p : ℕ} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
  {W : Subgroup G} {y z : G}

theorem RankOneSylowData.z_mem_jZero [Fact p.Prime] (hW : RankOneSylowData p M H Q K W y z)
    {L : Subgroup G} (hML : M ≤ Subgroup.normalizer (L : Set G)) (hLM : L ≤ M)
    (hJX : jZero H L ≤ d1PlusCore p H K) (hpJ : p ∣ Nat.card (jZero H L)) :
    z ∈ jZero H L := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := jZero H L) p hpJ
  have hJHM : jZero H L ≤ H ⊓ M := (jZero_le H L).trans (inf_le_inf_left _ hLM)
  have hS : IsPGroup p (Subgroup.zpowers (g : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, pow_one])
  obtain ⟨h, hh, hconj⟩ := RankOne.exists_conj_le_of_maximal hW.le hW.pgroup
    (fun W' h1 h2 h3 => hW.max W' h1 (h2.trans inf_le_left) h3)
    ((Subgroup.zpowers_le.mpr (hJHM g.2))) hS
  have hg'W : h * g * h⁻¹ ∈ W := hconj g (Subgroup.mem_zpowers _)
  have hg'J : h * (g : G) * h⁻¹ ∈ jZero H L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_jZero H L
      (RankOne.le_normalizer_inf hML hh)) g).mp g.2
  have hg'1 : h * (g : G) * h⁻¹ ≠ 1 := by
    intro h1
    have : (g : G) = 1 := by
      have := congrArg (fun t => h⁻¹ * t * h) h1
      simpa [mul_assoc] using this
    have hg1 : g = 1 := Subtype.ext this
    rw [hg1, orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg
  haveI := hW.cyclic
  have hgp : (g : G) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hpow : ∃ k : ℕ, (h * (g : G) * h⁻¹) ^ (p ^ k) = 1 :=
    ⟨1, by rw [pow_one, conj_pow, hgp, mul_one, mul_inv_cancel]⟩
  have hz := mem_zpowers_of_isCyclic_of_orderOf_eq (A := W ⊓ d1PlusCore p H K) hW.z_mem
    ⟨hg'W, hJX hg'J⟩ hW.z_order hg'1 hpow
  exact (Subgroup.zpowers_le.mpr hg'J) hz

theorem RankOneSylowData.elevenNine (hS : Setting G) {P : Sylow p G}
    (hd : AGL81CfgData p P M H Q K) (hshape : IsCaseTwoGroup p ↥K)
    (hW : RankOneSylowData p M H Q K W y z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hJX : jZero H L ≤ d1PlusCore p H K) (hpJ : p ∣ Nat.card (jZero H L))
    (hz2 : ¬ ∀ x ∈ jZero H L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (hFA : AGL81ElevenNineFieldAut G) (h82 : AGL81EightTwo G) (h1011 : AGL81TenElevenOneDisc G)
    (h416 : AGL81FourSixteenAt G) :
    ∃ a ∈ W, orderOf a = p ∧ a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K ∧
      ∀ x ∈ jZero H L, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hzJ := hW.z_mem_jZero hML hL.le hJX hpJ
  have hWJ : W ≤ Subgroup.normalizer (jZero H L : Set G) :=
    hW.le.trans ((RankOne.le_normalizer_inf hML).trans (le_normalizer_jZero H L))
  by_contra hno
  push Not at hno
  obtain ⟨a₀, ha₀W, ha₀p, ha₀o⟩ := hW.outer
  have hns : ¬ ∀ g ∈ Subgroup.zpowers a₀ ⊔ (W ⊓ jZero H L), ∃ u ∈ W ⊓ jZero H L,
      ∀ j ∈ jZero H L, ⁅u⁻¹ * g, j⁆ ∈ pCoreOf 2 (jZero H L) := by
    intro hsplit
    obtain ⟨u, ⟨huW, huJ⟩, hcu⟩ :=
      hsplit a₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a₀))
    have ha₁W : u⁻¹ * a₀ ∈ W := W.mul_mem (W.inv_mem huW) ha₀W
    have ha₁c : ∀ x ∈ jZero H L,
        u⁻¹ * a₀ * x * (u⁻¹ * a₀)⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := fun x hx => by
      have := hcu x hx
      rwa [commutatorElement_def] at this
    have ha₁o : u⁻¹ * a₀ ∉ hyp111Pre p H K ⊔ d1PlusCore p H K := fun h => ha₀o (by
      have e : a₀ = u * (u⁻¹ * a₀) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hJX huJ)) h)
    have ha₁C : u⁻¹ * a₀ ∈ RankOne.centModTwo (jZero H L) :=
      RankOne.mem_centModTwo (hWJ ha₁W) ha₁c
    have hnorm : ((W ⊓ jZero H L).subgroupOf W).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine ⟨W.mul_mem (W.mul_mem g.2 hn.1) (W.inv_mem g.2), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hWJ g.2) _).mp hn.2⟩
    have hpow : (u⁻¹ * a₀) ^ p ∈ W ⊓ jZero H L :=
      RankOne.pow_inv_mul_mem inf_le_left hnorm ⟨huW, huJ⟩ ha₀W
        (by rw [← ha₀p, pow_orderOf_eq_one]; exact Subgroup.one_mem _)
    have ha₁p : (u⁻¹ * a₀) ^ p = 1 := by
      by_contra hne
      haveI := hW.cyclic
      obtain ⟨k, hk⟩ := hW.pgroup ⟨_, hpow.1⟩
      have hzpow := mem_zpowers_of_isCyclic_of_orderOf_eq (A := W ⊓ d1PlusCore p H K)
        hW.z_mem ⟨hpow.1, hJX hpow.2⟩ hW.z_order hne ⟨k, congrArg Subtype.val hk⟩
      have hzC : z ∈ RankOne.centModTwo (jZero H L) :=
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ ha₁C p)) hzpow
      exact hz2 (RankOne.comm_of_mem_centModTwo hzC)
    have ha₁1 : u⁻¹ * a₀ ≠ 1 := fun h => ha₁o (h ▸ Subgroup.one_mem _)
    obtain ⟨x, hx, hnx⟩ := hno _ ha₁W (orderOf_eq_prime ha₁p ha₁1) ha₁o
    exact hnx (ha₁c x hx)
  have hshape' : (p = 3 ∧ IsLieOver ↥K (.A 1) 2 3) ∨ (p = 5 ∧ IsSzThirtyTwo ↥K) := by
    obtain ⟨d, hdI, he⟩ := hshape
    rcases hdI with ⟨hp3, hq⟩ | ⟨hp5, hs⟩
    · exact Or.inl ⟨hp3, d, hq, he⟩
    · exact Or.inr ⟨hp5, d, hs, he⟩
  have hdata : AGL81ElevenNineData p P M H Q K L W a₀ :=
    { data := hd
      shape := hshape'
      block := hL
      normal := hML
      j0_le := hJX
      dvd := hpJ
      sylow := ⟨hW.pgroup, hW.le, fun W' h1 h2 h3 => hW.max W' h1 (h2.trans inf_le_left) h3⟩
      mem := ha₀W
      order := ha₀p
      outer := ha₀o
      not_split := hns }
  have hNI := hFA hS p P M H Q K L W a₀ hdata
  rcases hshape' with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rcases hdata.tenElevenOne hS h1011 P hesc.sylow_le hNI with hΓ | hA
    · exact (h82 hS 3 P M H₁ R₁ hesc hΓ).2 hNI
    · exact RankOne.not_hasNormalIndex_three hA hNI
  · have hrk : Open.pRank 5 (Subgroup.centralizer ({z} : Set G) ⊓ M) ≤ 3 :=
      ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 5 (by norm_num) inf_le_right).trans
        (local_pRank_le_evenRank 5 (by norm_num) (by norm_num) M hesc.maxTwoLocal_M.1)).trans
        hS.rank.le
    have h25 := fun D hDM hDe hDc =>
      h416 hS P M H Q K L W a₀ z hdata ⟨hW.z_mem.1, hzJ⟩ hW.z_order hrk D hDM hDe hDc
    have hΓ := agl81ElevenNineGammaFive hS P M H Q K L W a₀ hdata h25 P hesc.sylow_le
    exact (h82 hS 5 P M H₁ R₁ hesc hΓ).2 hNI

end CFSG.LocalAnalysis.RankThreeTheoremC
