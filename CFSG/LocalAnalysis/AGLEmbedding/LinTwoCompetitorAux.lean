module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {G : Type} [Group G] [Finite G]

theorem inf_glbPrimeCore_le_glbPrimeCore (p : ℕ) {J H' : Subgroup G} (hJH' : J ≤ H') :
    J ⊓ GLBPrimeCore p H' ≤ GLBPrimeCore p J :=
  le_glbPrimeCore inf_le_left
    ((le_inf Subgroup.le_normalizer (hJH'.trans (le_normalizer_glbPrimeCore p H'))).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    ((glbPrimeCore_coprime p H').coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right))

theorem glbPrimeCore_eq_inf_of_le_normalizer (p : ℕ) {J H : Subgroup G} (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    GLBPrimeCore p J = J ⊓ GLBPrimeCore p H := by
  refine le_antisymm (le_inf (glbPrimeCore_le p J) (le_glbPrimeCore
    ((glbPrimeCore_le p J).trans hJH) (hHJ.trans ?_) (glbPrimeCore_coprime p J)))
    (inf_glbPrimeCore_le_glbPrimeCore p hJH)
  have : (primeComplementCore (G := J) p).Characteristic := primeComplementCore_characteristic p
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem glbPrimeCore_nclIn (p : ℕ) (H X : Subgroup G) :
    GLBPrimeCore p (nclIn H X) = nclIn H X ⊓ GLBPrimeCore p H :=
  glbPrimeCore_eq_inf_of_le_normalizer p (nclIn_le_self H X) (le_normalizer_nclIn H X)

omit [Finite G] in
theorem nclIn_le_nclIn_of_le {J H' X : Subgroup G} (hXJ : X ≤ J) (hJH' : J ≤ H') :
    nclIn J X ≤ nclIn H' X :=
  (nclIn_le (le_inf hXJ (le_nclIn (hXJ.trans hJH'))) inf_le_left
    ((le_inf Subgroup.le_normalizer (hJH'.trans (le_normalizer_nclIn H' X))).trans
      Subgroup.inf_normalizer_le_normalizer_inf)).trans inf_le_right

omit [Finite G] in
theorem mem_of_pow_eq_one_of_coprime_relIndex {p : ℕ} {J L : Subgroup G} (hLJ : L ≤ J)
    (hJL : J ≤ Subgroup.normalizer (L : Set G)) (hL : p.Coprime (L.relIndex J)) {g : G}
    (hgJ : g ∈ J) {k : ℕ} (hg : g ^ p ^ k = 1) : g ∈ L := by
  have : (L.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).mpr hJL
  have hxk : (⟨g, hgJ⟩ : J) ^ p ^ k = 1 := Subtype.ext (by simpa using hg)
  have h1 : orderOf ((⟨g, hgJ⟩ : J) : J ⧸ L.subgroupOf J) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one])
  have h2 : orderOf ((⟨g, hgJ⟩ : J) : J ⧸ L.subgroupOf J) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hL.pow_left k) h1 (orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h2
  exact h2

theorem mem_primeComplementCore_iff_mem_glbPrimeCore (p : ℕ) {H : Subgroup G} (h : H) :
    h ∈ primeComplementCore (G := H) p ↔ (h : G) ∈ GLBPrimeCore p H := by
  rw [← glbPrimeCore_subgroupOf, Subgroup.mem_subgroupOf]

theorem mk'_primeComplementCore_eq_one_iff (p : ℕ) {H : Subgroup G} (h : H) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) h = 1 ↔ (h : G) ∈ GLBPrimeCore p H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_primeComplementCore_iff_mem_glbPrimeCore]

omit [Finite G] in
theorem map_nclIn_eq_of {p : ℕ} {H R X : Subgroup G} (hXH : X ≤ H)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal) (hKs : IsSimpleGroup K)
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K)
    (hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K ≠ ⊥) :
    ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      K := by
  have hJK : nclIn H X ≤
      (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype := by
    refine nclIn_le (fun x hx => ⟨⟨x, hXH hx⟩, ?_, rfl⟩) (Subgroup.map_subtype_le _) ?_
    · have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (primeComplementCore (G := H) p))
        (show (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H from hx)
      rw [hXK] at hmem
      exact hmem.2
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hKn.comap _
  have hle : ((nclIn H X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hjj'⟩ := hJK hj
    rwa [← Subtype.ext hjj']
  have hnormal : (((nclIn H X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    (nclIn_normal H X).map _ (QuotientGroup.mk'_surjective _)
  have hne : ((nclIn H X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥ := by
    intro hbot
    have hXle : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXH))
    rw [hbot, le_bot_iff, hXK] at hXle
    exact hRK hXle
  have := hnormal.subgroupOf K
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((((nclIn H X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).subgroupOf K) with hbot | htop
  · exact absurd (le_bot_iff.mp (by
      have hdisj := Subgroup.subgroupOf_eq_bot.mp hbot
      exact (le_inf le_rfl hle).trans (disjoint_iff.mp hdisj).le)) hne
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

theorem nclIn_nclIn_of {p : ℕ} [Fact p.Prime] {H X : Subgroup G} (hXH : X ≤ H)
    (hX : IsPGroup p X)
    (hS : ∃ S : Sylow p (nclIn H X), (S : Subgroup (nclIn H X)) = X.subgroupOf (nclIn H X)) :
    nclIn (nclIn H X) X = nclIn H X := by
  have hXJ : X ≤ nclIn H X := le_nclIn hXH
  refine le_antisymm (nclIn_le_self _ X) ?_
  obtain ⟨S, hSX⟩ := hS
  have hcop : p.Coprime ((nclIn (nclIn H X) X).relIndex (nclIn H X)) := by
    refine ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr fun hdvd => S.not_dvd_index ?_
    rw [hSX]
    exact hdvd.trans (Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex X _ _
      (le_nclIn hXJ) (nclIn_le_self _ X)))
  have hconj : ∀ c ∈ H, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn (nclIn H X) X := by
    intro c hc x hx
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine mem_of_pow_eq_one_of_coprime_relIndex (nclIn_le_self _ X) (le_normalizer_nclIn _ X)
      hcop ((Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc) x).mp (hXJ hx)) (k := k)
      ?_
    rw [conj_pow, hxk, mul_one, mul_inv_cancel]
  rintro _ ⟨y, hy, rfl⟩
  have hcl : Subgroup.normalClosure ((X.subgroupOf H : Subgroup H) : Set H) ≤
      (nclIn (nclIn H X) X).subgroupOf H := by
    show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨b, hb, hbz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hbz
    exact hconj c c.2 b hb
  exact hcl hy

theorem eq_one_of_forall_commutator_mem_of {p : ℕ} [Fact p.Prime] {H R X : Subgroup G}
    (hRH : R ≤ H) (hR : IsPGroup p R) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hJK : ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥) {r : G}
    (hr : r ∈ R) (hc : ∀ j ∈ nclIn H X, r * j * r⁻¹ * j⁻¹ ∈ GLBPrimeCore p H) : r = 1 := by
  have hrH : r ∈ H := hRH hr
  have hcent : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hrH⟩ ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← hJK] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    have h1 := (mk'_primeComplementCore_eq_one_iff p (⟨r, hrH⟩ * j * ⟨r, hrH⟩⁻¹ * j⁻¹ : H)).mpr
      (hc j hj)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hC, Subgroup.mem_bot, mk'_primeComplementCore_eq_one_iff] at hcent
  have hbot := inf_eq_bot_of_isPGroup Fact.out hR (glbPrimeCore_coprime p H)
  have hmem : r ∈ R ⊓ GLBPrimeCore p H := ⟨hr, hcent⟩
  rwa [hbot, Subgroup.mem_bot] at hmem

end General

namespace D1L2Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X : Subgroup G}

theorem le_H (h : D1L2Config p n P M H R X) : X ≤ H := h.le_R.trans h.ext.le_H

theorem isPGroup (h : D1L2Config p n P M H R X) : IsPGroup p X :=
  h.ext.isPGroup.to_le h.le_R

theorem card_map_inf (h : D1L2Config p n P M H R X)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hKe : Nonempty (K ≃* PSL2GF p n)) :
    Nat.card ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ n := by
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  obtain ⟨e⟩ := hKe
  have := hKn
  rw [← hRbar]
  exact (isElemAbelian_sylow_inf_of_psl2GF (by have := h.three_le; omega) e Rbar).2

theorem card_le_of_le_socle (h : D1L2Config p n P M H R X)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hKe : Nonempty (K ≃* PSL2GF p n)) {S : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hS : IsPGroup p S) (hSK : S ≤ K) : Nat.card S ≤ p ^ n := by
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  have := hKn
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rbar
  calc Nat.card S ≤ Nat.card ((T : Subgroup K).map K.subtype) := card_le_card_map_sylow T hS hSK
    _ = p ^ n := by rw [hT, hRbar]; exact h.card_map_inf hKn hKe

theorem card_eq (h : D1L2Config p n P M H R X) : Nat.card X = p ^ n := by
  obtain ⟨K, hKn, hKe, -, hXK⟩ := h.socle
  have hXp : IsPGroup p (X.subgroupOf H) := h.isPGroup.comap_subtype
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_H).toEquiv,
    ← card_map_mk_of_isPGroup Fact.out _ (primeComplementCore_coprime p) hXp, hXK]
  exact h.card_map_inf hKn hKe

theorem map_nclIn_eq (h : D1L2Config p n P M H R X)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hKe : Nonempty (K ≃* PSL2GF p n))
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) :
    ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      K := by
  obtain ⟨e⟩ := hKe
  have : IsSimpleGroup (PSL2GF p n) :=
    isSimpleGroup_psl2GF_of_two_le (by have := h.three_le; omega)
  refine map_nclIn_eq_of h.le_H hKn e.isSimpleGroup hXK fun hbot => ?_
  have hcard := h.card_map_inf hKn ⟨e⟩
  rw [hbot, Subgroup.card_bot] at hcard
  have := Nat.one_lt_pow (by have := h.three_le; omega) (Fact.out : p.Prime).one_lt (n := n)
  omega

theorem card_le_of_le_nclIn (h : D1L2Config p n P M H R X) {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQJ : Q ≤ nclIn H X) : Nat.card Q ≤ p ^ n := by
  obtain ⟨K, hKn, hKe, -, hXK⟩ := h.socle
  have hQH : Q ≤ H := hQJ.trans (nclIn_le_self H X)
  have hQp : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv,
    ← card_map_mk_of_isPGroup Fact.out _ (primeComplementCore_coprime p) hQp]
  refine h.card_le_of_le_socle hKn hKe (hQp.map _) ?_
  rw [← h.map_nclIn_eq hKn hKe hXK]
  exact Subgroup.map_mono (Subgroup.comap_mono hQJ)

theorem exists_sylow_nclIn (h : D1L2Config p n P M H R X) :
    ∃ S : Sylow p (nclIn H X), (S : Subgroup (nclIn H X)) = X.subgroupOf (nclIn H X) := by
  have hXJ : X ≤ nclIn H X := le_nclIn h.le_H
  refine ⟨{ toSubgroup := X.subgroupOf (nclIn H X)
            isPGroup' := h.isPGroup.comap_subtype
            is_maximal' := fun {Q} hQ hXQ => ?_ }, rfl⟩
  have hXQ' : X ≤ Q.map (nclIn H X).subtype := fun x hx =>
    ⟨⟨x, hXJ hx⟩, hXQ (show (⟨x, hXJ hx⟩ : nclIn H X) ∈ X.subgroupOf (nclIn H X) from hx), rfl⟩
  have heq := Subgroup.eq_of_le_of_card_ge hXQ'
    ((h.card_le_of_le_nclIn (hQ.map _) (Subgroup.map_subtype_le _)).trans h.card_eq.ge)
  exact le_antisymm (fun q hq => heq.ge ⟨q, hq, rfl⟩) hXQ

theorem nclIn_nclIn (h : D1L2Config p n P M H R X) : nclIn (nclIn H X) X = nclIn H X :=
  nclIn_nclIn_of h.le_H h.isPGroup h.exists_sylow_nclIn

theorem nclIn_le_nclIn (h : D1L2Config p n P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') : nclIn H X ≤ nclIn H' X := by
  calc nclIn H X = nclIn (nclIn H X) X := h.nclIn_nclIn.symm
    _ ≤ nclIn H' X := nclIn_le_nclIn_of_le (le_nclIn h.le_H) hJH'

theorem eq_one_of_forall_commutator_mem (h : D1L2Config p n P M H R X) {r : G} (hr : r ∈ R)
    (hc : ∀ j ∈ nclIn H X, r * j * r⁻¹ * j⁻¹ ∈ GLBPrimeCore p H) : r = 1 := by
  obtain ⟨K, hKn, hKe, hC, hXK⟩ := h.socle
  exact eq_one_of_forall_commutator_mem_of h.ext.le_H h.ext.isPGroup (h.map_nclIn_eq hKn hKe hXK)
    hC hr hc

end D1L2Config

end CFSG.AGLEmbedding
