module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure JStarTargetCard (p a B : ℕ) (L : Type) [Group L] [Finite L] : Prop where
  sylow_card : ∀ S : Sylow p L, Nat.card (S : Subgroup L) = p ^ a
  aut_card_dvd : ∀ S : Subgroup (MulAut L), IsPGroup p S → Nat.card S ∣ B

section Socle

variable {G : Type} [Group G] [Finite G]

structure D1SocleConfig (T : Type) [Group T] (p : ℕ) [Fact p.Prime] (P : Sylow p G)
    (M H R U : Subgroup G) : Prop where
  ext : D1Extremal p P M H R
  glob : CFSG.AGLEmbeddingD2.AGLGlobal G
  le_R : U ≤ R
  socle : ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), K.Normal ∧
    Nonempty (K ≃* T) ∧
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥ ∧
    (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K

theorem D1L2Config.toSocleConfig {p n : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}
    (h : D1L2Config p n P M H R X) : D1SocleConfig (PSL2GF p n) p P M H R X :=
  ⟨h.ext, h.glob, h.le_R, h.socle⟩

end Socle

theorem JStarTargetCard.three_le {T : Type} [Group T] [Finite T] {p a b : ℕ} [Fact p.Prime]
    (hT : JStarTarget p b T) (hTc : JStarTargetCard p a b T) : 3 ≤ a := by
  have hp : p.Prime := Fact.out
  obtain ⟨S⟩ : Nonempty (Sylow p T) := inferInstance
  obtain ⟨E, hES, -, hEcard⟩ := hT.exists_elem_le_sylow S
  have h1 := Subgroup.card_le_of_le hES
  rw [hEcard, hTc.sylow_card S] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1

theorem JStarTargetCard.pos_of_base {T : Type} [Group T] [Finite T] {p a b : ℕ} [Fact p.Prime]
    (hTc : JStarTargetCard p a b T) (hT : JStarTargetBase p b T) : 0 < a := by
  have hp : p.Prime := Fact.out
  have hdvd : p ∣ Nat.card T :=
    prime_dvd_card_of_positive_rank p hp ⊤ (by have := hT.two_le_pRank; omega)
  obtain ⟨S⟩ : Nonempty (Sylow p T) := inferInstance
  have hS := hTc.sylow_card S
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0, pow_zero] at hS
    exact absurd (Subgroup.card_eq_one.mp hS) (S.ne_bot_of_dvd_card hdvd)
  · exact h0

theorem card_inf_of_target {T : Type} [Group T] [Finite T] {p a b : ℕ} [Fact p.Prime]
    (hTc : JStarTargetCard p a b T) {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (e : K ≃* T) (Rb : Sylow p Y) : Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) = p ^ a := by
  obtain ⟨S, hS⟩ := exists_sylow_map_subtype_eq_inf K Rb
  rw [← hS, Subgroup.card_map_of_injective K.subtype_injective]
  have hes : Function.Surjective (e : K →* T) := e.surjective
  have h := hTc.sylow_card (S.mapSurjective hes)
  rw [Sylow.coe_mapSurjective] at h
  rwa [Subgroup.card_map_of_injective (show Function.Injective (e : K →* T) from e.injective)]
    at h

theorem three_le_pRank_inf_of_target {T : Type} [Group T] [Finite T] {p b : ℕ}
    [Fact p.Prime] (hT : JStarTarget p b T) {Y : Type} [Group Y] [Finite Y]
    {K : Subgroup Y} [K.Normal] (e : K ≃* T) (Rb : Sylow p Y) :
    3 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨S, hS⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hes : Function.Surjective (e : K →* T) := e.surjective
  obtain ⟨E, hES, hE, hEcard⟩ := hT.exists_elem_le_sylow (S.mapSurjective hes)
  rw [Sylow.coe_mapSurjective] at hES
  set E' : Subgroup Y := (E.map e.symm.toMonoidHom).map K.subtype
  have hE'le : E' ≤ (Rb : Subgroup Y) ⊓ K := by
    rw [← hS]
    refine Subgroup.map_mono ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hES hy
    have : e.symm.toMonoidHom ((e : K →* T) z) = z := e.symm_apply_apply z
    rw [this]
    exact hz
  have hE' : IsElemAbelian p E' :=
    elementary_abelian_map p (elementary_abelian_map p hE _) _
  have hE'card : Nat.card E' = p ^ 3 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hEcard]
  exact le_csSup (pRank_bddAbove p hp _) ⟨E', hE'le, hE', hE'card⟩

theorem card_dvd_of_isPGroup_of_target {T : Type} [Group T] [Finite T] {p a b : ℕ}
    [Fact p.Prime] (hTc : JStarTargetCard p a b T) {Y : Type} [Group Y] {K : Subgroup Y}
    (hKn : K.Normal) (hK : Nonempty (K ≃* T)) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (A : Subgroup Y) (hA : IsPGroup p A) : Nat.card A ∣ b := by
  obtain ⟨e⟩ := hK
  let f : Y →* MulAut T := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have hf : Function.Injective f := (MulAut.congr e).injective.comp hinj
  have h := hTc.aut_card_dvd (A.map f) (hA.map f)
  rwa [Subgroup.card_map_of_injective hf] at h

namespace D1SocleConfig

variable {G : Type} [Group G] [Finite G] {T : Type} [Group T] [Finite T] {p a b : ℕ}
  [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}

omit [Finite T] in
theorem le_H (h : D1SocleConfig T p P M H R X) : X ≤ H := h.le_R.trans h.ext.le_H

omit [Finite T] in
theorem isPGroup (h : D1SocleConfig T p P M H R X) : IsPGroup p X :=
  h.ext.isPGroup.to_le h.le_R

theorem card_map_inf (h : D1SocleConfig T p P M H R X) (_hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKn : K.Normal) (hKe : Nonempty (K ≃* T)) :
    Nat.card ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ a := by
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  obtain ⟨e⟩ := hKe
  have := hKn
  rw [← hRbar]
  exact card_inf_of_target hTc e Rbar

theorem card_le_of_le_socle (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKn : K.Normal)
    (hKe : Nonempty (K ≃* T)) {S : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hS : IsPGroup p S) (hSK : S ≤ K) : Nat.card S ≤ p ^ a := by
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  have := hKn
  obtain ⟨T', hT'⟩ := exists_sylow_map_subtype_eq_inf K Rbar
  calc Nat.card S ≤ Nat.card ((T' : Subgroup K).map K.subtype) :=
        card_le_card_map_sylow T' hS hSK
    _ = p ^ a := by rw [hT', hRbar]; exact h.card_map_inf hT hTc hKn hKe

theorem card_eq (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) : Nat.card X = p ^ a := by
  obtain ⟨K, hKn, hKe, -, hXK⟩ := h.socle
  have hXp : IsPGroup p (X.subgroupOf H) := h.isPGroup.comap_subtype
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_H).toEquiv,
    ← card_map_mk_of_isPGroup Fact.out _ (primeComplementCore_coprime p) hXp, hXK]
  exact h.card_map_inf hT hTc hKn hKe

theorem map_nclIn_eq (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKn : K.Normal)
    (hKe : Nonempty (K ≃* T))
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) :
    ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      K := by
  obtain ⟨e⟩ := hKe
  have : IsSimpleGroup T := hT.simple
  refine map_nclIn_eq_of h.le_H hKn e.isSimpleGroup hXK fun hbot => ?_
  have hcard := h.card_map_inf hT hTc hKn ⟨e⟩
  rw [hbot, Subgroup.card_bot] at hcard
  have := Nat.one_lt_pow (by have := hTc.pos_of_base hT; omega) (Fact.out : p.Prime).one_lt (n := a)
  omega

theorem card_le_of_le_nclIn (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQJ : Q ≤ nclIn H X) : Nat.card Q ≤ p ^ a := by
  obtain ⟨K, hKn, hKe, -, hXK⟩ := h.socle
  have hQH : Q ≤ H := hQJ.trans (nclIn_le_self H X)
  have hQp : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv,
    ← card_map_mk_of_isPGroup Fact.out _ (primeComplementCore_coprime p) hQp]
  refine h.card_le_of_le_socle hT hTc hKn hKe (hQp.map _) ?_
  rw [← h.map_nclIn_eq hT hTc hKn hKe hXK]
  exact Subgroup.map_mono (Subgroup.comap_mono hQJ)

theorem exists_sylow_nclIn (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) :
    ∃ S : Sylow p (nclIn H X), (S : Subgroup (nclIn H X)) = X.subgroupOf (nclIn H X) := by
  have hXJ : X ≤ nclIn H X := le_nclIn h.le_H
  refine ⟨{ toSubgroup := X.subgroupOf (nclIn H X)
            isPGroup' := h.isPGroup.comap_subtype
            is_maximal' := fun {Q} hQ hXQ => ?_ }, rfl⟩
  have hXQ' : X ≤ Q.map (nclIn H X).subtype := fun x hx =>
    ⟨⟨x, hXJ hx⟩, hXQ (show (⟨x, hXJ hx⟩ : nclIn H X) ∈ X.subgroupOf (nclIn H X) from hx), rfl⟩
  have heq := Subgroup.eq_of_le_of_card_ge hXQ'
    ((h.card_le_of_le_nclIn hT hTc (hQ.map _) (Subgroup.map_subtype_le _)).trans
      (h.card_eq hT hTc).ge)
  exact le_antisymm (fun q hq => heq.ge ⟨q, hq, rfl⟩) hXQ

theorem nclIn_nclIn (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) : nclIn (nclIn H X) X = nclIn H X :=
  nclIn_nclIn_of h.le_H h.isPGroup (h.exists_sylow_nclIn hT hTc)

theorem nclIn_le_nclIn (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    nclIn H X ≤ nclIn H' X := by
  calc nclIn H X = nclIn (nclIn H X) X := (h.nclIn_nclIn hT hTc).symm
    _ ≤ nclIn H' X := nclIn_le_nclIn_of_le (le_nclIn h.le_H) hJH'

theorem eq_one_of_forall_commutator_mem (h : D1SocleConfig T p P M H R X)
    (hT : JStarTargetBase p b T) (hTc : JStarTargetCard p a b T) {r : G} (hr : r ∈ R)
    (hc : ∀ j ∈ nclIn H X, r * j * r⁻¹ * j⁻¹ ∈ GLBPrimeCore p H) : r = 1 := by
  obtain ⟨K, hKn, hKe, hC, hXK⟩ := h.socle
  exact eq_one_of_forall_commutator_mem_of h.ext.le_H h.ext.isPGroup
    (h.map_nclIn_eq hT hTc hKn hKe hXK) hC hr hc

end D1SocleConfig

end CFSG.AGLEmbedding
