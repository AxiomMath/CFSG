module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Escape

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pRank_quotient_inf_conj_le_two_of_weakCore_le (hp : p.Prime) (P : Sylow p G)
    {M Y : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hP : 3 ≤ Open.pRank p (P : Subgroup G)) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) (hOM : O ≤ (Y ⊓ M).subgroupOf Y) {x : Y ⧸ O}
    (hx : x ∉ ((Y ⊓ M).subgroupOf Y).map (QuotientGroup.mk' O)) :
    Open.pRank p (((Y ⊓ M).subgroupOf Y).map (QuotientGroup.mk' O) ⊓
      GLBConj x (((Y ⊓ M).subgroupOf Y).map (QuotientGroup.mk' O))) ≤ 2 := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hk : (k : G) ∉ M := fun hkM => hx ⟨k, Subgroup.mem_subgroupOf.mpr ⟨k.2, hkM⟩, rfl⟩
  rw [← map_glbConj]
  refine (PreuniquenessRankFour.Helpers.pRank_mono p hp
    (map_inf_map_le_of_ker_le _ (by rwa [QuotientGroup.ker_mk']))).trans ?_
  rw [pRank_map_mk_eq_pRank_map_subtype hp O hO]
  refine (PreuniquenessRankFour.Helpers.pRank_mono p hp ?_).trans
    (escaping_GLBConj_intersection_rank_le_two p hp P hPM hWM hP k hk)
  refine (Subgroup.map_inf_le _ _ _).trans ?_
  rw [map_glbConj, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  exact inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)

theorem reducedNongeneration_of_not_le (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p G)
    {M Y : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hYM : ¬ Y ≤ M) (T : Sylow p Y) (hTP : (T : Subgroup Y).map Y.subtype ≤ P)
    (hTrank : 3 ≤ Open.pRank p ((T : Subgroup Y).map Y.subtype))
    (hcore : GLBPrimeCore p Y ≤ M) :
    ∃ Tbar : Sylow p (Y ⧸ primeComplementCore (G := Y) p),
      (Tbar : Subgroup _) = (T : Subgroup Y).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (Y ⧸ primeComplementCore (G := Y) p) Tbar
        (((Y ⊓ M).subgroupOf Y).map (QuotientGroup.mk' (primeComplementCore p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTY : ((T : Subgroup Y).map Y.subtype).subgroupOf Y = T :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have hO : p.Coprime (Nat.card (primeComplementCore (G := Y) p)) :=
    primeComplementCore_coprime p
  have hOM : primeComplementCore (G := Y) p ≤ (Y ⊓ M).subgroupOf Y := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hcore
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), Sylow.coe_mapSurjective _ _,
    ⟨hp, hp2, primeComplementCore_quotient_eq_bot p, ?_, ?_, ?_, ?_, fun x hx =>
      pRank_quotient_inf_conj_le_two_of_weakCore_le hp P hPM hWM
        (hTrank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp hTP)) _ hO hOM hx⟩⟩
  · rw [Sylow.coe_mapSurjective, pRank_map_mk_eq_pRank_map_subtype hp _ hO]
    exact hTrank
  · have hle := weakCore_map_le_map_inf_of_coprime hp P hWM hTP (Subgroup.map_subtype_le _) _ hO
      hOM
    rwa [hTY] at hle
  ·
    intro E hE hEcard hET F hFE hFidx
    rw [Sylow.coe_mapSurjective] at hET
    obtain ⟨E₁, hE₁T, hE₁map, hE₁, hE₁card⟩ :=
      exists_isElemAbelian_lift hp _ hO T.isPGroup' hE hET
    have hE₁Y : (E₁.map Y.subtype).subgroupOf Y = E₁ :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    have hle := hyperplane_centralizers_map_le_map_inf_of_coprime hp P hWM
      (elementary_abelian_map p hE₁ Y.subtype)
      (by rw [Subgroup.card_map_of_injective Y.subtype_injective, hE₁card, hEcard])
      ((Subgroup.map_mono hE₁T).trans hTP) (Subgroup.map_subtype_le _) _ hO hOM
    rw [hE₁Y, hE₁map] at hle
    exact iSup₂_le_iff.mp hle F ⟨hFE, hFidx⟩
  ·
    intro htop
    apply hYM
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (primeComplementCore (G := Y) p))
      ((Y ⊓ M).subgroupOf Y)
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hcomap
    intro g hg
    have hmem : (⟨g, hg⟩ : Y) ∈ (Y ⊓ M).subgroupOf Y := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2

end Escape

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem pRank_le_one_of_characteristic_isElemAbelian (h : ReducedNongeneration p X R X₀)
    (E : Subgroup (CFSG.pCore p X)) [E.Characteristic] (hE : IsElemAbelian p E) :
    Open.pRank p E ≤ 1 := by
  have hp := h.prime
  have hcard := h.card_le_of_normal_isElemAbelian (elementary_abelian_map p hE
    (CFSG.pCore p X).subtype)
  rw [← pRank_map_of_injective p hp _ (CFSG.pCore p X).subtype_injective]
  obtain ⟨A, hA, -, hAcard⟩ := PreuniquenessRankFour.Helpers.pRank_attained p hp
    (E.map (CFSG.pCore p X).subtype)
  have hle : p ^ Open.pRank p (E.map (CFSG.pCore p X).subtype) ≤ p ^ 1 := by
    rw [← hAcard, pow_one]
    exact (Subgroup.card_le_of_le hA).trans hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

theorem isCyclic_of_characteristic_of_isMulCommutative (h : ReducedNongeneration p X R X₀)
    (A : Subgroup (CFSG.pCore p X)) [A.Characteristic] (hA : IsMulCommutative A) :
    IsCyclic A :=
  no_large_characteristic_elementary_forces_characteristic_abelian_cyclic p h.prime
    CFSG.pCore_isPGroup (fun E hEc hE => by
      have := hEc
      exact h.pRank_le_one_of_characteristic_isElemAbelian E hE) A hA

theorem pRank_le_three_of_layer_eq_bot (h : ReducedNongeneration p X R X₀)
    (hlayer : CFSG.layer X = ⊥) : Open.pRank p (⊤ : Subgroup X) ≤ 3 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hQc : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p h.core_eq_bot hlayer
  obtain ⟨C, hC, hfrat, -, hcent, hcyc, -⟩ :=
    cyclic_characteristic_abelian_pGroup_has_cyclic_critical_quotient p h.ne_two
      CFSG.pCore_isPGroup fun A hAc hA => by
        have := hAc
        exact h.isCyclic_of_characteristic_of_isMulCommutative A hA
  exact pRank_top_le_three_of_critical hp h.ne_two _ CFSG.pCore_isPGroup hQc
    (fun N hN hNp => by
      have := hN
      exact h.pRank_le_two_of_normal_isPGroup hNp) C hC hfrat hcent hcyc

end ReducedNongeneration

theorem layer_ne_bot_of_four_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Sylow p G) {M Y : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hYM : ¬ Y ≤ M) (T : Sylow p Y)
    (hTP : (T : Subgroup Y).map Y.subtype ≤ P)
    (hTrank : 4 ≤ Open.pRank p ((T : Subgroup Y).map Y.subtype))
    (hcore : GLBPrimeCore p Y ≤ M) :
    CFSG.layer (Y ⧸ primeComplementCore (G := Y) p) ≠ ⊥ := by
  intro hlayer
  obtain ⟨Tbar, -, hred⟩ :=
    reducedNongeneration_of_not_le hp hp2 P hPM hWM hYM T hTP (by omega) hcore
  have h3 := hred.pRank_le_three_of_layer_eq_bot hlayer
  have h4 : Open.pRank p ((T : Subgroup Y).map Y.subtype) ≤
      Open.pRank p (⊤ : Subgroup (Y ⧸ primeComplementCore (G := Y) p)) := by
    rw [← pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := Y) p)
      (primeComplementCore_coprime p)]
    exact PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
  omega

end CFSG.AGLEmbedding
