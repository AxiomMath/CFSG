module

public import CFSG.LocalAnalysis.AGLEmbedding.Escape
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

structure D1Extremal {G : Type*} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) : Prop extends D1Escape p P M H R where
  extremal : ∀ H' : Subgroup G, IsTwoLocal H' → ¬ H' ≤ M → 3 ≤ pRank p (H' ⊓ M) →
    ∀ X : Subgroup G, X ≤ H' ⊓ M → IsPGroup p X → Nat.card X ≤ Nat.card R
  extremal3 : ∀ H' : Subgroup G, IsTwoLocal H' → ¬ H' ≤ M → 3 ≤ pRank p (H' ⊓ M) →
    ∀ X : Subgroup G, X ≤ H' ⊓ M → IsPGroup p X → Nat.card X = Nat.card R →
      pRank p X ≤ pRank p R

variable {G : Type*} [Group G] [Finite G]

theorem D1Escape.isPGroup {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Escape p P M H R) : IsPGroup p R := by
  obtain ⟨T, rfl⟩ := h.isSylow
  exact T.isPGroup'.map H.subtype

theorem card_le_card_map_sylow {p : ℕ} [Fact p.Prime] {K X : Subgroup G} (T : Sylow p K)
    (hX : IsPGroup p X) (hXK : X ≤ K) :
    Nat.card X ≤ Nat.card ((T : Subgroup K).map K.subtype) := by
  obtain ⟨T', hT'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  have hle : X ≤ (T' : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXK]
    exact Subgroup.map_mono hT'
  rw [Subgroup.card_map_of_injective K.subtype_injective, T.card_eq_multiplicity,
    ← T'.card_eq_multiplicity, ← Subgroup.card_map_of_injective K.subtype_injective]
  exact Subgroup.card_le_of_le hle

namespace D1Extremal

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem le_of_card_lt (h : D1Extremal p P M H R) {X H' : Subgroup G} (hXM : X ≤ M)
    (hX : IsPGroup p X) (hXrank : 3 ≤ pRank p X) (hXR : Nat.card R < Nat.card X)
    (hH' : IsTwoLocal H') (hXH' : X ≤ H') : H' ≤ M := by
  by_contra hH'M
  have hXinf : X ≤ H' ⊓ M := le_inf hXH' hXM
  exact (h.extremal H' hH' hH'M (hXrank.trans (pRank_mono p h.prime hXinf)) X hXinf
    hX).not_gt hXR

theorem le_of_card_le_of_pRank_lt (h : D1Extremal p P M H R) {X H' : Subgroup G}
    (hXM : X ≤ M) (hX : IsPGroup p X) (hXR : Nat.card R ≤ Nat.card X)
    (hrk : pRank p R < pRank p X) (hH' : IsTwoLocal H') (hXH' : X ≤ H') : H' ≤ M := by
  rcases hXR.lt_or_eq with hlt | heq
  · exact h.le_of_card_lt hXM hX (h.three_le_pRank.trans hrk.le) hlt hH' hXH'
  · by_contra hH'M
    have hXinf : X ≤ H' ⊓ M := le_inf hXH' hXM
    exact (h.extremal3 H' hH' hH'M ((h.three_le_pRank.trans hrk.le).trans
      (pRank_mono p h.prime hXinf)) X hXinf hX heq.symm).not_gt hrk

theorem le_of_sylow_le (h : D1Extremal p P M H R) (hRP : R ≠ (P : Subgroup G))
    {H' : Subgroup G} (hH' : IsTwoLocal H') (hPH' : (P : Subgroup G) ≤ H') : H' ≤ M :=
  h.le_of_card_lt h.sylow_le P.isPGroup' (h.three_le_pRank.trans (pRank_mono p h.prime h.le_P))
    (Subgroup.card_lt_of_lt (lt_of_le_of_ne h.le_P hRP)) hH' hPH'

theorem normalizer_le_of_sylow_le (h : D1Extremal p P M H R)
    (hRP : R ≠ (P : Subgroup G)) {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hPT : (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  h.le_of_sylow_le hRP ⟨T, hT1, hT, rfl⟩ hPT

end D1Extremal

theorem exists_sylow_le_normalizer_of_coprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A N : Subgroup G} (hA : IsPGroup p A) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hN : p.Coprime (Nat.card N)) :
    ∃ T : Sylow q N, A ≤ Subgroup.normalizer ((T : Subgroup N).map N.subtype : Set G) := by
  let _ : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N (N.normalizerMonoidHom.comp (Subgroup.inclusion hAN))
  obtain ⟨T₀⟩ : Nonempty (Sylow q N) := inferInstance
  have hcard : ¬ p ∣ Nat.card (Sylow q N) := fun hdvd =>
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hN
      (hdvd.trans (T₀.card_dvd_index.trans (T₀ : Subgroup N).index_dvd_card))
  obtain ⟨T, hT⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q N) hcard
  refine ⟨T, fun a ha => ?_⟩
  have hfix : (T : Subgroup N).map
      (N.normalizerMonoidHom (Subgroup.inclusion hAN ⟨a, ha⟩)).toMonoidHom = T := by
    have h := congrArg (fun S : Sylow q N => (S : Subgroup N)) (hT ⟨a, ha⟩)
    rw [Sylow.pointwise_smul_def] at h
    exact h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  conv_rhs => rw [← hfix]
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem odd_card_of_twoLocals_le {p : ℕ} (hp : p.Prime) {P C O M : Subgroup G}
    (hP : IsPGroup p P) (hPC : P ≤ C) (hCM : ¬ C ≤ M) (hOC : O ≤ C)
    (hOn : (O.subgroupOf C).Normal) (hOp : p.Coprime (Nat.card O)) (hOM : O ≤ M)
    (h2 : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → P ≤ Subgroup.normalizer (T : Set G) →
      Subgroup.normalizer (T : Set G) ≤ M) :
    Odd (Nat.card O) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hev
  have hcardO : Nat.card (O.subgroupOf C) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv
  obtain ⟨T, hT⟩ := exists_sylow_le_normalizer_of_coprime (q := 2) (hP.comap_subtype (K := C))
    ((Subgroup.normalizer_eq_top (O.subgroupOf C)).symm ▸ le_top) (hcardO ▸ hOp)
  let TC : Subgroup C := (T : Subgroup (O.subgroupOf C)).map (O.subgroupOf C).subtype
  have hT1 : TC.map C.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
    exact T.ne_bot_of_dvd_card
      (hcardO ▸ even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
  have hNT : Subgroup.normalizer ((TC.map C.subtype : Subgroup G) : Set G) ≤ M := by
    refine h2 _ ((T.isPGroup'.map _).map _) hT1 fun x hx => ?_
    exact Subgroup.le_normalizer_map C.subtype
      (Subgroup.mem_map_of_mem C.subtype (hT (show ⟨x, hPC hx⟩ ∈ P.subgroupOf C from hx)))
  apply hCM
  have htop : (⊤ : Subgroup C) ≤ M.subgroupOf C := by
    rw [← Sylow.normalizer_sup_eq_top T]
    refine sup_le (fun c hc => hNT ?_) (fun c hc => hOM hc)
    exact Subgroup.le_normalizer_map C.subtype (Subgroup.mem_map_of_mem C.subtype hc)
  exact Subgroup.subgroupOf_eq_top.mp (top_unique htop)

@[expose] def D1ExtremalCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → False

theorem D1Escape.exists_extremal {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Escape p P M H R) : ∃ K R' : Subgroup G, D1Extremal p P M K R' := by
  have : Fact p.Prime := ⟨h.prime⟩
  let S : Set (Subgroup G) := {X | IsPGroup p X ∧ ∃ H' : Subgroup G, IsTwoLocal H' ∧
    ¬ H' ≤ M ∧ 3 ≤ pRank p (H' ⊓ M) ∧ X ≤ H' ⊓ M}
  obtain ⟨X, ⟨hX, H₁, hH₁, hH₁M, hH₁rank, hXH₁⟩, hmax⟩ :=
    S.exists_max_image (fun X : Subgroup G => toLex (Nat.card X, pRank p X)) S.toFinite
      ⟨R, h.isPGroup, H, h.maxTwoLocal_H.1, h.not_le, h.three_le_pRank_inf, h.le_inf⟩
  have hmax' : ∀ Y ∈ S, Nat.card Y ≤ Nat.card X ∧
      (Nat.card Y = Nat.card X → pRank p Y ≤ pRank p X) := fun Y hY =>
    Prod.Lex.toLex_le_toLex'.mp (hmax Y hY)
  obtain ⟨K, hH₁K, hK⟩ := exists_maximal_twoLocal hH₁
  have hKM : ¬ K ≤ M := fun hle => hH₁M (hH₁K.trans hle)
  have hKrank : 3 ≤ pRank p (K ⊓ M) :=
    hH₁rank.trans (pRank_mono p h.prime (inf_le_inf_right M hH₁K))
  obtain ⟨T, hTM, hTrank, -⟩ := intersecting_local_has_contained_sylow p h.prime P h.sylow_le
    h.weakCore_le hKrank
  have hXK : X ≤ K := (hXH₁.trans inf_le_left).trans hH₁K
  obtain ⟨hTX, hTXr⟩ := hmax' _ ⟨T.isPGroup'.map K.subtype, K, hK.1, hKM, hKrank,
    _root_.le_inf (Subgroup.map_subtype_le _) hTM⟩
  have hcard : Nat.card ((T : Subgroup K).map K.subtype) = Nat.card X :=
    le_antisymm hTX (card_le_card_map_sylow T hX hXK)
  obtain ⟨TX, hTXle⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  have hXTX : X ≤ (TX : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXK]
    exact Subgroup.map_mono hTXle
  have hTXeq : (TX : Subgroup K).map K.subtype = X := by
    refine (Subgroup.eq_of_le_of_card_ge hXTX ?_).symm
    rw [Subgroup.card_map_of_injective K.subtype_injective, TX.card_eq_multiplicity,
      ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective K.subtype_injective, hcard]
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le p P h.sylow_le (hXH₁.trans inf_le_right) hX
  let σ := MulAut.conj (m : G)
  refine ⟨K.map σ.toMonoidHom, X.map σ.toMonoidHom,
    { prime := h.prime
      ne_two := h.ne_two
      sylow_le := h.sylow_le
      weakCore_le := h.weakCore_le
      maxTwoLocal_M := h.maxTwoLocal_M
      maxTwoLocal_H := glbIsMaxTwoLocal_map_mulAut hK σ
      le_H := Subgroup.map_mono hXK
      le_P := hm
      isSylow := ⟨sylowMapMulAut TX σ, by rw [map_subtype_sylowMapMulAut TX σ, hTXeq]⟩
      three_le_pRank := by
        rw [pRank_map_of_injective p h.prime _ σ.injective]
        exact hTrank.trans (hTXr hcard)
      not_le := fun hle => hKM (le_of_map_conj_le m.2 hle)
      extremal := fun H' hH' hH'M hrank X' hX'H' hX' => by
        rw [Subgroup.card_map_of_injective σ.injective]
        exact (hmax' X' ⟨hX', H', hH', hH'M, hrank, hX'H'⟩).1
      extremal3 := fun H' hH' hH'M hrank X' hX'H' hX' hX'c => by
        rw [Subgroup.card_map_of_injective σ.injective] at hX'c
        rw [pRank_map_of_injective p h.prime _ σ.injective]
        exact (hmax' X' ⟨hX', H', hH', hH'M, hrank, hX'H'⟩).2 hX'c }⟩

theorem d1MaxCase_of_extremalCase (h : D1ExtremalCase) : D1MaxCase := by
  intro G _ _ hglob p P M hloc H hH R hRP hRrank
  by_contra hnot
  obtain ⟨K, R', hext⟩ := (D1Escape.of_maxCase hloc hH R hRP hRrank hnot).exists_extremal
  exact h G hglob p P M hloc K R' hext

theorem d1_of_extremalCase (h : D1ExtremalCase) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) (p : ℕ)
    (hp : p ∈ GLBBetaFour G) (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hHM : 3 ≤ pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_maxCase (d1MaxCase_of_extremalCase h) G hnonab hK hchar he hpre p hp P M hM hWM H hH hHM

end CFSG.AGLEmbedding
