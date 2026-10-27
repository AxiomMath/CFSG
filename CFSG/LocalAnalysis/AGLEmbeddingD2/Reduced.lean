module

public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

structure D2Reduced (p : ℕ) (X : Type*) [Group X] [Finite X] (R : Sylow p X)
    (A X₀ : Subgroup X) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  core_eq_bot : primeComplementCore (G := X) p = ⊥
  pRank_eq : Open.pRank p (R : Subgroup X) = 2
  elem : IsElemAbelian p A
  card_A : Nat.card A = p ^ 2
  A_le : A ≤ R
  sylow_le : (R : Subgroup X) ≤ X₀
  ne_top : X₀ ≠ ⊤
  normalizer_le_of_le_A : ∀ Y : Subgroup X, Y ≤ A → Y ≠ ⊥ →
    Subgroup.normalizer (Y : Set X) ≤ X₀
  normalizer_le_of_rank : ∀ Y : Subgroup X, Y ≤ X₀ → IsPGroup p Y → 2 ≤ Open.pRank p Y →
    Subgroup.normalizer (Y : Set X) ≤ X₀

theorem exists_isPGroup_map_mk_eq_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (N : Subgroup X) [N.Normal] {Y : Subgroup (X ⧸ N)} (hY : IsPGroup p Y) :
    ∃ W : Subgroup X, IsPGroup p W ∧ W.map (QuotientGroup.mk' N) = Y := by
  set f := QuotientGroup.mk' N
  let g : Y.comap f →* Y := (f.comp (Y.comap f).subtype).codRestrict Y fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p (Y.comap f)) := inferInstance
  have htop : (S : Subgroup (Y.comap f)).map g = ⊤ := by
    have hmax := (S.mapSurjective hg).is_maximal' (hY.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at hmax
    exact hmax.symm
  refine ⟨(S : Subgroup (Y.comap f)).map (Y.comap f).subtype, S.isPGroup'.map _, ?_⟩
  have hcomp : f.comp (Y.comap f).subtype = Y.subtype.comp g := rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem normalizer_map_mk_le_map_inf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M H : Subgroup G} (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O))
    (hOM : O ≤ (H ⊓ M).subgroupOf H) {Q : Subgroup H} (hQ : IsPGroup p Q)
    (hN : Subgroup.normalizer ((Q.map H.subtype : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer ((Q.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) := by
  have hNH : Subgroup.normalizer (Q : Set H) ≤ (H ⊓ M).subgroupOf H := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hN (Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
    ((comap_normalizer_map_le_sup hp O hO hQ).trans (sup_le hOM hNH))

theorem D2Escape.reduced_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) (hOM : O ≤ (H ⊓ M).subgroupOf H)
    (hcore : primeComplementCore (G := H ⧸ O) p = ⊥) :
    ∃ Rbar : Sylow p (H ⧸ O),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' O) ∧
      D2Reduced p (H ⧸ O) Rbar ((A.subgroupOf H).map (QuotientGroup.mk' O))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hTR : (T : Subgroup H) = R.subgroupOf H := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hRH : (R.subgroupOf H).map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le h.le_H
  have hAH : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le h.A_le_H
  have hAcard : Nat.card (A.subgroupOf H) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le_H).toEquiv, h.card_A]
  have hAp : IsPGroup p (A.subgroupOf H) := IsPGroup.of_card hAcard
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hTR], h.prime, h.ne_two, hcore, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Sylow.coe_mapSurjective, hTR, pRank_map_mk_eq_pRank_map_subtype h.prime _ hO, hRH]
    exact h.pRank_eq
  ·
    exact elementary_abelian_map p (isElemAbelian_subgroupOf h.elem H) _
  ·
    rw [card_map_mk_of_isPGroup h.prime O hO hAp, hAcard]
  ·
    rw [Sylow.coe_mapSurjective, hTR]
    exact Subgroup.map_mono (Subgroup.comap_mono h.A_le)
  ·
    rw [Sylow.coe_mapSurjective, hTR]
    exact Subgroup.map_mono (Subgroup.comap_mono (le_inf h.le_H h.le_M))
  ·
    intro htop
    apply h.not_le
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' O) ((H ⊓ M).subgroupOf H)
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hcomap
    intro g hg
    have hmem : (⟨g, hg⟩ : H) ∈ (H ⊓ M).subgroupOf H := hcomap ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  ·
    intro Y hYA hY1
    set Y₁ := Y.comap (QuotientGroup.mk' O) ⊓ A.subgroupOf H
    have hmap : Y₁.map (QuotientGroup.mk' O) = Y := map_comap_inf_eq _ hYA
    have hY₁A : Y₁.map H.subtype ≤ A := (Subgroup.map_mono inf_le_right).trans hAH.le
    have hY₁ne : Y₁.map H.subtype ≠ ⊥ := by
      intro hbot
      apply hY1
      rw [← hmap, (Subgroup.map_eq_bot_iff_of_injective Y₁ H.subtype_injective).mp hbot,
        Subgroup.map_bot]
    rw [← hmap]
    exact normalizer_map_mk_le_map_inf h.prime O hO hOM (hAp.to_le inf_le_right)
      (h.normalizer_le_of_le_A hY₁A hY₁ne)
  ·
    intro Y hYX hY hrk
    obtain ⟨W, hW, hWY⟩ := exists_isPGroup_map_mk_eq_of_isPGroup O hY
    have hWB : W ≤ (H ⊓ M).subgroupOf H := by
      have hle : W ≤ (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O)).comap
          (QuotientGroup.mk' O) :=
        (Subgroup.le_comap_map _ W).trans (Subgroup.comap_mono (hWY ▸ hYX))
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hle
    have hWM : W.map H.subtype ≤ M := by
      rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp (hWB hw)).2
    have hrank : 2 ≤ Open.pRank p (W.map H.subtype) := by
      rw [← pRank_map_mk_eq_pRank_map_subtype h.prime O hO W, hWY]
      exact hrk
    rw [← hWY]
    exact normalizer_map_mk_le_map_inf h.prime O hO hOM hW
      (h.normalizer_le_of_le_M hWM (hW.map H.subtype) hrank)

theorem D2Escape.reduced {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      D2Reduced p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) := by
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime p
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  exact h.reduced_of_coprime _ hO hOM (primeComplementCore_quotient_eq_bot p)

end CFSG.AGLEmbeddingD2
