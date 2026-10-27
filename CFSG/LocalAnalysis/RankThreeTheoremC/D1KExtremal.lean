module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1KExtremal (p : ℕ) (P : Sylow p G) (M H R : Subgroup G) : Prop
    extends D1Escape p P M H R where
  kappa_max : ∀ (P' : Sylow p G) (M' N R' : Subgroup G), D1Escape p P' M' N R' →
    d1Kappa p M' N ≤ d1Kappa p M H
  extremalK : ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → 3 ≤ Open.pRank p (N ⊓ M) →
    d1Kappa p M H ≤ d1Kappa p M N → ∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup p X →
      Nat.card X ≤ Nat.card R
  extremalK3 : ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → 3 ≤ Open.pRank p (N ⊓ M) →
    d1Kappa p M H ≤ d1Kappa p M N → ∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup p X →
      Nat.card X = Nat.card R → Open.pRank p X ≤ Open.pRank p R

theorem exists_d1Escape_of_sylow {p : ℕ} {P : Sylow p G} {M H R N : Subgroup G}
    (he : D1Escape p P M H R) (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M) (T : Sylow p N)
    (hTM : (T : Subgroup N).map N.subtype ≤ M)
    (h3 : 3 ≤ Open.pRank p ((T : Subgroup N).map N.subtype)) :
    ∃ P' : Sylow p G, D1Escape p P' M N ((T : Subgroup N).map N.subtype) := by
  classical
  have hp := he.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := he.sylow_le
  set T' := (T : Subgroup N).map N.subtype with hT'
  have hT : IsPGroup p T' := T.isPGroup'.map N.subtype
  obtain ⟨S, hS⟩ := (hT.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) S
  set P' : Sylow p G := (m : G) • P with hP'
  have hP'coe : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj (m : G)).toMonoidHom := by
    ext x
    rw [hP', Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'coe]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hPM hy)) (M.inv_mem m.2)
  have hTP' : T' ≤ P' := by
    intro t ht
    have h1 : (⟨t, hTM ht⟩ : M) ∈ (S : Subgroup M) := hS (Subgroup.mem_subgroupOf.mpr ht)
    rw [← hm, Sylow.coe_subgroup_smul, Sylow.coe_subtype,
      Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, hy, hyt⟩ := h1
    rw [hP'coe]
    refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
    have := congrArg Subtype.val hyt
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hW : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'coe]; exact weakCore_conj_le hp he.weakCore_le m.2
  exact ⟨P',
    { prime := hp
      ne_two := he.ne_two
      sylow_le := hP'M
      weakCore_le := hW
      maxTwoLocal_M := he.maxTwoLocal_M
      maxTwoLocal_H := hN
      le_H := Subgroup.map_subtype_le _
      le_P := hTP'
      isSylow := ⟨T, rfl⟩
      three_le_pRank := h3
      not_le := hNM }⟩

theorem exists_sylow_map_eq_of_card_le {p : ℕ} [Fact p.Prime] {N X : Subgroup G}
    (T : Sylow p N) (hX : IsPGroup p X) (hXN : X ≤ N)
    (hc : Nat.card ((T : Subgroup N).map N.subtype) ≤ Nat.card X) :
    ∃ S : Sylow p N, (S : Subgroup N).map N.subtype = X := by
  obtain ⟨S, hS⟩ := (hX.comap_subtype (K := N)).exists_le_sylow
  have hXS : X ≤ (S : Subgroup N).map N.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXN]
    exact Subgroup.map_mono hS
  refine ⟨S, (Subgroup.eq_of_le_of_card_ge hXS ?_).symm⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective, S.card_eq_multiplicity,
    ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective N.subtype_injective]
  exact hc

theorem exists_d1KExtremal_of_escape {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Escape p P M H R) :
    ∃ (P₀ : Sylow p G) (M₀ H₀ R₀ : Subgroup G), D1KExtremal p P₀ M₀ H₀ R₀ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  let S : Set (Sylow p G × Subgroup G × Subgroup G × Subgroup G) :=
    {a | D1Escape p a.1 a.2.1 a.2.2.1 a.2.2.2}
  let f : Sylow p G × Subgroup G × Subgroup G × Subgroup G → ℕ ×ₗ (ℕ ×ₗ ℕ) := fun a =>
    toLex (d1Kappa p a.2.1 a.2.2.1, toLex (Nat.card a.2.2.2, Open.pRank p a.2.2.2))
  obtain ⟨⟨P₀, M₀, H₀, R₀⟩, h₀, hmax⟩ := S.exists_max_image f S.toFinite ⟨(P, M, H, R), h⟩
  have h₀ : D1Escape p P₀ M₀ H₀ R₀ := h₀
  have hkey : ∀ (P' : Sylow p G) (M' N R' : Subgroup G), D1Escape p P' M' N R' →
      d1Kappa p M' N ≤ d1Kappa p M₀ H₀ ∧ (d1Kappa p M' N = d1Kappa p M₀ H₀ →
        Nat.card R' ≤ Nat.card R₀ ∧ (Nat.card R' = Nat.card R₀ → Open.pRank p R' ≤ Open.pRank p R₀)) := by
    intro P' M' N R' he
    obtain ⟨h1, h2⟩ := Prod.Lex.toLex_le_toLex'.mp (hmax (P', M', N, R') he)
    exact ⟨h1, fun heq => Prod.Lex.toLex_le_toLex'.mp (h2 heq)⟩
  have hsyl : ∀ N : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M₀ → 3 ≤ Open.pRank p (N ⊓ M₀) →
      d1Kappa p M₀ H₀ ≤ d1Kappa p M₀ N → ∃ T : Sylow p N,
        (T : Subgroup N).map N.subtype ≤ M₀ ∧
        Nat.card ((T : Subgroup N).map N.subtype) ≤ Nat.card R₀ := by
    intro N hN hNM hrank hk
    obtain ⟨T, hTM, hTrank, -⟩ := intersecting_local_has_contained_sylow p h₀.prime P₀
      h₀.sylow_le h₀.weakCore_le hrank
    obtain ⟨P', he'⟩ := exists_d1Escape_of_sylow h₀ hN hNM T hTM hTrank
    obtain ⟨hk1, hk2⟩ := hkey _ _ _ _ he'
    exact ⟨T, hTM, (hk2 (le_antisymm hk1 hk)).1⟩
  refine ⟨P₀, M₀, H₀, R₀,
    { toD1Escape := h₀
      kappa_max := fun P' M' N R' he => (hkey P' M' N R' he).1
      extremalK := ?_
      extremalK3 := ?_ }⟩
  · intro N hN hNM hrank hk X hXNM hX
    obtain ⟨T, -, hTc⟩ := hsyl N hN hNM hrank hk
    exact (card_le_card_map_sylow T hX (hXNM.trans inf_le_left)).trans hTc
  · intro N hN hNM hrank hk X hXNM hX hXR
    by_contra hlt
    push Not at hlt
    have hXN : X ≤ N := hXNM.trans inf_le_left
    obtain ⟨T, -, hTc⟩ := hsyl N hN hNM hrank hk
    obtain ⟨S', hS'⟩ := exists_sylow_map_eq_of_card_le T hX hXN (hXR ▸ hTc)
    have h3 : 3 ≤ Open.pRank p ((S' : Subgroup N).map N.subtype) := by
      rw [hS']; exact h₀.three_le_pRank.trans hlt.le
    obtain ⟨P', he'⟩ := exists_d1Escape_of_sylow h₀ hN hNM S' (hS' ▸ hXNM.trans inf_le_right) h3
    rw [hS'] at he'
    obtain ⟨hk1, hk2⟩ := hkey _ _ _ _ he'
    exact (hk2 (le_antisymm hk1 hk)).2 hXR |>.not_gt hlt

structure D1ExtremalOn (p : ℕ) (P : Sylow p G) (M H R : Subgroup G) (c : ℕ) : Prop
    extends D1Escape p P M H R where
  extremal : ∀ H' : Subgroup G, IsTwoLocal H' → ¬ H' ≤ M → 3 ≤ Open.pRank p (H' ⊓ M) →
    (∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ H' ≤ N ∧ c ≤ d1Kappa p M N) →
    ∀ X : Subgroup G, X ≤ H' ⊓ M → IsPGroup p X → Nat.card X ≤ Nat.card R
  extremal3 : ∀ H' : Subgroup G, IsTwoLocal H' → ¬ H' ≤ M → 3 ≤ Open.pRank p (H' ⊓ M) →
    (∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ H' ≤ N ∧ c ≤ d1Kappa p M N) →
    ∀ X : Subgroup G, X ≤ H' ⊓ M → IsPGroup p X → Nat.card X = Nat.card R →
      Open.pRank p X ≤ Open.pRank p R

theorem D1Extremal.toOn {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} (h : D1Extremal p P M H R)
    (c : ℕ) : D1ExtremalOn p P M H R c :=
  { toD1Escape := h.toD1Escape
    extremal := fun H' hH' hH'M h3 _ => h.extremal H' hH' hH'M h3
    extremal3 := fun H' hH' hH'M h3 _ => h.extremal3 H' hH' hH'M h3 }

theorem D1ExtremalOn.toD1Extremal {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} {c : ℕ}
    (h : D1ExtremalOn p P M H R c) (hc : c ≤ 1) : D1Extremal p P M H R := by
  have hex : ∀ H' : Subgroup G, IsTwoLocal H' →
      ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ H' ≤ N ∧ c ≤ d1Kappa p M N := fun H' hH' => by
    obtain ⟨N, hH'N, hN⟩ := exists_maximal_twoLocal hH'
    exact ⟨N, hN, hH'N, hc.trans Nat.card_pos⟩
  exact { toD1Escape := h.toD1Escape
          extremal := fun H' hH' hH'M h3 => h.extremal H' hH' hH'M h3 (hex H' hH')
          extremal3 := fun H' hH' hH'M h3 => h.extremal3 H' hH' hH'M h3 (hex H' hH') }

theorem D1KExtremal.toOn {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1KExtremal p P M H R) : D1ExtremalOn p P M H R (d1Kappa p M H) := by
  have hN : ∀ H' : Subgroup G, ¬ H' ≤ M → 3 ≤ Open.pRank p (H' ⊓ M) → ∀ N : Subgroup G,
      H' ≤ N → ¬ N ≤ M ∧ 3 ≤ Open.pRank p (N ⊓ M) := fun H' hH'M h3 N hH'N =>
    ⟨fun hle => hH'M (hH'N.trans hle), h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime (inf_le_inf_right M hH'N))⟩
  exact { toD1Escape := h.toD1Escape
          extremal := fun H' _ hH'M h3 ⟨N, hNmax, hH'N, hk⟩ X hX hXp =>
            h.extremalK N hNmax (hN H' hH'M h3 N hH'N).1 (hN H' hH'M h3 N hH'N).2 hk X
              (hX.trans (inf_le_inf_right M hH'N)) hXp
          extremal3 := fun H' _ hH'M h3 ⟨N, hNmax, hH'N, hk⟩ X hX hXp =>
            h.extremalK3 N hNmax (hN H' hH'M h3 N hH'N).1 (hN H' hH'M h3 N hH'N).2 hk X
              (hX.trans (inf_le_inf_right M hH'N)) hXp }

theorem D1KExtremal.toD1Extremal_of_kappa_eq_one {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1KExtremal p P M H R) (h1 : d1Kappa p M H = 1) : D1Extremal p P M H R :=
  h.toOn.toD1Extremal h1.le

namespace D1ExtremalOn

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G} {c : ℕ}

theorem le_of_card_lt (h : D1ExtremalOn p P M H R c) {X H' : Subgroup G} (hXM : X ≤ M)
    (hX : IsPGroup p X) (hXrank : 3 ≤ Open.pRank p X) (hXR : Nat.card R < Nat.card X)
    (hH' : IsTwoLocal H') (hXH' : X ≤ H')
    (hc : ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ H' ≤ N ∧ c ≤ d1Kappa p M N) : H' ≤ M := by
  by_contra hH'M
  have hXinf : X ≤ H' ⊓ M := le_inf hXH' hXM
  exact (h.extremal H' hH' hH'M (hXrank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime hXinf)) hc X hXinf
    hX).not_gt hXR

theorem le_of_card_le_of_pRank_lt (h : D1ExtremalOn p P M H R c) {X H' : Subgroup G}
    (hXM : X ≤ M) (hX : IsPGroup p X) (hXR : Nat.card R ≤ Nat.card X)
    (hrk : Open.pRank p R < Open.pRank p X) (hH' : IsTwoLocal H') (hXH' : X ≤ H')
    (hc : ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧ H' ≤ N ∧ c ≤ d1Kappa p M N) : H' ≤ M := by
  rcases hXR.lt_or_eq with hlt | heq
  · exact h.le_of_card_lt hXM hX (h.three_le_pRank.trans hrk.le) hlt hH' hXH' hc
  · by_contra hH'M
    have hXinf : X ≤ H' ⊓ M := le_inf hXH' hXM
    exact (h.extremal3 H' hH' hH'M ((h.three_le_pRank.trans hrk.le).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime hXinf)) hc X hXinf hX heq.symm).not_gt hrk

end D1ExtremalOn

end CFSG.LocalAnalysis.RankThreeTheoremC
