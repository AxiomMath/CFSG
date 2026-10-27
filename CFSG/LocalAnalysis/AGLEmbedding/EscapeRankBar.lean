module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem pRank_centralizer_le_two_of_normalizer_not_le {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) {M D : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hDM : D ≤ M) (hD : IsPGroup p D)
    (hD2 : 2 ≤ Open.pRank p D) (hDN : ¬ Subgroup.normalizer (D : Set G) ≤ M) :
    Open.pRank p (M ⊓ Subgroup.centralizer (D : Set G)) ≤ 2 := by
  by_contra h3
  exact hDN (normalizer_le_of_centralizer_rank_in_containing_sylow p hp P hPM hWM hDM hD hD2
    (by omega))

theorem pRank_centralizer_barM_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Sylow p G) {M D : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (hDM : D ≤ M) (hD : IsPGroup p D)
    (hD2 : 2 ≤ Open.pRank p D) (hDN : ¬ Subgroup.normalizer (D : Set G) ≤ M) :
    Open.pRank p (Subgroup.centralizer
      ((barM M D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hO : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hDp : IsPGroup p (D.subgroupOf M) := hD.comap_subtype
  have hceq := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p (CFSG.pCore 2 ↥M)
    (hp.coprime_iff_not_dvd.mp hO) (D.subgroupOf M) hDp
  rw [barM, ← hceq, pRank_map_mk_eq_pRank_map_subtype hp _ hO]
  refine (le_of_eq ?_).trans (pRank_centralizer_le_two_of_normalizer_not_le hp P hPM hWM hDM hD
    hD2 hDN)
  congr 1
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.2, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hm ⟨d, hDM hd⟩ (Subgroup.mem_subgroupOf.mpr hd)
    exact congrArg Subtype.val this
  · rintro ⟨hgM, hg⟩
    refine ⟨⟨g, hgM⟩, Subgroup.mem_centralizer_iff.mpr fun d hd => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hg d (Subgroup.mem_subgroupOf.mp hd)

section Centralizer

variable {Y : Type} [Group Y] [Finite Y]

private theorem not_isCyclic_of_two_le_pRank {p : ℕ} (hp : p.Prime) {A : Subgroup Y}
    (h : 2 ≤ Open.pRank p A) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨E, hEA, hE, hEc⟩ := pRank_attained p hp A
  have hEc' : IsCyclic E := by
    have : IsCyclic (E.subgroupOf A) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEA).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEA).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg, hEc] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p ^ 2 ≤ p ^ Open.pRank p A := Nat.pow_le_pow_right hp.pos h
  have h4 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

theorem two_le_pRank_inf_centralizer_of_two_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup Y} (hA : 2 ≤ Open.pRank p A) {y : Y} (hyA : y ∈ A) (hy : orderOf y = p) :
    2 ≤ Open.pRank p (A ⊓ Subgroup.centralizer ({y} : Set Y)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hyp : IsPGroup p ((Subgroup.zpowers y).subgroupOf A) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])).comap_subtype
  obtain ⟨T, hT⟩ := hyp.exists_le_sylow
  set T' : Subgroup Y := (T : Subgroup A).map A.subtype with hT'
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hyT' : y ∈ T' :=
    ⟨⟨y, hyA⟩, hT (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)), rfl⟩
  have hrank : 2 ≤ Open.pRank p T' := by
    rw [hT', pRank_map_of_injective p hp A.subtype A.subtype_injective,
      pRank_sylow_eq_globalRank p hp T,
      ← pRank_map_of_injective p hp A.subtype A.subtype_injective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hA
  have h := two_le_pRank_inf_centralizer_zpowers hp hp2 hT'p
    (not_isCyclic_of_two_le_pRank hp hrank) hyT' hy
  refine h.trans (pRank_mono p hp (le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) ?_))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  exact Subgroup.mem_centralizer_iff.mp hx.2 y (Subgroup.mem_zpowers y)

end Centralizer

end CFSG.AGLEmbedding
