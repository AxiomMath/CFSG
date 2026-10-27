module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointDelta
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_of_isSylowOf {p : ℕ} (hp : p.Prime) {Y S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) : Open.pRank p S = Open.pRank p Y := by
  obtain ⟨T, rfl⟩ := hS
  rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp Y.subtype
    Y.subtype_injective, CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp T,
    ← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp Y.subtype
      Y.subtype_injective (⊤ : Subgroup Y), ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isSylowOf_map_conj {p : ℕ} [Fact p.Prime] {S Y : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p S Y) (g : G) :
    CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj g).toMonoidHom)
      (Y.map (MulAut.conj g).toMonoidHom) := by
  refine CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [card_map_of_injective (MulAut.conj g).injective,
    card_map_of_injective (MulAut.conj g).injective, h.card_eq]

omit [Finite G] in
theorem centralizer_conj_eq (g x : G) :
    centralizer ({g * x * g⁻¹} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [CFSG.RankThree.PartTwo.Sec21.mem_map_conj_iff, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

structure IsPPoint (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop where
  elem : IsPElement p M x
  mem : x ∈ (P : Subgroup G)
  sylow : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (centralizer ({x} : Set G))
  three_le : 3 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))

theorem exists_isPPoint (hFC : FullCoreLocality G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hloc : D1Local p P M) {x : G} (hx : IsPElement p M x) :
    ∃ m ∈ M, IsPPoint p P M (m * x * m⁻¹) := by
  have hprime := hloc.beta.1
  have : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  obtain ⟨hxM, hxo, hrank, hCM⟩ := hx
  have hx3 : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hMC : x ∈ M ⊓ C := ⟨hxM, hxC⟩
  obtain ⟨Q₀, hQ₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (M ⊓ C)
  have hQ₀rank : 3 ≤ Open.pRank p Q₀ := by
    rw [pRank_eq_of_isSylowOf hprime hQ₀]
    exact hrank
  have hxQ₀ : x ∈ Q₀ := by
    by_contra hxQ
    have hcomm : ∀ q ∈ Q₀, q * x = x * q := fun q hq =>
      mem_centralizer_singleton_iff.1 (hQ₀.le hq).2
    obtain ⟨a, ha⟩ := hQ₀.isPGroup.exists_card_eq
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime Q₀ hx3 hxQ hcomm
    have hpg : IsPGroup p (Q₀ ⊔ zpowers x : Subgroup G) :=
      IsPGroup.of_card (n := a + 1) (by rw [hcard, ha]; ring)
    have heq := hQ₀.eq_of_le le_sup_left (sup_le hQ₀.le (zpowers_le.2 hMC)) hpg
    exact hxQ (heq ▸ mem_sup_right (mem_zpowers x))
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM Q₀
    hQ₀.isPGroup (hQ₀.le.trans inf_le_left)
  refine ⟨m, m.2, ?_⟩
  set y : G := (m : G) * x * (m : G)⁻¹ with hy
  set Q₁ : Subgroup G := Q₀.map (MulAut.conj (m : G)).toMonoidHom with hQ₁
  have hMm : M.map (MulAut.conj (m : G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer m.2)
  have hCy : centralizer ({y} : Set G) = C.map (MulAut.conj (m : G)).toMonoidHom :=
    centralizer_conj_eq (m : G) x
  have hMCy : (M ⊓ C).map (MulAut.conj (m : G)).toMonoidHom = M ⊓ centralizer ({y} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (m : G)).injective, hMm, hCy]
  have hQ₁syl : CFSG.ABGLocalTools.IsSylowOf p Q₁ (M ⊓ centralizer ({y} : Set G)) :=
    hMCy ▸ isSylowOf_map_conj hQ₀ (m : G)
  have hyQ₁ : y ∈ Q₁ := ⟨x, hxQ₀, rfl⟩
  have hyP : y ∈ (P : Subgroup G) := hm hyQ₁
  have hQ₁rank : 3 ≤ Open.pRank p Q₁ := by
    rw [hQ₁, pRank_map_automorphism p hprime.one_lt]
    exact hQ₀rank
  have hQ₁p : IsPGroup p Q₁ := hQ₁syl.isPGroup
  have hQ₁Cy : Q₁ ≤ centralizer ({y} : Set G) := hQ₁syl.le.trans inf_le_right
  have hQ₁M : Q₁ ≤ M := hQ₁syl.le.trans inf_le_left
  have hPCy : (P : Subgroup G) ⊓ centralizer ({y} : Set G) = Q₁ :=
    hQ₁syl.eq_of_le (le_inf hm hQ₁Cy) (inf_le_inf_right _ hPM) (P.isPGroup'.to_inf_left)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p Q₁ (centralizer ({y} : Set G)) := by
    obtain ⟨T', hT'⟩ := (hQ₁p.comap_subtype :
      IsPGroup p (Q₁.subgroupOf (centralizer ({y} : Set G)))).exists_le_sylow
    set S : Subgroup G := (T' : Subgroup (centralizer ({y} : Set G))).map
      (centralizer ({y} : Set G)).subtype with hS
    have hSsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer ({y} : Set G)) := ⟨T', rfl⟩
    have hQ₁S : Q₁ ≤ S := fun g hg => ⟨⟨g, hQ₁Cy hg⟩, hT' (mem_subgroupOf.2 hg), rfl⟩
    by_cases hlt : Q₁ < S
    · exfalso
      have hgrow := CFSG.RankThree.PartTwo.Sec21.lt_inf_normalizer_of_lt hSsyl.isPGroup hlt
      have hNM : normalizer (Q₁ : Set G) ≤ M :=
        normalizer_le_of_two_le_pRank hFC hloc hQ₁p hQ₁M (by omega)
      have hle : S ⊓ normalizer (Q₁ : Set G) ≤ M ⊓ centralizer ({y} : Set G) :=
        le_inf (inf_le_right.trans hNM) (inf_le_left.trans hSsyl.le)
      have := hQ₁syl.eq_of_le hgrow.le hle (hSsyl.isPGroup.to_inf_left)
      exact hgrow.ne this.symm
    · have hSQ : S ≤ Q₁ := by
        by_contra hnot
        exact hlt (lt_of_le_of_ne hQ₁S fun h => hnot (h ▸ le_rfl))
      have : S = Q₁ := le_antisymm hSQ hQ₁S
      exact this ▸ hSsyl
  have hyM : y ∈ M := M.mul_mem (M.mul_mem m.2 hxM) (M.inv_mem m.2)
  have helem : IsPElement p M y := by
    refine ⟨hyM, ?_, ?_, ?_⟩
    · have := MulEquiv.orderOf_eq (MulAut.conj (m : G)) x
      rw [MulAut.conj_apply] at this
      rw [hy, this, hxo]
    · rw [← hMCy, pRank_map_automorphism p hprime.one_lt]
      exact hrank
    · intro hle
      apply hCM
      rw [hCy] at hle
      exact (conjugate_subgroup_le_iff_of_conjugator_mem C M (m : G) m.2).1 hle
  exact ⟨helem, hyP, hPCy ▸ hSyl, hPCy ▸ hQ₁rank⟩

end CFSG.LocalAnalysis.RankFourTheoremC
