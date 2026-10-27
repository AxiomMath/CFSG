module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_singleton_conj (m x : G) :
    centralizer ({MulAut.conj m x} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj m).toMonoidHom := by
  have hCeq : ∀ y : G, centralizer ({y} : Set G) =
      centralizer ((zpowers y : Subgroup G) : Set G) := fun y => by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hCeq, hCeq, centralizer_map_automorphism, MonoidHom.map_zpowers]
  rfl

theorem IsLargeObstruction.conj {p : ℕ} [hfact : Fact p.Prime] {M : Subgroup G} {x m : G}
    (hx : IsLargeObstruction p M x) (hm : m ∈ M) : IsLargeObstruction p M (MulAut.conj m x) := by
  obtain ⟨hxM, hx1, hxp, h3, hCM⟩ := hx
  refine ⟨?_, by simpa using hx1, by rw [← map_pow, hxp, map_one], ?_, ?_⟩
  · rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
  · rwa [centralizer_singleton_conj, pRank_map_automorphism p hfact.out.one_lt]
  · rwa [centralizer_singleton_conj, conjugate_subgroup_le_iff_of_conjugator_mem _ M m hm]

theorem pRank_le_of_isSylowOf {p : ℕ} [hfact : Fact p.Prime] {S K : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) :
    CFSG.Open.pRank p K ≤ CFSG.Open.pRank p S := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro r ⟨E, hEK, hE, hEc⟩
  obtain ⟨T, hT⟩ := ((elementary_isPGroup p E hE).comap_subtype (K := K)).exists_le_sylow
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf p ((T : Subgroup K).map K.subtype) K := ⟨T, rfl⟩
  have hET : E ≤ (T : Subgroup K).map K.subtype := fun y hy => ⟨⟨y, hEK hy⟩, hT hy, rfl⟩
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hTsyl
  have hmap : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (hk y).mp (hET hy)
  refine le_csSup (pRank_set_bddAbove p hfact.out.one_lt S) ⟨_, hmap,
    elementary_map_injective p E _ (MulAut.conj k⁻¹).injective hE, ?_⟩
  rw [card_map_of_injective (MulAut.conj k⁻¹).injective, hEc]

theorem exists_largeObstruction_isSylowOf (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x₀ : G} (hx₀ : IsLargeObstruction p M x₀) :
    ∃ x ∈ (P : Subgroup G), IsLargeObstruction p M x ∧
      CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
        (centralizer ({x} : Set G)) ∧
      CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) = 3 := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hx₀M, -, hx₀p, -, -⟩ := id hx₀
  have hx₀e : CFSG.IsElementaryAbelian p (zpowers x₀) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx₀p
  obtain ⟨m₀, hm₀⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM (zpowers x₀)
    (CFSG.IsElementaryAbelian.isPGroup p (zpowers x₀)) (zpowers_le.mpr hx₀M)
  have hx₁P : MulAut.conj (m₀ : G) x₀ ∈ (P : Subgroup G) :=
    hm₀ (mem_map_of_mem _ (mem_zpowers x₀))
  obtain ⟨x, ⟨hxP, hx⟩, hmax⟩ := Set.exists_max_image
    {y : G | y ∈ (P : Subgroup G) ∧ IsLargeObstruction p M y}
    (fun y => Nat.card ((P : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G))
    (Set.toFinite _) ⟨MulAut.conj (m₀ : G) x₀, hx₁P, hx₀.conj m₀.2⟩
  obtain ⟨-, hx1, hxp, hx3, -⟩ := id hx
  refine ⟨x, hxP, hx, ?_⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hS₀p : IsPGroup p ((P : Subgroup G) ⊓ C : Subgroup G) := P.isPGroup'.to_inf_left
  have hNM : normalizer (((P : Subgroup G) ⊓ C : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hS₀p (inf_le_left.trans hPM)
      (two_le_pRank_inf_centralizer P.isPGroup' (by omega) hxP hx1 hxp)
  obtain ⟨T, hT⟩ := (hS₀p.comap_subtype (K := C)).exists_le_sylow
  set S : Subgroup G := (T : Subgroup C).map C.subtype with hSdef
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p S C := ⟨T, rfl⟩
  have hle : (P : Subgroup G) ⊓ C ≤ S := fun y hy => ⟨⟨y, hy.2⟩, hT hy, rfl⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ C) C := by
    rcases hle.lt_or_eq with hlt | heq
    ·
      exfalso
      set Q : Subgroup G := S ⊓ normalizer (((P : Subgroup G) ⊓ C : Subgroup G) : Set G)
        with hQdef
      have hQ : (P : Subgroup G) ⊓ C < Q :=
        pGroup_proper_subgroup_lt_internal_normalizer p hprime S _ hSsyl.isPGroup hlt
      obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM Q
        hSsyl.isPGroup.to_inf_left (inf_le_right.trans hNM)
      have hxQ : x ∈ Q := hQ.le ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
      have hQm : Q.map (MulAut.conj (m : G)).toMonoidHom ≤
          (P : Subgroup G) ⊓ centralizer ({MulAut.conj (m : G) x} : Set G) := by
        refine le_inf hm ?_
        rw [centralizer_singleton_conj]
        exact map_mono (inf_le_left.trans hSsyl.le)
      have h1 : Nat.card ((P : Subgroup G) ⊓ centralizer ({MulAut.conj (m : G) x} : Set G) :
          Subgroup G) ≤ Nat.card ((P : Subgroup G) ⊓ C : Subgroup G) :=
        hmax _ ⟨hm (mem_map_of_mem _ hxQ), hx.conj m.2⟩
      have h2 := card_le_of_le hQm
      rw [card_map_of_injective (MulAut.conj (m : G)).injective] at h2
      have h3 := Subgroup.card_lt_of_lt hQ
      omega
    · rw [heq]
      exact hSsyl
  refine ⟨hsyl, le_antisymm ?_ (hx3.trans (pRank_le_of_isSylowOf hsyl))⟩
  exact hP3 ▸ pRank_mono p hprime.one_lt inf_le_left

end CFSG.LocalAnalysis.RankThreeTheoremC
