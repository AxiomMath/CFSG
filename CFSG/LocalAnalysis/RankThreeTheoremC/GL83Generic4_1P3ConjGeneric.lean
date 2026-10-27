module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_isGenericPoint (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {u₀ : G} (hu₀ : IsLargeObstruction p M u₀) :
    ∃ m ∈ M, MulAut.conj m u₀ ∈ (P : Subgroup G) ∧ IsGenericPoint p P M (MulAut.conj m u₀) := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hx₀M, -, hx₀p, -, -⟩ := id hu₀
  have hx₀e : CFSG.IsElementaryAbelian p (zpowers u₀) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx₀p
  obtain ⟨m₀, hm₀⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM (zpowers u₀)
    (CFSG.IsElementaryAbelian.isPGroup p (zpowers u₀)) (zpowers_le.mpr hx₀M)
  have hx₁P : MulAut.conj (m₀ : G) u₀ ∈ (P : Subgroup G) :=
    hm₀ (mem_map_of_mem _ (mem_zpowers u₀))
  obtain ⟨x, ⟨hxP, m₁, hm₁M, hxm₁⟩, hmax⟩ := Set.exists_max_image
    {y : G | y ∈ (P : Subgroup G) ∧ ∃ m ∈ M, y = MulAut.conj m u₀}
    (fun y => Nat.card ((P : Subgroup G) ⊓ centralizer ({y} : Set G) : Subgroup G))
    (Set.toFinite _) ⟨MulAut.conj (m₀ : G) u₀, hx₁P, m₀, m₀.2, rfl⟩
  have hx : IsLargeObstruction p M x := hxm₁ ▸ hu₀.conj hm₁M
  obtain ⟨-, hx1, hxp, hx3, -⟩ := id hx
  suffices hgen : IsGenericPoint p P M x from ⟨m₁, hm₁M, hxm₁ ▸ hxP, hxm₁ ▸ hgen⟩
  refine ⟨hxP, hx, ?_⟩
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
        hmax _ ⟨hm (mem_map_of_mem _ hxQ), (m : G) * m₁, M.mul_mem m.2 hm₁M, by
          rw [hxm₁, map_mul]; rfl⟩
      have h2 := card_le_of_le hQm
      rw [card_map_of_injective (MulAut.conj (m : G)).injective] at h2
      have h3 := Subgroup.card_lt_of_lt hQ
      omega
    · rw [heq]
      exact hSsyl
  refine ⟨hsyl, le_antisymm ?_ (hx3.trans (pRank_le_of_isSylowOf hsyl))⟩
  exact hP3 ▸ pRank_mono p hprime.one_lt inf_le_left

end CFSG.LocalAnalysis.RankThreeTheoremC
