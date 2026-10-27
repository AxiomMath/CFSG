module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint CFSG.RankThree.PartTwo.KFacts Subgroup

private theorem stepASetup_exists_maximal_solvable {M : Type*} [Group M] [Finite M]
    (D : Subgroup M) :
    ∃ R : Subgroup M, R.Normal ∧ R ≤ D ∧ Group.IsSolvable R ∧
      ∀ R' : Subgroup M, R'.Normal → R' ≤ D → Group.IsSolvable R' → R ≤ R' → R' ≤ R := by
  obtain ⟨R, ⟨hRn, hRD, hRs⟩, hmax⟩ :=
    (Set.toFinite {R : Subgroup M | R.Normal ∧ R ≤ D ∧ Group.IsSolvable R}).exists_maximal
      ⟨⊥, inferInstance, bot_le, inferInstance⟩
  exact ⟨R, hRn, hRD, hRs, fun R' h1 h2 h3 h4 => hmax ⟨h1, h2, h3⟩ h4⟩

private theorem stepASetup_exists_minimal_normal {Y : Type*} [Group Y] [Finite Y]
    (Dh : Subgroup Y) [Dh.Normal] (hDh : Dh ≠ ⊥) :
    ∃ N : Subgroup Y, N.Normal ∧ N ≤ Dh ∧ N ≠ ⊥ ∧
      ∀ M' : Subgroup Y, M'.Normal → M' ≤ N → M' = ⊥ ∨ M' = N := by
  obtain ⟨N, ⟨hNn, hND, hN1⟩, hmin⟩ :=
    (Set.toFinite {N : Subgroup Y | N.Normal ∧ N ≤ Dh ∧ N ≠ ⊥}).exists_minimal
      ⟨Dh, inferInstance, le_rfl, hDh⟩
  refine ⟨N, hNn, hND, hN1, fun M' hM' hle => ?_⟩
  by_cases h : M' = ⊥
  · exact Or.inl h
  · exact Or.inr (le_antisymm hle (hmin ⟨hM', hle.trans hND, h⟩ hle))

private theorem stepASetup_le_comap {M : Type*} [Group M] (R : Subgroup M) [R.Normal]
    (N : Subgroup (M ⧸ R)) : R ≤ N.comap (QuotientGroup.mk' R) := fun x hx => by
  change QuotientGroup.mk' R x ∈ N
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact N.one_mem

private theorem stepASetup_isSolvable_comap {M : Type*} [Group M] (R : Subgroup M) [R.Normal]
    [Group.IsSolvable R] (N : Subgroup (M ⧸ R)) (hN : ∀ a b : N, a * b = b * a) :
    Group.IsSolvable (N.comap (QuotientGroup.mk' R)) := by
  have : Group.IsSolvable N := Group.isSolvable_of_comm hN
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (stepASetup_le_comap R N))
    ((QuotientGroup.mk' R).subgroupComap N) fun x hx => ?_
  have hx1 : QuotientGroup.mk' R x.1 = 1 := congrArg Subtype.val hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  exact ⟨⟨x.1, hx1⟩, rfl⟩

private theorem stepASetup_nonabelian {M : Type*} [Group M] {D R : Subgroup M} [R.Normal]
    (hRD : R ≤ D) (hRs : Group.IsSolvable R)
    (hmax : ∀ R' : Subgroup M, R'.Normal → R' ≤ D → Group.IsSolvable R' → R ≤ R' → R' ≤ R)
    {N : Subgroup (M ⧸ R)} [N.Normal] (hND : N ≤ D.map (QuotientGroup.mk' R)) (hN1 : N ≠ ⊥) :
    ∃ a b : N, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have := hRs
  have hsolv := stepASetup_isSolvable_comap R N hab
  have hPD : N.comap (QuotientGroup.mk' R) ≤ D := by
    intro x hx
    obtain ⟨d, hdD, hd⟩ := hND hx
    have hdx : d⁻¹ * x ∈ R := by
      rw [← QuotientGroup.eq]
      exact hd
    have hx' : x = d * (d⁻¹ * x) := by group
    rw [hx']
    exact mul_mem hdD (hRD hdx)
  have hPR := hmax _ (Subgroup.Normal.comap inferInstance _) hPD hsolv (stepASetup_le_comap R N)
  refine hN1 (eq_bot_iff.mpr fun y hy => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  have hxR : x ∈ R := hPR hy
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff x).mpr hxR

theorem exists_suzuki_normal_product (hKP : KPSz) {M : Type} [Group M] [Finite M]
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections M) {D : Subgroup M} [D.Normal]
    (hD3 : ¬ 3 ∣ Nat.card D) (hD : ¬ Group.IsSolvable D) :
    ∃ (R : Subgroup M) (_ : R.Normal), R ≤ D ∧ Group.IsSolvable R ∧
      ∃ (N : Subgroup (M ⧸ R)) (_ : N.Normal) (r : ℕ) (S : Fin r → Subgroup (M ⧸ R)),
        N ≤ D.map (QuotientGroup.mk' R) ∧ ¬ 3 ∣ Nat.card N ∧ 1 ≤ r ∧ SimpleFactorData N S ∧
        ∀ i, ∃ f, SuzukiModel (S i) 2 f := by
  obtain ⟨R, hRn, hRD, hRs, hmax⟩ := stepASetup_exists_maximal_solvable D
  refine ⟨R, hRn, hRD, hRs, ?_⟩
  have hDh : D.map (QuotientGroup.mk' R) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hD (by rw [le_antisymm h hRD]; exact hRs)
  have : (D.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
  obtain ⟨N, hNn, hND, hN1, hNmin⟩ := stepASetup_exists_minimal_normal _ hDh
  have hnonab := stepASetup_nonabelian hRD hRs hmax hND hN1
  obtain ⟨r, S, hr, hSle, hSsimple, hSconj, hSnormal, hprod⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hNmin
  have hSnonab : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    intro i
    by_contra hi
    push Not at hi
    have hcomm : ∀ j, ∀ u ∈ S j, ∀ v ∈ S j, u * v = v * u := by
      intro j u hu v hv
      obtain ⟨g, hg⟩ := hSconj i j
      rw [hg] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hi ⟨u', hu'⟩ ⟨v', hv'⟩))
    obtain ⟨a, b, hab⟩ := hnonab
    obtain ⟨e, -⟩ := hprod
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    refine hab ?_
    rw [← map_mul, ← map_mul]
    congr 1
    funext j
    exact Subtype.ext (hcomm j _ (x j).2 _ (y j).2)
  have h3N : ¬ 3 ∣ Nat.card N := fun h =>
    hD3 (h.trans ((Subgroup.card_dvd_of_le hND).trans (Subgroup.card_map_dvd D _)))
  refine ⟨N, hNn, r, S, hND, h3N, hr, ⟨hSle, hSsimple, hSnonab, hSnormal, hprod⟩, fun i => ?_⟩
  have := hSsimple i
  have hcatS : CFSG.Open.IsCatalogGroup (S i) :=
    (hcat.quotient R).simple_subgroup (S i) (hSsimple i) (hSnonab i)
  exact hKP (S i) (hSnonab i) hcatS fun h =>
    h3N (h.trans (Subgroup.card_dvd_of_le (hSle i)))

end CFSG.LocalAnalysis.RankThreeTheoremC
