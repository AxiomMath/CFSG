module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeContainment
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover
  (pairedTorusHom pairedTorusHom_apply f4i torusPair torusPair_apply torusPair_mem_reeGamma)

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem rankOneTorusOne_le_reeFixedTorus
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusOne K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨u, rfl⟩
  have e : pairedTorusHom a (f4i 0) (f4i 3) u = torusPair a (u, 1) := by
    simp [pairedTorusHom_apply, torusPair_apply, torusElt_one]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [pairedTorusHom_apply]
    exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  · rw [e]
    exact torusPair_mem_reeGamma a hK _

theorem rankOneTorusTwo_le_reeFixedTorus
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusTwo K a ≤ F4.reeFixedTorus K a := by
  rintro _ ⟨u, rfl⟩
  have e : pairedTorusHom a (f4i 1) (f4i 2) u = torusPair a (1, u) := by
    simp [pairedTorusHom_apply, torusPair_apply, torusElt_one]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [pairedTorusHom_apply]
    exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  · rw [e]
    exact torusPair_mem_reeGamma a hK _

theorem reeLocalBlock_eq_of_isSimpleGroup
    {j : Fin F4.fixedOrbitCount}
    {T R : Subgroup (ModGL F4.tag K)} (hT : T ≤ F4.reeFixedTorus K a)
    (hR : R = Subgroup.closure ((F4.reeFixedOrbitUnipotent K a j : Set (ModGL F4.tag K)) ∪
      (T : Set (ModGL F4.tag K)) ∪
        {canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j)}))
    (hsimple : IsSimpleGroup ↥R) :
    F4.reeLocalBlock K a j = R ∧
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ F4.reeLocalBlock K a j ∧
      T ≤ F4.reeLocalBlock K a j := by
  set n := canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) with hn
  have hX : F4.reeFixedOrbitUnipotent K a j ≤ R := by
    rw [hR]
    exact fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hnR : n ∈ R := by
    rw [hR]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hTR : T ≤ R := by
    rw [hR]
    exact fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx))
  have hnn : n * n = 1 := canonicalRep_fixedOrbitElement_mul_self j
  have hinv : n⁻¹ * n⁻¹ = 1 := by rw [← mul_inv_rev, hnn, inv_one]
  have hY : ∀ y ∈ F4.reeFixedOrbitNegUnipotent K a j,
      ∃ x ∈ F4.reeFixedOrbitUnipotent K a j, n * x * n⁻¹ = y := by
    intro y hy
    rw [← map_conj_reeFixedOrbitUnipotent j] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, by simpa [MulAut.conj_apply] using hxy⟩
  have hMR : F4.reeLocalBlock K a j ≤ R := by
    refine sup_le hX fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hY y hy
    exact mul_mem (mul_mem hnR (hX hx)) (inv_mem hnR)
  have hle : (F4.reeLocalBlock K a j).map (MulAut.conj n).toMonoidHom ≤
      F4.reeLocalBlock K a j := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · show n * x * n⁻¹ ∈ F4.reeLocalBlock K a j
      have : n * x * n⁻¹ ∈ F4.reeFixedOrbitNegUnipotent K a j := by
        rw [← map_conj_reeFixedOrbitUnipotent j]
        exact ⟨x, hx, rfl⟩
      exact reeFixedOrbitNegUnipotent_le_reeLocalBlock j this
    · obtain ⟨x, hx, rfl⟩ := hY y hy
      show n * (n * x * n⁻¹) * n⁻¹ ∈ F4.reeLocalBlock K a j
      have e : n * (n * x * n⁻¹) * n⁻¹ = x := by
        calc n * (n * x * n⁻¹) * n⁻¹ = (n * n) * x * (n⁻¹ * n⁻¹) := by group
          _ = x := by rw [hnn, hinv, one_mul, mul_one]
      rw [e]
      exact reeFixedOrbitUnipotent_le_reeLocalBlock j hx
  have hNn : n ∈ Subgroup.normalizer (F4.reeLocalBlock K a j : Set (ModGL F4.tag K)) := by
    refine Subgroup.mem_normalizer_iff.2 fun z => ⟨fun hz => hle ⟨z, hz, rfl⟩, fun hz => ?_⟩
    have h2 : n * (n * z * n⁻¹) * n⁻¹ ∈ F4.reeLocalBlock K a j := hle ⟨n * z * n⁻¹, hz, rfl⟩
    have e : n * (n * z * n⁻¹) * n⁻¹ = z := by
      calc n * (n * z * n⁻¹) * n⁻¹ = (n * n) * z * (n⁻¹ * n⁻¹) := by group
        _ = z := by rw [hnn, hinv, one_mul, mul_one]
    rwa [e] at h2
  have hRnorm : R ≤ Subgroup.normalizer (F4.reeLocalBlock K a j : Set (ModGL F4.tag K)) := by
    rw [hR, Subgroup.closure_le]
    rintro g ((hg | hg) | hg)
    · exact Subgroup.le_normalizer (reeFixedOrbitUnipotent_le_reeLocalBlock j hg)
    · exact reeFixedTorus_le_normalizer_reeLocalBlock j (hT hg)
    · rw [Set.mem_singleton_iff.1 hg]
      exact hNn
  have hN : ((F4.reeLocalBlock K a j).subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMR).2 hRnorm
  have hRM : R ≤ F4.reeLocalBlock K a j := by
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((F4.reeLocalBlock K a j).subgroupOf R) with
      hbot | htop
    · exfalso
      obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) j
      have hmem : (⟨u, hX hu⟩ : R) ∈ (F4.reeLocalBlock K a j).subgroupOf R :=
        Subgroup.mem_subgroupOf.2 (reeFixedOrbitUnipotent_le_reeLocalBlock j hu)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hu1 (congrArg Subtype.val hmem)
    · intro g hg
      have hmem : (⟨g, hg⟩ : R) ∈ (F4.reeLocalBlock K a j).subgroupOf R := by
        rw [htop]
        trivial
      exact Subgroup.mem_subgroupOf.1 hmem
  have hMeq : F4.reeLocalBlock K a j = R := le_antisymm hMR hRM
  exact ⟨hMeq, hRM hnR, fun t ht => hRM (hTR ht)⟩

theorem large_Ree_opposite_simple_blocks_generate_rank_one_model
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (F4.reeLocalBlock K a ⟨0, by decide⟩ = rankOneGroupOne K a ∧
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
        F4.reeLocalBlock K a ⟨0, by decide⟩ ∧
      rankOneTorusOne K a ≤ F4.reeLocalBlock K a ⟨0, by decide⟩) ∧
    (F4.reeLocalBlock K a ⟨1, by decide⟩ = rankOneGroupTwo K a ∧
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
        F4.reeLocalBlock K a ⟨1, by decide⟩ ∧
      rankOneTorusTwo K a ≤ F4.reeLocalBlock K a ⟨1, by decide⟩) :=
  ⟨reeLocalBlock_eq_of_isSimpleGroup (rankOneTorusOne_le_reeFixedTorus hK) rfl
      (isSimpleGroup_rankOneGroupOne ha hK).1,
    reeLocalBlock_eq_of_isSimpleGroup (rankOneTorusTwo_le_reeFixedTorus hK) rfl
      (isSimpleGroup_rankOneGroupTwo ha hK).1⟩

end RankOne

end CFSG.QuasithinUnique.Setup.X6
