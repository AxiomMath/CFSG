module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactGraph
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactClass
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
open CFSG.AGLEmbeddingD2.Tits.GN516
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

omit [Finite K] [Finite Y] in
theorem exists_eq_map_parJ_of_le (h : BorelQuotient D n H π M) {Q : Subgroup Y}
    (hQ : (borel D H).map π ≤ Q) : ∃ J : Set (Fin D.rank), Q = (parJ D H J).map π := by
  refine ⟨negIndices D (Q.comap π), ?_⟩
  rw [← eq_parJ_negIndices h.ct h.extras (Subgroup.map_le_iff_le_comap.1 hQ),
    Subgroup.map_comap_eq_self_of_surjective h.surj]

omit [Finite Y] in
theorem exists_sylow_eq_map_posUnipotent (h : BorelQuotient D n H π M) :
    ∃ U₀ : Sylow 2 Y, (U₀ : Subgroup Y) = (posUnipotent D).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent D).map π).index := fun hd =>
    h.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ h.surj))
  exact ⟨(hU2.map π).toSylow hidx, by rw [IsPGroup.toSylow_coe]⟩

theorem nodePerm_pow_eq_one (h : BorelQuotient D n H π M) {θ : MulAut Y}
    (hθ : ((posUnipotent D).map π).map θ.toMonoidHom = (posUnipotent D).map π) {m : ℕ}
    (hm : θ ^ m ∈ inner Y) : Nodes.nodePerm h θ hθ ^ m = 1 := by
  have hcongr : ∀ (α β : MulAut Y)
      (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
      (hβ : ((posUnipotent D).map π).map β.toMonoidHom = (posUnipotent D).map π),
      α = β → Nodes.nodePerm h α hα = Nodes.nodePerm h β hβ := by
    rintro α β hα hβ rfl
    rfl
  have hinner : ∀ (α : MulAut Y)
      (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π),
      α ∈ inner Y → Nodes.nodePerm h α hα = 1 := by
    rintro α hα ⟨z, rfl⟩
    have hz : z ∈ (borel D H).map π := by
      rw [← h.normalizer_map_posUnipotent]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hα
    refine Equiv.ext fun j => (Nodes.nodePerm_eq_iff h _ hα j j).2 ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1
      (Subgroup.le_normalizer (Subgroup.map_mono (borel_le_parJ {j}) hz))
  have hpow : ∀ k : ℕ,
      ((posUnipotent D).map π).map (θ ^ k).toMonoidHom = (posUnipotent D).map π := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      exact Subgroup.map_id _
    | succ k ih =>
      rw [pow_succ]
      exact Nodes.posUnipotent_map_mulAut_mul _ _ ih hθ
  have hperm : ∀ k : ℕ, Nodes.nodePerm h θ hθ ^ k = Nodes.nodePerm h (θ ^ k) (hpow k) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      exact (hinner _ _ ⟨1, by rw [map_one, pow_zero]⟩).symm
    | succ k ih =>
      rw [pow_succ, ih, ← Nodes.nodePerm_mul]
      exact hcongr _ _ _ _ (pow_succ θ k).symm
  rw [hperm m]
  exact hinner _ _ hm

theorem parabolicClassFixed_of_borelQuotient [IsSimpleGroup Y] (h : BorelQuotient D n H π M) :
    ParabolicClassFixed Y := by
  by_cases hnc : ∃ a b : Y, a * b ≠ b * a
  · obtain ⟨U₀, hU₀⟩ := exists_sylow_eq_map_posUnipotent h
    have hN : Subgroup.normalizer ((U₀ : Subgroup Y) : Set Y) = (borel D H).map π := by
      rw [hU₀]
      exact h.normalizer_map_posUnipotent
    intro P hP α hα
    obtain ⟨g, hg⟩ := exists_le_map_conj_of_isParabolicTwo U₀ hN hP
    obtain ⟨z, hz⟩ := exists_map_conj_inv_mul_eq U₀ α
    rw [hU₀] at hz
    have hθm : ((MulAut.conj z)⁻¹ * α) ^ orderOf α ∈ inner Y :=
      pow_orderOf_mem_inner (inv_mem ⟨z, rfl⟩)
    have hσ : Nodes.nodePerm h _ hz = 1 :=
      eq_one_of_diagram_perm D.isFiniteType (Conn.diagram_connected h hnc)
        (Core.nodePerm_adj_iff h _ hz) hα (nodePerm_pow_eq_one h hz hθm)
    obtain ⟨J, hJ⟩ := exists_eq_map_parJ_of_le h hg
    refine exists_map_eq_map_conj_of_map_eq (g := g) (h := z) ?_
    rw [hJ, Nodes.map_parJ_nodePerm h _ hz J, hσ, Equiv.Perm.coe_one, Set.image_id]
  · simp only [not_exists, not_not] at hnc
    exact parabolicClassFixed_of_forall_commute hnc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
