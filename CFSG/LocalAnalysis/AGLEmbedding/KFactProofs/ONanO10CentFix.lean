module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfMain
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.AGLEmbedding.O10Cent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent
  CFSG.AGLEmbedding.OmegaMinusPerf

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

theorem exists_perfect_fix_of_perfect (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v)
    (D₀ : Subgroup (↥(fixSpace x) ≃ₗ[ZMod 2] ↥(fixSpace x)))
    (hD₀ : D₀ ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x)))
    (hperf : ⁅D₀, D₀⁆ = D₀) (h3 : 3 ∣ Nat.card D₀) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hcψ := fixProj_comp_subtype hx3
  have hort : ∀ v a, polar Q (v + (fixSpace x).subtype (fixProj hx3 v)) ((fixSpace x).subtype a) =
      0 := fun v a => by
    rw [polar_comm]
    exact polar_fix_move hx a.2 (add_fixProj_mem_move hx3 v)
  have hinj : Function.Injective (extHom hcψ) := by
    intro S T hST
    apply LinearEquiv.ext
    intro a
    have h := LinearEquiv.congr_fun hST ((fixSpace x).subtype a)
    rw [extHom_apply, extHom_apply, extEquiv_apply', extEquiv_apply'] at h
    have hc1 : fixProj hx3 ((fixSpace x).subtype a) = a := LinearMap.congr_fun hcψ a
    rw [hc1, add_self_eq_zero', zero_add, zero_add] at h
    exact Subtype.ext h
  refine ⟨D₀.map (extHom hcψ), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨T, hT', rfl⟩
    refine extEquiv_mem_orthogonalGroup hcψ hort fun a => ?_
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hD₀ hT') a
    exact this
  · rintro _ ⟨T, hT', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact extEquiv_commute hcψ (τ := LinearEquiv.refl (ZMod 2) ↥(fixSpace x)) (T := T)
      (fun a => mem_fixSpace.1 a.2) (fun v => fixProj_apply_apply hx3 v) (fun a => rfl)
  · rw [← Subgroup.map_commutator, hperf]
  · rw [Subgroup.card_map_of_injective hinj]
    exact h3

theorem commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_perfect_of_minus_six [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) (hdim : finrank (ZMod 2) (fixSpace x) = 6)
    (hts : ∀ T : Submodule (ZMod 2) ↥(fixSpace x), finrank (ZMod 2) T = 3 →
      ∃ u ∈ T, (Q.restrict (fixSpace x)) u ≠ 0) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hq : (polarBilin (Q.restrict (fixSpace x))).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fix hQ hx hx3)
  obtain ⟨-, hperf, -, -, -, -, h6⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (Q.restrict (fixSpace x)) hq (Or.inr hdim) (fun T hT => hts T (by rw [hT, hdim]))
  obtain ⟨E, _, _, D, ψ, ρ, _, _, hinj, hrange, hcard⟩ := h6 hdim
  have hJcard : 3 ∣ Nat.card (⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x)),
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x))⁆ :
        Subgroup (↥(fixSpace x) ≃ₗ[ZMod 2] ↥(fixSpace x))) := by
    rw [← hrange, hcard, Nat.card_zmod]
    exact ⟨2 ^ 6 * 3 * 9 * 5, by norm_num⟩
  exact exists_perfect_fix_of_perfect hx hx3 _ (commutator_self_le _)
    (Subgroup.isPerfect_iff.1 hperf) hJcard

theorem exists_perfect_cent_ne_three [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) {PsM : List (AnisoPair Q)} (hlen : PsM.length ≤ 5)
    (hpw : PsM.Pairwise AnisoPair.Orth) (hmem : ∀ P ∈ PsM, P.a ∈ moveSpace x ∧ P.b = x P.a)
    (hCdim : finrank (ZMod 2) (fixSpace x) = 2 * (5 - PsM.length)) (hne : PsM.length ≠ 3) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  by_cases hk : 4 ≤ PsM.length
  · exact exists_perfect_of_frame hx (Frame.ofList PsM hpw hmem) hk
  · have hq : (polarBilin (Q.restrict (fixSpace x))).Nondegenerate :=
      nondegenerate_polarBilin_restrict (polarNondegOn_fix hQ hx hx3)
    have hc : 3 ≤ 5 - PsM.length := by omega
    by_cases hT : ∃ T : Submodule (ZMod 2) ↥(fixSpace x), 3 ≤ finrank (ZMod 2) T ∧
        ∀ y ∈ T, (Q.restrict (fixSpace x)) y = 0
    · exact exists_perfect_fix hQ hx hx3 hc hCdim hT
    · have hc3 : 5 - PsM.length = 3 := by
        by_contra hne3
        rcases exists_totSing_or_three_planes hq hc hCdim with h | ⟨h3, -⟩
        · exact hT h
        · exact hne3 h3
      refine exists_perfect_of_minus_six hQ hx hx3 (by omega) fun T hT3 => ?_
      by_contra hcon
      push Not at hcon
      exact hT ⟨T, by omega, hcon⟩

end CFSG.AGLEmbedding.O10Cent
