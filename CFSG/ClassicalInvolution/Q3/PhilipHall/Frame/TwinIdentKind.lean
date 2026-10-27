module

public import CFSG.ClassicalInvolution.Q3.Q3T7SectB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentLie
public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdent
open scoped MatrixGroups

section TwinIdent


theorem twinIdent_shape {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hK : ∃ K ∈ Ω, ∃ K' ∈ twinSet Ω K, K' ≠ K) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ IsOrthTag d ε t k := by
  obtain ⟨K, hK, K', hK', hne'⟩ := hK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨R', hR', rfl⟩ := (M.mem_iff K').mp hK'Ω
  have hRR' : R ≠ R' := fun h => hne' (by rw [h])
  have hmtc := modelTwinClass_two3 M hΩ ⟨_, hK⟩ hG2 hD4 hR hR' hRR' hzK hzK'
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hadm := M.admissible
  have hfund := M.isFundTag
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  cases t
  · have hk3 : 3 ≤ k := by
      have h1 := hadm.2.2.1
      have h2 : k ≠ 2 := fun hk => hadm.2.2.2.2 (by simp [hk])
      omega
    obtain ⟨hk4, -⟩ := modelTwinClass_psl hp2 hk3 le_rfl hmtc
    exact ⟨6, true, by norm_num, Or.inr (Or.inl ⟨rfl, rfl, rfl, hk4⟩)⟩
  · obtain ⟨hk4, -⟩ := modelTwinClass_psu hp2 hadm le_rfl hmtc
    exact ⟨6, false, by norm_num, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hk4⟩))⟩
  · obtain ⟨hk2, -⟩ := modelTwinClass_psp hp2 hadm le_rfl hmtc
    exact ⟨5, true, by norm_num, Or.inl ⟨rfl, rfl, hk2⟩⟩
  · have hk3 : 3 ≤ k := hadm.2.2.1
    exact ⟨2 * k + 1, true, by omega, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega, rfl, rfl⟩)))⟩
  · have hk4 : 4 ≤ k := hadm.2.2
    exact ⟨2 * k, true, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
  · have hk4 : 4 ≤ k := hadm.2.2
    exact ⟨2 * k, false, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
  · exact absurd rfl hG2
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (excLayer3 _ k (by simp) hadm)
      le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (excLayer3 _ k (by simp) hadm)
      le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (excLayer3 _ k (by simp) hadm)
      le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (excLayer3 _ k (by simp) hadm)
      le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (excLayer3 _ k (by simp) hadm)
      le_rfl)
  · exact absurd rfl hD4
  all_goals exact absurd hfund (by simp [IsFundTag])

theorem twinIdent_lieSystem {X : Type} [Group X] [Finite X] {Λ : Set (Subgroup X)}
    {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hlt : Nat.card X < n)
    (hΛ : HypOmegaModU (.sl2 3 1) Λ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Λ = ⊤) (htrans : ∀ K ∈ Λ, ∀ L ∈ Λ, ∃ g : X, conjSub g K = L)
    (hK : ∃ K ∈ Λ, ∃ K' ∈ twinSet Λ K, K' ≠ K) :
    ∃ (ι : Type) (D : LieSystemData3 ι X Λ) (i : ι), (∀ j, j = i) ∧
      ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
        IsOrthTag d ε tag k ∧ D.kind i = CompData.model tag k := by
  obtain ⟨K, hKΛ, K', hK'Λ, hne'⟩ := hK
  have hne : Λ.Nonempty := ⟨K, hKΛ⟩
  obtain ⟨D, hcard⟩ := exists_omegaLieU_sect hn hlt hΛ hO hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  have hone : ∀ j : Fin D.card, j = i := fun j => Fin.ext (by have := j.2; omega)
  refine ⟨Fin D.card, D.toLieSystemData3 hgen, i, hone, ?_⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩
      · exact he
      · omega
    subst he1
    let M := toIh8ModelSect D hΛ hgen hcard i ht hadm (Or.inl rfl) hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exact absurd (noTwins_of_g2d4_datum M htrans hG2d4 K hKΛ K' hK'Λ) hne'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    obtain ⟨d, ε, hd, hdε⟩ := twinIdent_shape hΛ M hG2 hD4 ⟨K, hKΛ, K', hK'Λ, hne'⟩
    exact ⟨t, k, d, ε, hd, hdε, hc⟩
  · exact absurd (top_mem_of_sl23_component_sect D hne hgen hcard i hc)
      (top_notMem_of_transitive3 htrans hKΛ hK'Λ.1 hne')
  · obtain ⟨e⟩ := exists_mulEquiv_m11_sect D hgen hcard i hc
    exact absurd (noTwins_of_mulEquiv_m11 e hΛ K hKΛ K' hK'Λ) hne'

end TwinIdent

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
