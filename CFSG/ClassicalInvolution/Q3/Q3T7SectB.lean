module

public import CFSG.ClassicalInvolution.Q3.Q3T7SectA
public import CFSG.ClassicalInvolution.Uniform.U8Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.Blueprint
open scoped MatrixGroups commutatorElement

section Sect


variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_mulEquiv_m11_sect (D : OmegaLieU 3 1 Φ) (hgen : omegaGen Φ = ⊤)
    (hcard : D.card = 1) (i : Fin D.card) (hc : D.kind i = Q3.CompData.m11) :
    Nonempty (↥NativeSporadic.M11 ≃* X) := by
  have hsurj : Function.Surjective (castHom hc (D.hom i)) := by
    have h := hom_surjective_of_gen3 D hcard hgen i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  have hinj : Function.Injective (castHom hc (D.hom i)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)).trans
      (Q3.center_m11_eq_bot Q3.m11Facts).le
  exact ⟨MulEquiv.ofBijective (castHom hc (D.hom i)) ⟨hinj, hsurj⟩⟩

theorem top_mem_of_sl23_component_sect (D : OmegaLieU 3 1 Φ) (hne : Φ.Nonempty)
    (hgen : omegaGen Φ = ⊤) (hcard : D.card = 1) (i : Fin D.card)
    (hc : D.kind i = Q3.CompData.sl23) : (⊤ : Subgroup X) ∈ Φ := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨j, R, hR, hKR⟩ := D.fundamental K hK
  obtain rfl : j = i := Fin.ext (by have := i.2; have := j.2; omega)
  obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom j) hR
  have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
  have hsurj := hom_surjective_of_gen3 D hcard hgen j
  have hKtop : K = ⊤ := by
    rw [hKR, ← hRR, hR'top, Subgroup.map_top, range_castHom]
    exact MonoidHom.range_eq_top.mpr hsurj
  exact hKtop ▸ hK

theorem ih8TwinShapeSectU_proved :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
      HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ), Ih8Model 3 1 Ω t k e →
            t ≠ .G2 → t ≠ .trialityD4 → (∃ K ∈ Ω, ∃ K' ∈ twinSet Ω K, K' ≠ K) →
              ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ IsOrthTag d ε t k := by
  intro G _ _ Ω hΩ hA htrans t k e M hG2 hD4 hK
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

theorem thm6SectBelowU_of {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSect3 Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ → DEdgeless Φ →
        HasLieTypeU 3 1 Φ .PSL 3 ∨ HasLieTypeU 3 1 Φ .PSU 3 ∨ HasLieTypeU 3 1 Φ .G2 0 ∨
          HasLieTypeU 3 1 Φ .trialityD4 0 ∨ HasM11TypeU 3 1 Φ := by
  intro X _ _ hlt Φ h hne hTop hDE
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨D, hcard⟩ := exists_omegaLieU_sect hn hlt h.hyp h.oddCore h.gen h.trans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Φ t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    by_cases hG2 : t = .G2
    · subst hG2
      obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inl hLie))
    by_cases hD4 : t = .trialityD4
    · subst hD4
      have hk : k = 0 := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inr (Or.inl hLie)))
    by_cases hL3 : t = .PSL ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hL3
      exact Or.inl hLie
    by_cases hU3 : t = .PSU ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hU3
      exact Or.inr (Or.inl hLie)
    exfalso
    have hef : e = 1 := (he.resolve_right fun h => hD4 h.1)
    subst hef
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have h3' : ¬ ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) := by
      rintro (h | h)
      · exact hL3 h
      · exact hU3 h
    let M := toIh8ModelSect D h.hyp h.gen hcard i ht hadm he hc
    obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
    obtain ⟨R, hR, S, hS, hRS⟩ := exists_commuting_fund hp2 ht hadm hG2 hD4 hA1 h3' (M.cls_sub hR₀)
    have hK := M.map_mem (M.fund_subset_cls hne hG2 hD4 hR)
    have hJ := M.map_mem (M.fund_subset_cls hne hG2 hD4 hS)
    have hcomm : Commutes (R.map M.ψ) (S.map M.ψ) := ih8_commutes_map M.ψ hRS
    obtain ⟨z, hz⟩ := h.hyp.classical _ hK
    obtain ⟨x, hx, y, hy, hxy⟩ := hz.exists_noncomm
    have hne' : R.map M.ψ ≠ S.map M.ψ := by
      intro h
      rw [← h] at hcomm
      exact hxy (hcomm x hx y hy)
    exact hDE _ hK _ hJ (Disconnected.dAdj_of_commutes hJ hne' hcomm)
  · exact (hTop (top_mem_of_sl23_component_sect D hne h.gen hcard i hc)).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, D, hcard, i, hc⟩)))

theorem thm7SectBelowU_of {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSect3 Φ →
        ∀ K ∈ Φ, (∃ K' ∈ twinSet Φ K, K' ≠ K) →
          ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ HasOrthTypeU 3 1 Φ d ε := by
  intro X _ _ hlt Φ h K hK hK'
  obtain ⟨K', hK'Ω, hne'⟩ := hK'
  have hne : Φ.Nonempty := ⟨K, hK⟩
  obtain ⟨D, hcard⟩ := exists_omegaLieU_sect hn hlt h.hyp h.oddCore h.gen h.trans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Φ t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    let M := toIh8ModelSect D h.hyp h.gen hcard i ht hadm he hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exact absurd (noTwins_of_g2d4_datum M h.trans hG2d4 K hK K' hK'Ω) hne'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    obtain ⟨d, ε, hd, hdε⟩ := ih8TwinShapeSectU_proved X Φ h.hyp h.aEmpty h.trans t k e M hG2 hD4
      ⟨K, hK, K', hK'Ω, hne'⟩
    exact ⟨d, ε, hd, t, k, hdε, hLie⟩
  · exact absurd (top_mem_of_sl23_component_sect D hne h.gen hcard i hc)
      (top_notMem_of_transitive3 h.trans hK hK'Ω.1 hne')
  · obtain ⟨e⟩ := exists_mulEquiv_m11_sect D h.gen hcard i hc
    exact absurd (noTwins_of_mulEquiv_m11 e h.hyp K hK K' hK'Ω) hne'

end Sect

end CFSG.ClassicalInvolution.Q3.Q3T7
