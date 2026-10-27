module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3 CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
  QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.RankThree.Classical

noncomputable section
open Classical

section Core7

variable {K V Γ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group Γ] [Fintype Γ]

variable {ρ : Γ →* Module.End K V} {Q : QuadraticForm K V}

theorem core7 (hs : Setting ρ Q) (hdim : finrank K V = 7)
    (hfaith : ∀ g : Γ, (∀ v : V, ρ g v = v) → g = 1) :
    ∃ F ∈ idx3 Γ, finrank K (LinearMap.range (av ρ F)) = 3 ∧
      (∀ x ∈ LinearMap.range (av ρ F), (∀ y ∈ LinearMap.range (av ρ F), polar Q x y = 0) →
        x = 0) := by
  have hint : DirectSum.IsInternal (fun o => LinearMap.range (Qf ρ o)) :=
    CFSG.RankThree.Classical.isInternal_range_of_orthogonal_idempotents (Qf ρ)
      (fun o => (hs.oidem o).idem) (fun o₁ o₂ hne => hs.orth hne)
      (Qf_sum hs.h3 hs.hΓ hs.hexp hs.hcomm)
  have hfinrank : finrank K V = ∑ o, finrank K (LinearMap.range (Qf ρ o)) := by
    have h1 := finrank_biSup_of_iSupIndep hint.submodule_iSupIndep Finset.univ
    have htop : (⨆ i ∈ (Finset.univ : Finset (Option (Subgroup Γ))),
        LinearMap.range (Qf ρ i)) = ⊤ := by
      simp only [Finset.mem_univ, iSup_pos]
      exact hint.submodule_iSup_eq_top
    rw [htop, finrank_top] at h1
    exact h1
  set S : Finset (Subgroup Γ) :=
    (idx3 Γ).filter (fun F => LinearMap.range (Qf ρ (some F)) ≠ ⊥) with hS
  have hzero : ∀ F, F ∉ S → Qf ρ (some F) = 0 := by
    intro F hF
    by_cases hmem : F ∈ idx3 Γ
    · have : LinearMap.range (Qf ρ (some F)) = ⊥ := by
        by_contra hr
        exact hF (Finset.mem_filter.2 ⟨hmem, hr⟩)
      exact LinearMap.range_eq_bot.1 this
    · exact Qf_some_of_not_mem hmem
  have hsumS : ∑ F ∈ S, finrank K (LinearMap.range (Qf ρ (some F))) =
      ∑ F : Subgroup Γ, finrank K (LinearMap.range (Qf ρ (some F))) := by
    refine Finset.sum_subset (Finset.subset_univ S) (fun F _ hF => ?_)
    rw [hzero F hF, LinearMap.range_zero, finrank_bot]
  have hdimsum : finrank K (LinearMap.range (Qf ρ none)) +
      ∑ F ∈ S, finrank K (LinearMap.range (Qf ρ (some F))) = 7 := by
    rw [hsumS, ← hdim, hfinrank, Fintype.sum_option]
  have hone : Qf ρ none + ∑ F ∈ S, Qf ρ (some F) = 1 := by
    have h := Qf_sum (ρ := ρ) hs.h3 hs.hΓ hs.hexp hs.hcomm
    rw [Fintype.sum_option] at h
    rw [← h]
    congr 1
    exact Finset.sum_subset (Finset.subset_univ S) (fun F _ hF => hzero F hF)
  have hidx : ∀ F ∈ S, F ∈ idx3 Γ := fun F hF => (Finset.mem_filter.1 hF).1
  have hev : ∀ F ∈ S, Even (finrank K (LinearMap.range (Qf ρ (some F)))) := fun F hF =>
    hs.even_finrank (hidx F hF)
  have hge : ∀ F ∈ S, 2 ≤ finrank K (LinearMap.range (Qf ρ (some F))) := by
    intro F hF
    have hne := (Finset.mem_filter.1 hF).2
    have hpos : 1 ≤ finrank K (LinearMap.range (Qf ρ (some F))) :=
      Submodule.one_le_finrank_iff.2 hne
    obtain ⟨m, hm⟩ := hev F hF
    omega
  have hA2 : S.card * 2 ≤ ∑ F ∈ S, finrank K (LinearMap.range (Qf ρ (some F))) := by
    have := Finset.card_nsmul_le_sum S (fun F => finrank K (LinearMap.range (Qf ρ (some F)))) 2 hge
    simpa using this
  have hS3 : 3 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg1, hgF⟩ := exists_common_nontrivial hs.hΓ S
      (fun F hF => (mem_idx3 F).1 (hidx F hF)) (by omega)
    apply hg1
    apply hfaith g
    intro v
    rw [decomp (ρ := ρ) hs.h3 hs.hΓ hs.hexp hs.hcomm v, map_sum]
    apply Finset.sum_congr rfl
    intro o _
    cases o with
    | none =>
      have := congrArg (fun f : Module.End K V => f v) (left_mul_avTop (ρ := ρ) g)
      simpa [Module.End.mul_apply, Qf] using this
    | some F =>
      by_cases hr : LinearMap.range (Qf ρ (some F)) = ⊥
      · have h0 : Qf ρ (some F) = 0 := LinearMap.range_eq_bot.1 hr
        rw [h0, LinearMap.zero_apply, map_zero]
      · have hmem : F ∈ idx3 Γ := by
          by_contra hn
          exact hr (by rw [Qf_some_of_not_mem hn, LinearMap.range_zero])
        have hFS : F ∈ S := Finset.mem_filter.2 ⟨hmem, hr⟩
        have hgFg := hgF F hFS
        have := congrArg (fun f : Module.End K V => f v)
          (show ρ g * Qf ρ (some F) = Qf ρ (some F) by
            rw [Qf_some_of_mem hmem, mul_sub, left_mul_av hgFg, left_mul_avTop g])
        simpa [Module.End.mul_apply] using this
  have hS4 : S.card ≤ 3 := by omega
  have hcardS : S.card = 3 := by omega
  obtain ⟨a, b, c, hab, hac, hbc, hSabc⟩ := Finset.card_eq_three.1 hcardS
  have haS : a ∈ S := by rw [hSabc]; simp
  have hbS : b ∈ S := by rw [hSabc]; simp
  have hcS : c ∈ S := by rw [hSabc]; simp
  have hsum3 := hdimsum
  rw [hSabc, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at hsum3
  have hga := hge a haS
  have hgb := hge b hbS
  have hgc := hge c hcS
  obtain ⟨ma, hma⟩ := hev a haS
  obtain ⟨mb, hmb⟩ := hev b hbS
  obtain ⟨mc, hmc⟩ := hev c hcS
  have hdim_a : finrank K (LinearMap.range (Qf ρ (some a))) = 2 := by omega
  have hn0a : (none : Option (Subgroup Γ)) ≠ some a := by simp
  have hoa : ∀ {o₁ o₂ : Option (Subgroup Γ)}, o₁ ≠ o₂ → Qf ρ o₁ * Qf ρ o₂ = 0 :=
    fun h => hs.orth h
  have hu : OIdem Q (av ρ a) := by
    rw [av_eq_add hs (hidx a haS)]
    exact (hs.oidem none).add (hs.oidem (some a)) (hoa hn0a) (hoa hn0a.symm)
  have hdu : finrank K (LinearMap.range (av ρ a)) = 3 := by
    rw [av_eq_add hs (hidx a haS), finrank_range_add (hs.oidem none).idem (hs.oidem (some a)).idem
      (hoa hn0a) (hoa hn0a.symm)]
    omega
  exact ⟨a, hidx a haS, hdu, nondeg_range hs.hnd hu.idem hu.adj⟩

end Core7

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

end
