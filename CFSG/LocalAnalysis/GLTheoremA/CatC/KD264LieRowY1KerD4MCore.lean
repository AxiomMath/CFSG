module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3 QuadraticMap Module CFSG.GroupTheory.WeirSylow
  CFSG.RankThree.Classical

noncomputable section
open Classical

section Core

variable {K V Γ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group Γ] [Fintype Γ]

structure Setting (ρ : Γ →* Module.End K V) (Q : QuadraticForm K V) : Prop where
  h3 : (3 : K) ≠ 0
  hΓ : Nat.card Γ = 27
  hexp : ∀ g : Γ, g ^ 3 = 1
  hcomm : ∀ g h : Γ, g * h = h * g
  hnd : (polarBilin Q).Nondegenerate
  hQ : ∀ g v, Q (ρ g v) = Q v

variable {ρ : Γ →* Module.End K V} {Q : QuadraticForm K V}

theorem Setting.hB (hs : Setting ρ Q) (g : Γ) (u w : V) :
    polar Q (ρ g u) (ρ g w) = polar Q u w :=
  polar_map_of_isometry (T := ρ g) (hs.hQ g) u w

theorem Setting.oidem (hs : Setting ρ Q) (o : Option (Subgroup Γ)) : OIdem Q (Qf ρ o) :=
  ⟨Qf_idem hs.h3 hs.hΓ o, fun u v => by
    have := Qf_bilin (ρ := ρ) (polarBilin Q)
      (fun g u w => by simp only [QuadraticMap.polarBilin_apply_apply]; exact hs.hB g u w) o u v
    simpa only [QuadraticMap.polarBilin_apply_apply] using this⟩

theorem Setting.orth (hs : Setting ρ Q) {o₁ o₂ : Option (Subgroup Γ)} (hne : o₁ ≠ o₂) :
    Qf ρ o₁ * Qf ρ o₂ = 0 :=
  Qf_orth hs.h3 hs.hΓ hs.hexp hs.hcomm hne

theorem exists_not_mem_of_idx3 {F : Subgroup Γ} (hF : F ∈ idx3 Γ) : ∃ g : Γ, g ∉ F := by
  by_contra h
  push Not at h
  have : F = ⊤ := (Subgroup.eq_top_iff' F).2 h
  have h1 := (mem_idx3 F).1 hF
  rw [this, Subgroup.index_top] at h1
  exact absurd h1 (by norm_num)

theorem Setting.mem_range_Qf_map (hs : Setting ρ Q) (o : Option (Subgroup Γ)) (g : Γ) {x : V}
    (hx : x ∈ LinearMap.range (Qf ρ o)) : ρ g x ∈ LinearMap.range (Qf ρ o) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨ρ g y, ?_⟩
  have := congrArg (fun f : Module.End K V => f y) (commute_Qf (ρ := ρ) hs.hcomm o g)
  simpa [Module.End.mul_apply] using this.symm

theorem Setting.nondeg_Qf (hs : Setting ρ Q) (o : Option (Subgroup Γ)) :
    ∀ x ∈ LinearMap.range (Qf ρ o), (∀ y ∈ LinearMap.range (Qf ρ o), polar Q x y = 0) → x = 0 :=
  nondeg_range hs.hnd (hs.oidem o).idem (hs.oidem o).adj

theorem Setting.even_finrank (hs : Setting ρ Q) {F : Subgroup Γ} (hF : F ∈ idx3 Γ) :
    Even (finrank K (LinearMap.range (Qf ρ (some F)))) := by
  obtain ⟨g, hg⟩ := exists_not_mem_of_idx3 hF
  exact even_finrank_of_cube hs.h3 (T := ρ g) (fun x hx => hs.mem_range_Qf_map (some F) g hx)
    (fun x hx => sq_add_self_add_one hs.h3 hs.hΓ hs.hexp hs.hcomm hF hg hx) (hs.hQ g)
    (hs.nondeg_Qf (some F))

theorem Setting.isCubePlane (hs : Setting ρ Q) {F : Subgroup Γ} (hF : F ∈ idx3 Γ)
    (h2 : finrank K (LinearMap.range (Qf ρ (some F))) = 2) :
    IsCubePlane Q (LinearMap.range (Qf ρ (some F))) := by
  obtain ⟨g, hg⟩ := exists_not_mem_of_idx3 hF
  exact ⟨h2, ρ g, fun x hx => hs.mem_range_Qf_map (some F) g hx,
    fun x hx => sq_add_self_add_one hs.h3 hs.hΓ hs.hexp hs.hcomm hF hg hx, hs.hQ g⟩

theorem av_eq_add (hs : Setting ρ Q) {F : Subgroup Γ} (hF : F ∈ idx3 Γ) :
    av ρ F = Qf ρ none + Qf ρ (some F) := by
  rw [Qf_some_of_mem hF, Qf]
  abel

theorem finish (hs : Setting ρ Q) (hnp : ¬ IsPlusType Q) {F G G' : Subgroup Γ}
    (hF : F ∈ idx3 Γ) (hG : G ∈ idx3 Γ) (hG' : G' ∈ idx3 Γ) (hFG : F ≠ G) (hFG' : F ≠ G')
    (hGG' : G ≠ G')
    (hone : Qf ρ none + Qf ρ (some F) + (Qf ρ (some G) + Qf ρ (some G')) = 1)
    (hdim4 : finrank K (LinearMap.range (Qf ρ none)) +
      finrank K (LinearMap.range (Qf ρ (some F))) = 4)
    (hG2 : finrank K (LinearMap.range (Qf ρ (some G))) = 2)
    (hG'2 : finrank K (LinearMap.range (Qf ρ (some G'))) = 2) :
    finrank K (LinearMap.range (av ρ F)) = 4 ∧
      (∀ x ∈ LinearMap.range (av ρ F), (∀ y ∈ LinearMap.range (av ρ F), polar Q x y = 0) →
        x = 0) ∧
      ¬ IsPlusType (Q.comp (LinearMap.range (av ρ F)).subtype) := by
  have hn0F : (none : Option (Subgroup Γ)) ≠ some F := by simp
  have hn0G : (none : Option (Subgroup Γ)) ≠ some G := by simp
  have hn0G' : (none : Option (Subgroup Γ)) ≠ some G' := by simp
  have hFGo : (some F : Option (Subgroup Γ)) ≠ some G := fun h => hFG (Option.some.inj h)
  have hFG'o : (some F : Option (Subgroup Γ)) ≠ some G' := fun h => hFG' (Option.some.inj h)
  have hGG'o : (some G : Option (Subgroup Γ)) ≠ some G' := fun h => hGG' (Option.some.inj h)
  have o : ∀ {o₁ o₂ : Option (Subgroup Γ)}, o₁ ≠ o₂ → Qf ρ o₁ * Qf ρ o₂ = 0 :=
    fun h => hs.orth h
  have hu : OIdem Q (av ρ F) := by
    rw [av_eq_add hs hF]
    exact (hs.oidem none).add (hs.oidem (some F)) (o hn0F) (o hn0F.symm)
  have hdu : finrank K (LinearMap.range (av ρ F)) = 4 := by
    rw [av_eq_add hs hF, finrank_range_add (hs.oidem none).idem (hs.oidem (some F)).idem
      (o hn0F) (o hn0F.symm)]
    exact hdim4
  refine ⟨hdu, nondeg_range hs.hnd hu.idem hu.adj, ?_⟩
  refine not_plus_of_split hs.h3 hs.hnd hnp hu (hs.oidem (some G)) (hs.oidem (some G')) ?_ ?_ ?_ ?_
    (o hGG'o) (o hGG'o.symm) ?_ (d := 2) (by norm_num) (by rw [hdu]) (hs.isCubePlane hG hG2)
    (hs.isCubePlane hG' hG'2)
  · rw [av_eq_add hs hF, add_mul, o hn0G, o hFGo, add_zero]
  · rw [av_eq_add hs hF, mul_add, o hn0G.symm, o hFGo.symm, add_zero]
  · rw [av_eq_add hs hF, add_mul, o hn0G', o hFG'o, add_zero]
  · rw [av_eq_add hs hF, mul_add, o hn0G'.symm, o hFG'o.symm, add_zero]
  · rw [av_eq_add hs hF]
    exact hone

theorem core_orth (hs : Setting ρ Q) (hnp : ¬ IsPlusType Q) (hdim : finrank K V = 8)
    (hfaith : ∀ g : Γ, (∀ v : V, ρ g v = v) → g = 1) :
    ∃ F ∈ idx3 Γ, finrank K (LinearMap.range (av ρ F)) = 4 ∧
      (∀ x ∈ LinearMap.range (av ρ F), (∀ y ∈ LinearMap.range (av ρ F), polar Q x y = 0) →
        x = 0) ∧
      ¬ IsPlusType (Q.comp (LinearMap.range (av ρ F)).subtype) := by
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
      ∑ F ∈ S, finrank K (LinearMap.range (Qf ρ (some F))) = 8 := by
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
  have hS4 : S.card ≤ 4 := by omega
  have o : ∀ {F F' : Subgroup Γ}, F ≠ F' → Qf ρ (some F) * Qf ρ (some F') = 0 := fun h =>
    hs.orth (fun h' => h (Option.some.inj h'))
  have hcard : S.card = 3 ∨ S.card = 4 := by omega
  rcases hcard with h | h
  · obtain ⟨a, b, c, hab, hac, hbc, hSabc⟩ := Finset.card_eq_three.1 h
    have haS : a ∈ S := by rw [hSabc]; simp
    have hbS : b ∈ S := by rw [hSabc]; simp
    have hcS : c ∈ S := by rw [hSabc]; simp
    rw [hSabc, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton] at hdimsum hone
    have hea := Nat.even_iff.1 (hev a haS)
    have heb := Nat.even_iff.1 (hev b hbS)
    have hec := Nat.even_iff.1 (hev c hcS)
    have hga := hge a haS
    have hgb := hge b hbS
    have hgc := hge c hcS
    have key : (finrank K (LinearMap.range (Qf ρ none)) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some a))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some b))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some c))) = 2) ∨
      (finrank K (LinearMap.range (Qf ρ none)) = 0 ∧
        finrank K (LinearMap.range (Qf ρ (some a))) = 4 ∧
        finrank K (LinearMap.range (Qf ρ (some b))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some c))) = 2) ∨
      (finrank K (LinearMap.range (Qf ρ none)) = 0 ∧
        finrank K (LinearMap.range (Qf ρ (some a))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some b))) = 4 ∧
        finrank K (LinearMap.range (Qf ρ (some c))) = 2) ∨
      (finrank K (LinearMap.range (Qf ρ none)) = 0 ∧
        finrank K (LinearMap.range (Qf ρ (some a))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some b))) = 2 ∧
        finrank K (LinearMap.range (Qf ρ (some c))) = 4) := by omega
    have ia := hidx a haS
    have ib := hidx b hbS
    have ic := hidx c hcS
    rcases key with ⟨h0, h1, h2, h3'⟩ | ⟨h0, h1, h2, h3'⟩ | ⟨h0, h1, h2, h3'⟩ | ⟨h0, h1, h2, h3'⟩
    · exact ⟨a, ia, finish hs hnp ia ib ic hab hac hbc (by rw [← add_assoc] at hone; exact hone)
        (by omega) h2 h3'⟩
    · exact ⟨a, ia, finish hs hnp ia ib ic hab hac hbc (by rw [← add_assoc] at hone; exact hone)
        (by omega) h2 h3'⟩
    · exact ⟨b, ib, finish hs hnp ib ia ic hab.symm hbc hac
        (by rw [← hone]; abel) (by omega) h1 h3'⟩
    · exact ⟨c, ic, finish hs hnp ic ia ib hac.symm hbc.symm hab
        (by rw [← hone]; abel) (by omega) h1 h2⟩
  · exfalso
    obtain ⟨a, T, haT, hTS, hTc⟩ := Finset.card_eq_succ.1 h
    obtain ⟨b, c, d, hbc, hbd, hcd, hTbcd⟩ := Finset.card_eq_three.1 hTc
    have haS : a ∈ S := by rw [← hTS]; simp
    have hbS : b ∈ S := by rw [← hTS, hTbcd]; simp
    have hcS : c ∈ S := by rw [← hTS, hTbcd]; simp
    have hdS : d ∈ S := by rw [← hTS, hTbcd]; simp
    have hab : a ≠ b := by
      rintro rfl
      apply haT
      rw [hTbcd]
      simp
    have hac : a ≠ c := by
      rintro rfl
      apply haT
      rw [hTbcd]
      simp
    have had : a ≠ d := by
      rintro rfl
      apply haT
      rw [hTbcd]
      simp
    rw [← hTS, Finset.sum_insert haT, hTbcd, Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]), Finset.sum_singleton] at hdimsum hone
    have hga := hge a haS
    have hgb := hge b hbS
    have hgc := hge c hcS
    have hgd := hge d hdS
    have hd0 : finrank K (LinearMap.range (Qf ρ none)) = 0 := by omega
    have ha2 : finrank K (LinearMap.range (Qf ρ (some a))) = 2 := by omega
    have hb2 : finrank K (LinearMap.range (Qf ρ (some b))) = 2 := by omega
    have hc2 : finrank K (LinearMap.range (Qf ρ (some c))) = 2 := by omega
    have hd2 : finrank K (LinearMap.range (Qf ρ (some d))) = 2 := by omega
    have hQ0 : Qf ρ none = 0 :=
      LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 hd0)
    rw [hQ0, zero_add] at hone
    exact false_of_four_planes hs.h3 hs.hnd hnp (hs.oidem (some a)) (hs.oidem (some b))
      (hs.oidem (some c)) (hs.oidem (some d)) (o hab) (o hab.symm) (o hac) (o hac.symm) (o had)
      (o had.symm) (o hbc) (o hbc.symm) (o hbd) (o hbd.symm) (o hcd) (o hcd.symm)
      (by rw [← hone]; abel) (hs.isCubePlane (hidx a haS) ha2) (hs.isCubePlane (hidx b hbS) hb2)
      (hs.isCubePlane (hidx c hcS) hc2) (hs.isCubePlane (hidx d hdS) hd2)

end Core

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
