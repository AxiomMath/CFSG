module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Avg
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open Subgroup CFSG.RankThree.Classical

noncomputable section
open Classical

section Core

variable {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group Γ] [Fintype Γ]

theorem natCard_ne_zero' (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (D : Subgroup Γ) :
    (Nat.card D : K) ≠ 0 := by
  have hdvd : Nat.card D ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card D
    rw [hΓ] at this
    exact this
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hk]
  push_cast
  exact pow_ne_zero _ h3

theorem left_mul_av {ρ : Γ →* Module.End K V} {D : Subgroup Γ} {g : Γ} (hg : g ∈ D) :
    ρ g * av ρ D = av ρ D := by
  simp only [av]
  rw [mul_smul_comm, sum_left_mul ρ hg]

theorem left_mul_avTop {ρ : Γ →* Module.End K V} (g : Γ) :
    ρ g * av ρ ⊤ = av ρ ⊤ :=
  left_mul_av (Subgroup.mem_top g)

@[expose] def Qf (ρ : Γ →* Module.End K V) : Option (Subgroup Γ) → Module.End K V
  | none => av ρ ⊤
  | some F => if F ∈ idx3 Γ then av ρ F - av ρ ⊤ else 0

variable {ρ : Γ →* Module.End K V}

theorem Qf_some_of_mem {F : Subgroup Γ} (hF : F ∈ idx3 Γ) :
    Qf ρ (some F) = av ρ F - av ρ ⊤ := by
  simp only [Qf, if_pos hF]

theorem Qf_some_of_not_mem {F : Subgroup Γ} (hF : F ∉ idx3 Γ) : Qf ρ (some F) = 0 := by
  simp only [Qf, if_neg hF]

theorem av_top_mul_top (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) :
    av ρ ⊤ * av ρ ⊤ = av ρ ⊤ :=
  av_mul_self ρ (natCard_ne_zero' h3 hΓ ⊤)

theorem Qf_idem (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (o : Option (Subgroup Γ)) :
    Qf ρ o * Qf ρ o = Qf ρ o := by
  cases o with
  | none => exact av_top_mul_top h3 hΓ
  | some F =>
    by_cases hF : F ∈ idx3 Γ
    · rw [Qf_some_of_mem hF]
      rw [sub_mul, mul_sub, mul_sub, av_mul_self ρ (natCard_ne_zero' h3 hΓ F),
        av_mul_avTop ρ F (natCard_ne_zero' h3 hΓ F), top_mul_av ρ F (natCard_ne_zero' h3 hΓ F),
        av_top_mul_top h3 hΓ]
      abel
    · rw [Qf_some_of_not_mem hF]
      simp

theorem Qf_orth (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) {o₁ o₂ : Option (Subgroup Γ)} (hne : o₁ ≠ o₂) :
    Qf ρ o₁ * Qf ρ o₂ = 0 := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => exact absurd rfl hne
    | some F =>
      by_cases hF : F ∈ idx3 Γ
      · rw [Qf, Qf_some_of_mem hF, mul_sub, top_mul_av ρ F (natCard_ne_zero' h3 hΓ F),
          av_top_mul_top h3 hΓ, sub_self]
      · rw [Qf_some_of_not_mem hF, mul_zero]
  | some F₁ =>
    cases o₂ with
    | none =>
      by_cases hF : F₁ ∈ idx3 Γ
      · rw [Qf_some_of_mem hF, Qf, sub_mul, av_mul_avTop ρ F₁ (natCard_ne_zero' h3 hΓ F₁),
          av_top_mul_top h3 hΓ, sub_self]
      · rw [Qf_some_of_not_mem hF, zero_mul]
    | some F₂ =>
      have hne' : F₁ ≠ F₂ := fun h => hne (by rw [h])
      by_cases h1 : F₁ ∈ idx3 Γ
      · by_cases h2 : F₂ ∈ idx3 Γ
        · rw [Qf_some_of_mem h1, Qf_some_of_mem h2, sub_mul, mul_sub, mul_sub,
            av_mul_av_of_ne ρ hΓ h3 ((mem_idx3 F₁).1 h1) ((mem_idx3 F₂).1 h2) hne',
            av_mul_avTop ρ F₁ (natCard_ne_zero' h3 hΓ F₁),
            top_mul_av ρ F₂ (natCard_ne_zero' h3 hΓ F₂), av_top_mul_top h3 hΓ]
          abel
        · rw [Qf_some_of_not_mem h2, mul_zero]
      · rw [Qf_some_of_not_mem h1, zero_mul]

theorem Qf_sum (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) : ∑ o, Qf ρ o = 1 := by
  rw [Fintype.sum_option]
  have h1 : ∑ F : Subgroup Γ, Qf ρ (some F) = ∑ F ∈ idx3 Γ, (av ρ F - av ρ ⊤) := by
    simp only [Qf]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Finset.sum_sub_distrib, sum_av_idx3 ρ hΓ hexp hcomm h3, Finset.sum_const,
    card_idx3 hΓ hexp hcomm, Qf]
  rw [← Nat.cast_smul_eq_nsmul K 13]
  module

theorem decomp (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) (v : V) : v = ∑ o, Qf ρ o v := by
  have h := congrArg (fun f : Module.End K V => f v) (Qf_sum (ρ := ρ) h3 hΓ hexp hcomm).symm
  simpa [LinearMap.sum_apply, Module.End.one_apply] using h

theorem Qf_bilin (B : LinearMap.BilinForm K V)
    (hB : ∀ (g : Γ) (u w : V), B (ρ g u) (ρ g w) = B u w) (o : Option (Subgroup Γ)) (u v : V) :
    B (Qf ρ o u) v = B u (Qf ρ o v) := by
  cases o with
  | none => exact bilin_av ρ B hB ⊤ u v
  | some F =>
    by_cases hF : F ∈ idx3 Γ
    · rw [Qf_some_of_mem hF]
      simp only [LinearMap.sub_apply, map_sub]
      rw [bilin_av ρ B hB F u v, bilin_av ρ B hB ⊤ u v]
    · rw [Qf_some_of_not_mem hF]
      simp

theorem range_nondeg (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) (B : LinearMap.BilinForm K V)
    (hB : ∀ (g : Γ) (u w : V), B (ρ g u) (ρ g w) = B u w)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0) (F : Subgroup Γ) :
    ∀ w ∈ LinearMap.range (Qf ρ (some F)),
      (∀ w' ∈ LinearMap.range (Qf ρ (some F)), B w w' = 0) → w = 0 := by
  intro w hw hperp
  obtain ⟨x, rfl⟩ := hw
  apply hnd
  intro v
  rw [decomp (ρ := ρ) h3 hΓ hexp hcomm v, map_sum]
  apply Finset.sum_eq_zero
  intro o _
  by_cases ho : o = some F
  · subst ho
    apply hperp
    exact LinearMap.mem_range_self _ _
  · rw [Qf_bilin B hB (some F) x (Qf ρ o v)]
    have h0 : Qf ρ (some F) (Qf ρ o v) = 0 := by
      have := congrArg (fun f : Module.End K V => f v)
        (Qf_orth (ρ := ρ) h3 hΓ hexp hcomm (o₁ := some F) (o₂ := o) (fun h => ho h.symm))
      simpa [Module.End.mul_apply] using this
    rw [h0, map_zero]

theorem range_two_le (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) (B : LinearMap.BilinForm K V)
    (halt : ∀ v : V, B v v = 0)
    (hB : ∀ (g : Γ) (u w : V), B (ρ g u) (ρ g w) = B u w)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0) (F : Subgroup Γ)
    (hne : LinearMap.range (Qf ρ (some F)) ≠ ⊥) :
    2 ≤ Module.finrank K (LinearMap.range (Qf ρ (some F))) := by
  have hpos : 1 ≤ Module.finrank K (LinearMap.range (Qf ρ (some F))) :=
    Submodule.one_le_finrank_iff.2 hne
  by_contra hlt
  have h1 : Module.finrank K (LinearMap.range (Qf ρ (some F))) = 1 := by omega
  obtain ⟨w0, hw0mem, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw0 : (⟨w0, hw0mem⟩ : LinearMap.range (Qf ρ (some F))) ≠ 0 :=
    fun h => hw0ne (congrArg Subtype.val h)
  have key := (finrank_eq_one_iff_of_nonzero' _ hw0).1 h1
  apply hw0ne
  apply range_nondeg h3 hΓ hexp hcomm B hB hnd F w0 hw0mem
  intro w' hw'
  obtain ⟨c, hc⟩ := key ⟨w', hw'⟩
  have hw'eq : w' = c • w0 := (congrArg Subtype.val hc).symm
  rw [hw'eq, map_smul, halt w0, smul_zero]

theorem exists_common_nontrivial (hΓ : Nat.card Γ = 27) (S : Finset (Subgroup Γ))
    (hS : ∀ F ∈ S, F.index = 3) (hcard : S.card ≤ 2) :
    ∃ g : Γ, g ≠ 1 ∧ ∀ F ∈ S, g ∈ F := by
  have hnt : ∀ H : Subgroup Γ, 1 < Nat.card H → ∃ g ∈ H, g ≠ 1 := by
    intro H hH
    have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.1 hH
    obtain ⟨x, hx⟩ := exists_ne (1 : H)
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  haveI : Nontrivial Γ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hΓ]; norm_num)
  have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hc with h0 | h1 | h2
  · obtain ⟨g, hg⟩ := exists_ne (1 : Γ)
    exact ⟨g, hg, fun F hF => by rw [Finset.card_eq_zero.1 h0] at hF; simp at hF⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    have hcardA : Nat.card a = 9 := card_of_index_eq_three hΓ (hS a (by rw [ha]; simp))
    obtain ⟨g, hgA, hg1⟩ := hnt a (by rw [hcardA]; norm_num)
    refine ⟨g, hg1, fun F hF => ?_⟩
    rw [ha, Finset.mem_singleton] at hF
    rw [hF]
    exact hgA
  · obtain ⟨x, y, hxy, hSxy⟩ := Finset.card_eq_two.1 h2
    have hx : x ∈ S := by rw [hSxy]; simp
    have hy : y ∈ S := by rw [hSxy]; simp
    have hinf : Nat.card (x ⊓ y : Subgroup Γ) = 3 :=
      card_inf_eq_three hΓ (hS x hx) (hS y hy) hxy
    obtain ⟨g, hgI, hg1⟩ := hnt (x ⊓ y) (by rw [hinf]; norm_num)
    refine ⟨g, hg1, fun F hF => ?_⟩
    rw [hSxy, Finset.mem_insert, Finset.mem_singleton] at hF
    rcases hF with rfl | rfl
    · exact (Subgroup.mem_inf.1 hgI).1
    · exact (Subgroup.mem_inf.1 hgI).2

theorem core_exists (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) (hdim : Module.finrank K V = 6)
    (hfaith : ∀ g : Γ, (∀ v : V, ρ g v = v) → g = 1)
    (B : LinearMap.BilinForm K V) (halt : ∀ v : V, B v v = 0)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0)
    (hB : ∀ (g : Γ) (u w : V), B (ρ g u) (ρ g w) = B u w) :
    ∃ F ∈ idx3 Γ, Module.finrank K (LinearMap.range (av ρ F)) = 2 ∧
      (∀ v ∈ LinearMap.range (av ρ F), (∀ w ∈ LinearMap.range (av ρ F), B v w = 0) → v = 0) ∧
      av ρ ⊤ = 0 := by
  have hint : DirectSum.IsInternal (fun o => LinearMap.range (Qf ρ o)) :=
    isInternal_range_of_orthogonal_idempotents (Qf ρ) (fun o => Qf_idem h3 hΓ o)
      (fun o₁ o₂ hne => Qf_orth h3 hΓ hexp hcomm hne) (Qf_sum h3 hΓ hexp hcomm)
  have hfinrank : Module.finrank K V = ∑ o, Module.finrank K (LinearMap.range (Qf ρ o)) := by
    have h1 := finrank_biSup_of_iSupIndep hint.submodule_iSupIndep Finset.univ
    have htop : (⨆ i ∈ (Finset.univ : Finset (Option (Subgroup Γ))),
        LinearMap.range (Qf ρ i)) = ⊤ := by
      simp only [Finset.mem_univ, iSup_pos]
      exact hint.submodule_iSup_eq_top
    rw [htop, finrank_top] at h1
    exact h1
  set S : Finset (Subgroup Γ) :=
    (idx3 Γ).filter (fun F => LinearMap.range (Qf ρ (some F)) ≠ ⊥) with hS
  have hzero : ∀ F, F ∉ S → LinearMap.range (Qf ρ (some F)) = ⊥ := by
    intro F hF
    by_contra hr
    apply hF
    rw [hS, Finset.mem_filter]
    refine ⟨?_, hr⟩
    by_contra hmem
    exact hr (by rw [Qf_some_of_not_mem hmem, LinearMap.range_zero])
  have hsumS : ∑ F ∈ S, Module.finrank K (LinearMap.range (Qf ρ (some F))) =
      ∑ F : Subgroup Γ, Module.finrank K (LinearMap.range (Qf ρ (some F))) := by
    refine Finset.sum_subset (Finset.subset_univ S) (fun F _ hF => ?_)
    rw [hzero F hF, finrank_bot]
  have hsum6 : Module.finrank K (LinearMap.range (Qf ρ none)) +
      ∑ F ∈ S, Module.finrank K (LinearMap.range (Qf ρ (some F))) = 6 := by
    rw [hsumS, ← hdim, hfinrank, Fintype.sum_option]
  have hdimS : ∀ F ∈ S, 2 ≤ Module.finrank K (LinearMap.range (Qf ρ (some F))) := by
    intro F hF
    exact range_two_le h3 hΓ hexp hcomm B halt hB hnd F (Finset.mem_filter.1 hF).2
  have hA2 : S.card * 2 ≤ ∑ F ∈ S, Module.finrank K (LinearMap.range (Qf ρ (some F))) :=
    Finset.card_nsmul_le_sum S _ 2 hdimS
  have hS3 : 3 ≤ S.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg1, hgF⟩ := exists_common_nontrivial hΓ S
      (fun F hF => (mem_idx3 F).1 (Finset.mem_filter.1 hF).1) (by omega)
    apply hg1
    apply hfaith g
    intro v
    rw [decomp (ρ := ρ) h3 hΓ hexp hcomm v, map_sum]
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
  have hTzero : Module.finrank K (LinearMap.range (Qf ρ none)) = 0 := by
    have hAS : 6 ≤ ∑ F ∈ S, Module.finrank K (LinearMap.range (Qf ρ (some F))) := by
      have : 3 * 2 ≤ S.card * 2 := Nat.mul_le_mul_right 2 hS3
      omega
    omega
  have hT : av ρ ⊤ = 0 := LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 hTzero)
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨F, hF⟩ := hSne
  have hFd : Module.finrank K (LinearMap.range (Qf ρ (some F))) = 2 := by
    have hsplit := Finset.add_sum_erase S
      (fun F => Module.finrank K (LinearMap.range (Qf ρ (some F)))) hF
    have hrest : (S.erase F).card * 2 ≤
        ∑ G ∈ S.erase F, Module.finrank K (LinearMap.range (Qf ρ (some G))) :=
      Finset.card_nsmul_le_sum _ _ 2 (fun G hG => hdimS G (Finset.mem_of_mem_erase hG))
    rw [Finset.card_erase_of_mem hF] at hrest
    have h2 := hdimS F hF
    have hcard3 : S.card = 3 := by omega
    rw [hcard3] at hrest
    omega
  have hFmem : F ∈ idx3 Γ := (Finset.mem_filter.1 hF).1
  have hAF : av ρ F = Qf ρ (some F) := by
    rw [Qf_some_of_mem hFmem, hT, sub_zero]
  refine ⟨F, hFmem, ?_, ?_, hT⟩
  · rw [hAF]
    exact hFd
  · intro v hv hperp
    rw [hAF] at hv hperp
    exact range_nondeg h3 hΓ hexp hcomm B hB hnd F v hv hperp

end Core

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end
