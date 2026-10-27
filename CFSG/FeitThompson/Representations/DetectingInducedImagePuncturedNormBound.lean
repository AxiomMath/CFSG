module

public import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
import CFSG.FeitThompson.Representations.OneBlockRestrictionPuncturedNorm
import CFSG.FeitThompson.Representations.CommutingCyclicAverageCharacterCongruence
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open OneBlockRestriction

open scoped Classical in
theorem card_sub_index_sq_le_sum_erase_norm_sq
    {G : Type*} [Group G] [Fintype G] {S : Subgroup G} [Fintype ↥S]
    {H P : Subgroup ↥S} [Fintype ↥H] [H.Normal] [P.Normal] [IsMulCommutative ↥H]
    (hPH : P ≤ H)
    (ν : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)) →+ Submodule.span ℤ (Irr G))
    (hν : ∀ f : charSpanZero (indFamDetect H (P.subgroupOf H)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun S (f : ↥S → ℂ))
    (hiso : ∀ f g : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)),
      cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥S → ℂ) (g : ↥S → ℂ))
    (hcard : 2 ≤ (indFamDetect H (P.subgroupOf H)).ncard)
    {lam : ↥S → ℂ} (hlamT : lam ∈ indFamDetect H (P.subgroupOf H)) (hlamIrr : lam ∈ Irr ↥S)
    {chi : G → ℂ} (hchi : chi = (ν ⟨lam, Submodule.subset_span hlamT⟩ : G → ℂ))
    {u q : ℕ} (hu : 0 < u) (hq : q.Prime) (hd : H.index = u * q)
    (hPu : 2 * (u : ℤ) ≤ (Nat.card ↥P : ℤ) - 1)
    {x y : ↥S} (hxP : x ∈ P) (hx1 : x ≠ 1) (hyq : orderOf y = q) (hxy : Commute x y)
    (hval : ∀ j : ℕ, 1 ≤ j → j ≤ q - 1 → chi ((y ^ j * x : ↥S) : G) = lam (y ^ j * x)) :
    (Nat.card ↥S : ℝ) - (H.index : ℝ) ^ 2
      ≤ ∑ z ∈ Finset.univ.erase (1 : ↥H), ‖chi ((z : ↥S) : G)‖ ^ 2 := by
  classical
  have hchimem : chi ∈ Submodule.span ℤ (Irr G) := hchi ▸ (ν _).2
  have hlamnorm : cfInner lam lam = 1 := cfInner_self_of_mem_Irr hlamIrr
  have horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H), ξ ≠ lam →
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) chi = 0 := by
    intro ξ hξ hne
    rw [hchi, hiso]
    exact NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H
      (mem_indFam_Irr_of_mem_indFamDetect hξ) (mem_indFam_Irr_of_mem_indFamDetect hlamT) hne
  obtain ⟨a, n, b, hnpos, ha, hn, hlam1, hbsupp, hsplit⟩ :=
    exists_intCast_eq_on_sdiff_one_of_cfInner_eq_zero hPH ν hν hcard hlamT hchimem horth
  have hn1 : n = 1 := by
    have h : (n : ℂ) = 1 := by rw [← hn, hlamnorm]
    exact_mod_cast h
  have ha1 : a = 1 := by
    have h : (a : ℂ) = 1 := by rw [← ha, hchi, hiso, hlamnorm]
    exact_mod_cast h
  subst hn1 ha1
  obtain ⟨θ, hθ, hθP, hθind⟩ := exists_mem_Irr_of_mem_indFamDetect hlamT
  set α : ↥H → ℂ := ∑ ψ ∈ irrFinset ↥H, (b ψ : ℂ) • ψ with hαdef
  have hαapply : ∀ z : ↥H, α z = ∑ ψ ∈ irrFinset ↥H, (b ψ : ℂ) * ψ z := by
    intro z
    rw [hαdef, Finset.sum_apply]
    simp
  have hα : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H)) := by
    rw [hαdef]
    refine Submodule.sum_mem _ fun ψ hψ => ?_
    by_cases hdet : ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel ψ
    · rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_irrTrivialOn.2
        ⟨mem_irrFinset.1 hψ, fun z hz => mem_charValueKernel.1 (hdet hz)⟩))
    · rw [hbsupp ψ hdet]
      simp
  obtain ⟨m, hm⟩ := exists_int_apply_one_of_mem_span_irrTrivialOn hα
  have hsplit' : ∀ z : ↥H, z ≠ 1 → chi ((z : ↥S) : G) = indClassFun H θ (z : ↥S) + α z := by
    intro z hz
    rw [hsplit z hz, hαapply z, hθind]
    push_cast
    ring
  set xH : ↥H := ⟨x, hPH hxP⟩ with hxHdef
  have hxHne : xH ≠ 1 := fun h => hx1 (congrArg (fun w : ↥H => (w : ↥S)) h)
  have hαx : α xH = (m : ℂ) := by
    rw [apply_eq_apply_one_of_mem_span_irrTrivialOn hα
      (Subgroup.mem_subgroupOf.2 (show (xH : ↥S) ∈ P from hxP)), hm]
  set Ψ : ↥S → ℂ := resClassFun S chi - lam with hΨdef
  have hΨmem : Ψ ∈ Submodule.span ℤ (Irr ↥S) := by
    refine sub_mem ?_ (Submodule.subset_span hlamIrr)
    have h := comp_mem_span_Irr (X := ↥S) S.subtype hchimem
    have he : chi ∘ (S.subtype : ↥S →* G) = resClassFun S chi := by funext z; simp
    rwa [he] at h
  have hΨx : Ψ x = (m : ℂ) := by
    have h : chi ((x : ↥S) : G) = lam x + (m : ℂ) := by
      rw [← hαx, ← hθind]; exact hsplit' xH hxHne
    rw [hΨdef]
    simp only [Pi.sub_apply, resClassFun_apply, h]
    ring
  have hqm : (q : ℤ) ∣ m := by
    have h := prime_dvd_sub_of_forall_apply_eq (G := ↥S) hq (x := y) (g := x) hyq hxy.symm
      hΨmem (Θ := (0 : Subgroup.zpowers y → ℂ)) (Submodule.zero_mem _) (c := m) (e := 0)
      hΨx (by simp)
      (fun j hj1 hj2 => by
        rw [hΨdef]
        simp only [Pi.sub_apply, resClassFun_apply, Pi.zero_apply]
        rw [hval j hj1 hj2, sub_self])
    simpa using h
  obtain ⟨bq, hbq⟩ := hqm
  have hnn : cfInner (indClassFun H θ) (indClassFun H θ) = ((1 : ℕ) : ℂ) := by
    rw [hθind, hlamnorm]; norm_num
  have key := sum_erase_norm_sq_eq (P := P) hθ hθP hnn 1 hα
    (f := fun z : ↥H => chi ((z : ↥S) : G))
    (fun z hz => by rw [hsplit' z hz]; push_cast; ring)
  rw [hm] at key
  have keyC : (∑ z ∈ Finset.univ.erase (1 : ↥H), (‖chi ((z : ↥S) : G)‖ : ℂ) ^ 2)
      = ((Nat.card ↥S : ℂ) - (H.index : ℂ) ^ 2 - 2 * (H.index : ℂ) * (m : ℂ))
        + ∑ z ∈ Finset.univ.erase (1 : ↥H), (‖α z‖ : ℂ) ^ 2 := by
    convert key using 2
    · congr!
    · norm_num
    · congr!
  have keyR : (∑ z ∈ Finset.univ.erase (1 : ↥H), ‖chi ((z : ↥S) : G)‖ ^ 2)
      = ((Nat.card ↥S : ℝ) - (H.index : ℝ) ^ 2 - 2 * (H.index : ℝ) * (m : ℝ))
        + ∑ z ∈ Finset.univ.erase (1 : ↥H), ‖α z‖ ^ 2 := by
    exact_mod_cast keyC
  have hnormα1 : ‖α 1‖ ^ 2 = (m : ℝ) ^ 2 := by
    rw [hm, Complex.norm_intCast, sq_abs]
  have hlb : ((Nat.card ↥P : ℝ) - 1) * (m : ℝ) ^ 2
      ≤ ∑ z ∈ Finset.univ.erase (1 : ↥H), ‖α z‖ ^ 2 := by
    rw [← hnormα1]
    convert card_sub_one_mul_norm_sq_le_sum_erase_norm_sq (P := P) hPH hα using 2
    congr!
  have hb2 : (bq : ℝ) ≤ (bq : ℝ) ^ 2 := by
    have h : ((bq : ℝ)) ≤ ((bq ^ 2 : ℤ) : ℝ) := by exact_mod_cast Int.le_self_sq bq
    simpa using h
  have hu0 : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hPu' : 2 * (u : ℝ) ≤ (Nat.card ↥P : ℝ) - 1 := by exact_mod_cast hPu
  have hmR : (m : ℝ) = (q : ℝ) * (bq : ℝ) := by rw [hbq]; push_cast; ring
  have hdR : (H.index : ℝ) = (u : ℝ) * (q : ℝ) := by rw [hd]; push_cast; ring
  have h3 : (0 : ℝ) ≤ ((Nat.card ↥P : ℝ) - 1) * (bq : ℝ) ^ 2 - 2 * (u : ℝ) * (bq : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hPu') (sq_nonneg ((bq : ℝ))),
      mul_nonneg hu0.le (sub_nonneg.2 hb2)]
  have hmain : (0 : ℝ) ≤ -(2 * (H.index : ℝ) * (m : ℝ))
      + ((Nat.card ↥P : ℝ) - 1) * (m : ℝ) ^ 2 := by
    have heq : -(2 * (H.index : ℝ) * (m : ℝ)) + ((Nat.card ↥P : ℝ) - 1) * (m : ℝ) ^ 2
        = (q : ℝ) ^ 2 *
          (((Nat.card ↥P : ℝ) - 1) * (bq : ℝ) ^ 2 - 2 * (u : ℝ) * (bq : ℝ)) := by
      rw [hmR, hdR]; ring
    rw [heq]
    exact mul_nonneg (sq_nonneg _) h3
  linarith

end CFSG.FeitThompson
