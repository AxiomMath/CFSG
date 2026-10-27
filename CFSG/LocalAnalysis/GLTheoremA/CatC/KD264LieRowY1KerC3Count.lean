module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open Subgroup

noncomputable section

open Classical

@[expose] def idx3 (Γ : Type) [Group Γ] [Fintype Γ] : Finset (Subgroup Γ) :=
  Finset.univ.filter (fun F : Subgroup Γ => F.index = 3)

@[expose] def subEl {Γ : Type} [Group Γ] [Fintype Γ] (F : Subgroup Γ) : Finset Γ :=
  Finset.univ.filter (fun g : Γ => g ∈ F)

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem mem_idx3 (F : Subgroup Γ) : F ∈ idx3 Γ ↔ F.index = 3 := by
  unfold idx3
  simp

theorem mem_subEl (F : Subgroup Γ) (g : Γ) : g ∈ subEl F ↔ g ∈ F := by
  unfold subEl
  simp

theorem subEl_card (F : Subgroup Γ) : (subEl F).card = Nat.card F := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  unfold subEl
  simp [Fintype.card_subtype]

theorem card_of_index_eq_three (hΓ : Nat.card Γ = 27) {F : Subgroup Γ} (h : F.index = 3) :
    Nat.card F = 9 := by
  have h1 := F.card_mul_index
  rw [h, hΓ] at h1
  omega

theorem card_inf_eq_three (hΓ : Nat.card Γ = 27) {F F' : Subgroup Γ} (hF : F.index = 3)
    (hF' : F'.index = 3) (hne : F ≠ F') : Nat.card (F ⊓ F' : Subgroup Γ) = 3 := by
  have hc : Nat.card F = 9 := card_of_index_eq_three hΓ hF
  have hc' : Nat.card F' = 9 := card_of_index_eq_three hΓ hF'
  have hidx : (F ⊓ F').index ≤ 9 := by
    have := Subgroup.index_inf_le (H := F) (K := F')
    rw [hF, hF'] at this
    omega
  have hmul : Nat.card (F ⊓ F' : Subgroup Γ) * (F ⊓ F').index = 27 := by
    rw [← hΓ]
    exact (F ⊓ F').card_mul_index
  have hdvd : Nat.card (F ⊓ F' : Subgroup Γ) ∣ 9 := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hlt : Nat.card (F ⊓ F' : Subgroup Γ) ≠ 9 := by
    intro h9
    apply hne
    have h1 : F ⊓ F' = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hc])
    have hle : F ≤ F' := by
      rw [← h1]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc'])
  generalize hn : Nat.card (F ⊓ F' : Subgroup Γ) = n at hmul hdvd hlt ⊢
  have hn9 : n ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> omega

theorem sum_idx3_subEl {M : Type} [AddCommMonoid M] (f : Γ → M) :
    ∑ F ∈ idx3 Γ, ∑ g ∈ subEl F, f g =
      ∑ g : Γ, ((idx3 Γ).filter (fun F => g ∈ F)).card • f g := by
  have h1 : ∀ F ∈ idx3 Γ, ∑ g ∈ subEl F, f g = ∑ g : Γ, if g ∈ F then f g else 0 := by
    intro F _
    unfold subEl
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const]

theorem card_filter_contains (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) {e : Γ} (he : e ≠ 1) :
    ((idx3 Γ).filter (fun F => e ∈ F)).card = 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsMulCommutative Γ := ⟨⟨hcomm⟩⟩
  set N : Subgroup Γ := Subgroup.zpowers e with hN
  haveI : N.Normal := Subgroup.normal_of_comm N
  have hord : orderOf e = 3 := orderOf_eq_prime (hexp e) he
  have hNcard : Nat.card N = 3 := by rw [hN, Nat.card_zpowers, hord]
  have hQcard : Nat.card (Γ ⧸ N) = 9 := by
    have h1 := N.card_mul_index
    rw [hNcard, hΓ] at h1
    have h2 : N.index = Nat.card (Γ ⧸ N) := rfl
    omega
  have hQexp : ∀ q : Γ ⧸ N, q ^ 3 = 1 := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hexp g]
    rfl
  have hcount := CFSG.RankThree.Classical.card_subgroups_natCard_eq_prime (p := 3)
    Nat.prime_three hQexp (by rw [hQcard]; norm_num)
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hNle : ∀ F : Subgroup Γ, e ∈ F → N ≤ F := fun F hF => Subgroup.zpowers_le.2 hF
  rw [show (4 : ℕ) = 3 + 1 by norm_num, ← hcount]
  apply Finset.card_nbij' (fun F : Subgroup Γ => F.map (QuotientGroup.mk' N))
    (fun M : Subgroup (Γ ⧸ N) => M.comap (QuotientGroup.mk' N))
  · intro F hF
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hF
    obtain ⟨hF1, hF2⟩ := hF
    rw [mem_idx3] at hF1
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hidx : (F.map (QuotientGroup.mk' N)).index = 3 := by
      rw [Subgroup.index_map_eq F hsurj (by rw [QuotientGroup.ker_mk']; exact hNle F hF2), hF1]
    have h1 := (F.map (QuotientGroup.mk' N)).card_mul_index
    rw [hQcard, hidx] at h1
    omega
  · intro M hM
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hM
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, mem_idx3, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hMidx : M.index = 3 := by
      have h1 := M.card_mul_index
      rw [hQcard, hM] at h1
      omega
    refine ⟨?_, ?_⟩
    · rw [Subgroup.index_comap_of_surjective M hsurj, hMidx]
    · have he1 : ((e : Γ) : Γ ⧸ N) = 1 := (QuotientGroup.eq_one_iff e).2 (Subgroup.mem_zpowers e)
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, he1]
      exact M.one_mem
  · intro F hF
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hF
    simp only
    rw [QuotientGroup.comap_map_mk', sup_eq_right.2 (hNle F hF.2)]
  · intro M _
    simp only
    exact Subgroup.map_comap_eq_self_of_surjective hsurj M

theorem card_idx3 (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) : (idx3 Γ).card = 13 := by
  have hcardU : (Finset.univ : Finset Γ).card = 27 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hΓ]
  have key := sum_idx3_subEl (M := ℕ) (fun g : Γ => if g ≠ 1 then 1 else 0)
  have hL : ∑ F ∈ idx3 Γ, ∑ g ∈ subEl F, (if g ≠ 1 then 1 else 0) = ∑ F ∈ idx3 Γ, 8 := by
    refine Finset.sum_congr rfl (fun F hF => ?_)
    rw [Finset.sum_boole]
    have h1 : (subEl F).filter (fun g => g ≠ 1) = (subEl F).erase 1 := by
      rw [Finset.filter_ne']
    have h2 : (1 : Γ) ∈ subEl F := (mem_subEl F 1).2 F.one_mem
    have h9 : Nat.card F = 9 := card_of_index_eq_three hΓ ((mem_idx3 F).1 hF)
    rw [h1, Finset.card_erase_of_mem h2, subEl_card, h9]
    norm_num
  have hR : ∑ g : Γ, ((idx3 Γ).filter (fun F => g ∈ F)).card • (if g ≠ 1 then 1 else 0)
      = ∑ g : Γ, (if g ≠ 1 then 4 else 0) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hg : g = 1
    · subst hg
      simp
    · rw [if_pos hg, if_pos hg, smul_eq_mul, mul_one]
      exact card_filter_contains hΓ hexp hcomm hg
  have hsum104 : ∑ g : Γ, (if g ≠ 1 then 4 else 0) = 104 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), hcardU, smul_eq_mul]
  have hfin : (idx3 Γ).card • 8 = 104 := by
    rw [← Finset.sum_const, ← hL, key, hR, hsum104]
  rw [smul_eq_mul] at hfin
  omega

theorem sum_idx3_sub {M : Type} [AddCommMonoid M] (hΓ : Nat.card Γ = 27)
    (hexp : ∀ g : Γ, g ^ 3 = 1) (hcomm : ∀ g h : Γ, g * h = h * g) (f : Γ → M) :
    ∑ F ∈ idx3 Γ, ∑ g ∈ subEl F, f g = 9 • f 1 + 4 • ∑ g, f g := by
  rw [sum_idx3_subEl f]
  have h1 : ((idx3 Γ).filter (fun F => (1 : Γ) ∈ F)) = idx3 Γ := by
    refine Finset.filter_true_of_mem (fun F _ => F.one_mem)
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun g : Γ => ((idx3 Γ).filter (fun F => g ∈ F)).card • f g) (Finset.mem_univ (1 : Γ))
  have hsplit2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ (1 : Γ))
  have hrest : ∑ g ∈ Finset.univ.erase (1 : Γ),
      ((idx3 Γ).filter (fun F => g ∈ F)).card • f g = 4 • ∑ g ∈ Finset.univ.erase (1 : Γ), f g := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    have hg1 : g ≠ 1 := Finset.ne_of_mem_erase hg
    rw [card_filter_contains hΓ hexp hcomm hg1]
  rw [← hsplit, hrest, h1, card_idx3 hΓ hexp hcomm, ← hsplit2]
  rw [smul_add]
  module

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end
