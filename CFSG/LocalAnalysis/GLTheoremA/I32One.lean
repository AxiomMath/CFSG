module

public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement

private theorem eq_top_of_forall_odd_orderOf_mem {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) (Q : Subgroup X) (hQ : ∀ s : X, Odd (orderOf s) → s ∈ Q) :
    Q = ⊤ := by
  have hconj : ∀ (g : X), ∀ x ∈ Subgroup.closure {s : X | Odd (orderOf s)},
      g * x * g⁻¹ ∈ Subgroup.closure {s : X | Odd (orderOf s)} := by
    intro g x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      have h : orderOf x = orderOf (g * x * g⁻¹) :=
        SemiconjBy.orderOf_eq g (x := x) (y := g * x * g⁻¹) (by simp [SemiconjBy])
      change Odd (orderOf (g * x * g⁻¹))
      rw [← h]
      exact hx
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa [mul_assoc] using Subgroup.inv_mem _ hx
  have hKnormal : (Subgroup.closure {s : X | Odd (orderOf s)}).Normal :=
    ⟨fun n hn g => hconj g n hn⟩
  set K : Subgroup X := Subgroup.closure {s : X | Odd (orderOf s)}
  have hKQ : K ≤ Q := (Subgroup.closure_le Q).2 fun s hs => hQ s hs
  have h2 : IsPGroup 2 (X ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    have hxk : x ^ (2 ^ k) ∈ K := by
      refine Subgroup.subset_closure ?_
      change Odd (orderOf (x ^ (2 ^ k)))
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm]
      simpa [Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] using hm
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hxk
  have : Group.IsNilpotent (X ⧸ K) := h2.isNilpotent
  have hsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hperf : commutator (X ⧸ K) = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' K) (commutator X) = commutator (X ⧸ K) := by
      simp only [commutator_def]
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
    rw [← h1, hX, Subgroup.map_top_of_surjective _ hsurj]
  have : Subsingleton (X ⧸ K) := by
    by_contra h
    have : Nontrivial (X ⧸ K) := not_subsingleton_iff_nontrivial.1 h
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ K)).ne hperf
  have hKtop : K = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
  exact top_le_iff.1 (hKtop ▸ hKQ)

theorem commutator_commutator_eq_of_perfect {G : Type*} [Group G] [Finite G] {A H : Subgroup G}
    (hA : IsPGroup 2 A) (hH : ⁅H, H⁆ = H) (hHA : H ≤ Subgroup.normalizer (A : Set G)) :
    ⁅⁅A, H⁆, H⁆ = ⁅A, H⁆ := by
  refine le_antisymm
    (Subgroup.le_normalizer_iff_commutator_le_left.1 (Subgroup.normalizer_commutator_ge_right A H))
    ?_
  set N : Subgroup G := ⁅⁅A, H⁆, H⁆
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.normalizer_commutator_ge_right ⁅A, H⁆ H
  have hperf : commutator H = ⊤ := by
    rw [← Subgroup.map_subtype_inj, Subgroup.map_subtype_commutator, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hH
  let Q : Subgroup H :=
    { carrier := {g | ∀ a ∈ A, ⁅a, (g : G)⁆ ∈ N}
      one_mem' := fun a _ => by simp [N.one_mem]
      mul_mem' := by
        intro g h hg hh a ha
        have e : ⁅a, ((g * h : H) : G)⁆ = ⁅a, (g : G)⁆ * ((g : G) * ⁅a, (h : G)⁆ * (g : G)⁻¹) := by
          simp only [Subgroup.coe_mul, commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hg a ha) ((Subgroup.mem_normalizer_iff.1 (hHN g.2) _).1 (hh a ha))
      inv_mem' := by
        intro g hg a ha
        have e : ⁅a, ((g⁻¹ : H) : G)⁆ = (g : G)⁻¹ * ⁅a, (g : G)⁆⁻¹ * (g : G) := by
          simp only [Subgroup.coe_inv, commutatorElement_def]; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (hHN (g⁻¹ : H).2) _).1 (N.inv_mem (hg a ha))
        simpa using this }
  have hodd : ∀ s : H, Odd (orderOf s) → s ∈ Q := by
    intro s hs a ha
    have hzH : Subgroup.zpowers (s : G) ≤ H := by
      rw [Subgroup.zpowers_le]; exact s.2
    have hord : orderOf (s : G) = orderOf s := Subgroup.orderOf_coe s
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers (s : G))) (Nat.card A) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
      rw [Nat.card_zpowers, hk, hord]
      exact Nat.Coprime.pow_right k hs.coprime_two_right
    have hsolv : Group.IsSolvable A := by
      have := hA.isNilpotent
      infer_instance
    have key := GL83.commutator_double_eq_self (Subgroup.zpowers (s : G)) A (hzH.trans hHA) hcop
      hsolv
    have hmem : ⁅a, (s : G)⁆ ∈ ⁅A, Subgroup.zpowers (s : G)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers _)
    rw [← key] at hmem
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hzH) hzH hmem
  have hQtop : Q = ⊤ := eq_top_of_forall_odd_orderOf_mem hperf Q hodd
  refine Subgroup.commutator_le.2 fun a ha h hh => ?_
  have hmem : (⟨h, hh⟩ : H) ∈ Q := hQtop ▸ Subgroup.mem_top _
  exact hmem a ha

end CFSG.LocalAnalysis.GLTheoremA
