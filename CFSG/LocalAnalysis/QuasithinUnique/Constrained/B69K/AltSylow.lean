module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.B69K

lemma bkSyl_injective_pair {m : ℕ} {p q : Fin m} (h : p ≠ q) :
    Function.Injective ![p, q] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

lemma bkSyl_two_group_eq {m : ℕ} {V₀ Q : Subgroup (Equiv.Perm (Fin m))}
    (hidx : ¬ 2 ∣ V₀.relIndex (alternatingGroup (Fin m)))
    (hVQ : V₀ ≤ Q) (hQA : Q ≤ alternatingGroup (Fin m)) (hQ : IsPGroup 2 Q) : Q ≤ V₀ := by
  have hmul : V₀.relIndex Q * Q.relIndex (alternatingGroup (Fin m)) =
      V₀.relIndex (alternatingGroup (Fin m)) :=
    Subgroup.relIndex_mul_relIndex (H := V₀) (K := Q) (L := alternatingGroup (Fin m)) hVQ hQA
  have hodd : ¬ 2 ∣ V₀.relIndex Q := fun h => hidx (h.trans (Dvd.intro _ hmul))
  have hcard : V₀.relIndex Q ∣ Nat.card Q :=
    Subgroup.relIndex_dvd_card (H := V₀) (K := Q)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  rw [hn] at hcard
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcard
  have hi0 : i = 0 := by
    by_contra h
    exact hodd (by rw [hi]; exact dvd_pow_self 2 h)
  rw [hi0, pow_zero] at hi
  exact (Subgroup.relIndex_eq_one (H := V₀) (K := Q)).1 hi

section Sylow

theorem sylow_alt_unique_fixed {m : ℕ} (hodd : Odd m) (hm : 5 ≤ m)
    {V₀ : Subgroup (Equiv.Perm (Fin m))} (hV₀A : V₀ ≤ alternatingGroup (Fin m))
    (hV₀ : IsPGroup 2 V₀) (hidx : ¬ 2 ∣ (V₀.subgroupOf (alternatingGroup (Fin m))).index) :
    ∃ p : Fin m, (∀ g ∈ V₀, g p = p) ∧ ∀ q : Fin m, (∀ g ∈ V₀, g q = q) → q = p := by
  have hodd' : ¬ 2 ∣ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨p, hp⟩ := hV₀.nonempty_fixed_point_of_prime_not_dvd_card (Fin m) hodd'
  have hpfix : ∀ g ∈ V₀, g p = p := fun g hg => MulAction.mem_fixedPoints.1 hp ⟨g, hg⟩
  refine ⟨p, hpfix, fun q hq => ?_⟩
  by_contra hqp
  have hpq : p ≠ q := fun h => hqp h.symm
  have hidx' : ¬ 2 ∣ V₀.relIndex (alternatingGroup (Fin m)) := hidx
  haveI := alternatingGroup.isMultiplyPretransitive (Fin m)
  have hpt : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin m)) (Fin m) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin m) - 2)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) (by omega)
  let f₀ : Fin 2 ↪ Fin m := ⟨![p, q], bkSyl_injective_pair hpq⟩
  have hK : V₀.subgroupOf (alternatingGroup (Fin m)) ≤
      MulAction.stabilizer (alternatingGroup (Fin m)) f₀ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    intro i
    fin_cases i
    · exact hpfix _ hx
    · exact hq _ hx
  have hSidx : (MulAction.stabilizer (alternatingGroup (Fin m)) f₀).index =
      Nat.card (Fin 2 ↪ Fin m) :=
    @MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin m)) (Fin 2 ↪ Fin m) _ _ f₀
      hpt
  have hcardE : Nat.card (Fin 2 ↪ Fin m) = m * (m - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
      show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one,
      Nat.mul_comm (m - 1) m]
  have hev : 2 ∣ (MulAction.stabilizer (alternatingGroup (Fin m)) f₀).index := by
    rw [hSidx, hcardE]
    exact (Nat.even_mul_pred_self m).two_dvd
  apply hidx
  rw [← Subgroup.relIndex_mul_index hK]
  exact Dvd.dvd.mul_left hev _

theorem exists_odd_normalizing {m : ℕ} (hodd : Odd m) (hm : 5 ≤ m)
    {V₀ : Subgroup (Equiv.Perm (Fin m))} (hV₀A : V₀ ≤ alternatingGroup (Fin m))
    (hV₀ : IsPGroup 2 V₀) (hidx : ¬ 2 ∣ (V₀.subgroupOf (alternatingGroup (Fin m))).index) :
    ∃ s : Equiv.Perm (Fin m), s ∉ alternatingGroup (Fin m) ∧ ∀ v ∈ V₀, s * v * s⁻¹ ∈ V₀ := by
  have hidx' : ¬ 2 ∣ V₀.relIndex (alternatingGroup (Fin m)) := hidx
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hAidx : (alternatingGroup (Fin m)).index = 2 :=
    alternatingGroup.index_eq_two (α := Fin m)
  have hnorm : (alternatingGroup (Fin m)).Normal := inferInstance
  obtain ⟨P, hVP⟩ := hV₀.exists_le_sylow
  obtain ⟨s, hsP, hsA⟩ :
      ∃ s ∈ (P : Subgroup (Equiv.Perm (Fin m))), s ∉ alternatingGroup (Fin m) := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hPV : (P : Subgroup (Equiv.Perm (Fin m))) ≤ V₀ :=
      bkSyl_two_group_eq hidx' hVP (fun x hx => hcon x hx) P.isPGroup'
    have heq : (P : Subgroup (Equiv.Perm (Fin m))) = V₀ := le_antisymm hPV hVP
    have h2 : 2 ∣ V₀.index := by
      rw [← Subgroup.relIndex_mul_index hV₀A, hAidx]
      exact dvd_mul_left 2 _
    have h2' : 2 ∣ (P : Subgroup (Equiv.Perm (Fin m))).index := by
      rw [heq]
      exact h2
    exact P.not_dvd_index h2'
  refine ⟨s, hsA, fun v hv => ?_⟩
  have hR : (P : Subgroup (Equiv.Perm (Fin m))) ⊓ alternatingGroup (Fin m) ≤ V₀ :=
    bkSyl_two_group_eq hidx' (le_inf hVP hV₀A) inf_le_right
      (P.isPGroup'.to_le inf_le_left)
  have hmem : s * v * s⁻¹ ∈ (P : Subgroup (Equiv.Perm (Fin m))) ⊓ alternatingGroup (Fin m) :=
    Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hsP (hVP hv)) (inv_mem hsP),
      hnorm.conj_mem v (hV₀A hv) s⟩
  exact hR hmem

end Sylow

end CFSG.Quasithin.B69K
