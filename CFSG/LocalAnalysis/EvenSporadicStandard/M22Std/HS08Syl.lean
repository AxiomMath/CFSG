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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type*} [Group G]

structure SqData (t : G) (T : Subgroup G) (z z' : G) : Prop where
  t_mem : t ∈ T
  z_mem : z ∈ T
  z'_mem : z' ∈ T
  ne : z ≠ z'
  mul : z * z' = t
  z_ne : z ≠ 1
  z'_ne : z' ≠ 1
  z_central : ∀ x ∈ T, z * x = x * z
  z'_central : ∀ x ∈ T, z' * x = x * z'
  z_sq : ∃ x ∈ T, x * x = z
  z'_sq : ∃ x ∈ T, x * x = z'
  uniq : ∀ u ∈ T, (∀ x ∈ T, u * x = x * u) → u ≠ 1 → (∃ x ∈ T, x * x = u) → u = z ∨ u = z'

namespace SqData

variable {t z z' : G} {T : Subgroup G} (h : SqData t T z z')
include h

theorem image_central_square {n : G} (hn : ∀ x, x ∈ T ↔ n * x * n⁻¹ ∈ T) {u : G} (huT : u ∈ T)
    (huc : ∀ x ∈ T, u * x = x * u) (hu1 : u ≠ 1) (hsq : ∃ x ∈ T, x * x = u) :
    n * u * n⁻¹ = z ∨ n * u * n⁻¹ = z' := by
  apply h.uniq (n * u * n⁻¹) ((hn u).1 huT)
  · intro w hw
    have hw' : n⁻¹ * w * n ∈ T := by
      refine (hn (n⁻¹ * w * n)).2 ?_
      simpa [mul_assoc] using hw
    have := huc _ hw'
    calc n * u * n⁻¹ * w = n * (u * (n⁻¹ * w * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * w * n) * u) * n⁻¹ := by rw [this]
      _ = w * (n * u * n⁻¹) := by group
  · intro h1
    apply hu1
    calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · obtain ⟨x, hxT, hx⟩ := hsq
    refine ⟨n * x * n⁻¹, (hn x).1 hxT, ?_⟩
    rw [← hx]
    group

theorem conj_fix {n : G} (hn : ∀ x, x ∈ T ↔ n * x * n⁻¹ ∈ T) : n * t * n⁻¹ = t := by
  have h1 := h.image_central_square hn h.z_mem h.z_central h.z_ne h.z_sq
  have h2 := h.image_central_square hn h.z'_mem h.z'_central h.z'_ne h.z'_sq
  have hne : n * z * n⁻¹ ≠ n * z' * n⁻¹ := fun h' => h.ne (mul_left_cancel (mul_right_cancel h'))
  have hprod : n * t * n⁻¹ = (n * z * n⁻¹) * (n * z' * n⁻¹) := by rw [← h.mul]; group
  rw [hprod]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2, h.mul]
  · rw [h1, h2, h.z'_central z h.z_mem, h.mul]
  · exact absurd (h1.trans h2.symm) hne

end SqData

section Sylow

variable [Finite G]

theorem exists_conj_two_sylow {C P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ C ∧ IsPGroup 2 P₁ ∧ ¬ 2 ∣ P₁.relIndex C)
    (h₂ : P₂ ≤ C ∧ IsPGroup 2 P₂ ∧ ¬ 2 ∣ P₂.relIndex C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup 2 (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup 2 (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow 2 ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow 2 ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : G)⁻¹ * x * g ∈ P₁ :=
      Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

namespace SqData

variable {t z z' : G} {T : Subgroup G} (h : SqData t T z z')
include h

theorem eq_of_le (hTH : T ≤ centralizer ({t} : Set G))
    (hTmax : ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) → IsPGroup 2 P → T ≤ P → P = T)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S) : S = T := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h' => hne ?_
    refine le_antisymm (fun x hx => ?_) hTS
    have : (⟨x, hx⟩ : S) ∈ T.subgroupOf S := by rw [h']; exact Subgroup.mem_top _
    exact this
  have hcond := Group.normalizerCondition_of_isNilpotent (G := S) (T.subgroupOf S) hlt
  obtain ⟨s, hsN, hsT⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hcond).2
  have hsT' : (s : G) ∉ T := hsT
  have hnorm : ∀ x, x ∈ T ↔ (s : G) * x * (s : G)⁻¹ ∈ T := by
    intro x
    by_cases hx : x ∈ S
    · have := (Subgroup.mem_normalizer_iff.1 hsN) ⟨x, hx⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have hxT : x ∉ T := fun h' => hx (hTS h')
      have hx' : (s : G) * x * (s : G)⁻¹ ∉ T := fun h' => hx (by
        have := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hTS h')) s.2
        simpa [mul_assoc] using this)
      exact ⟨fun h' => absurd h' hxT, fun h' => absurd h' hx'⟩
  have hfix := h.conj_fix hnorm
  have hsH : (s : G) ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (s : G) * t = ((s : G) * t * (s : G)⁻¹) * s := by group
      _ = t * s := by rw [hfix]
  have hP : T ⊔ zpowers (s : G) = T := by
    refine hTmax _ (sup_le hTH (by rw [zpowers_le]; exact hsH)) ?_ le_sup_left
    refine hS.to_le (sup_le hTS ?_)
    rw [zpowers_le]
    exact s.2
  exact hsT' (hP ▸ (le_sup_right : zpowers (s : G) ≤ T ⊔ zpowers (s : G)) (mem_zpowers _))

omit h in
theorem exists_normalizing_conj (P : Sylow 2 G) {x y g : G}
    (hxc : ∀ w ∈ (P : Subgroup G), x * w = w * x)
    (hyc : ∀ w ∈ (P : Subgroup G), y * w = w * y) (hg : g * x * g⁻¹ = y) :
    ∃ n : G, (∀ w, w ∈ (P : Subgroup G) ↔ n * w * n⁻¹ ∈ (P : Subgroup G)) ∧ n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({y} : Set G) with hC
  have hPC : (P : Subgroup G) ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (hyc w hw).symm
  have hP'C : ((g • P : Sylow 2 G) : Subgroup G) ≤ C := by
    intro w hw
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
    have hw' : g⁻¹ * w * g ∈ (P : Subgroup G) := by simpa [MulAut.smul_def, mul_assoc] using hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hxc _ hw'
    calc w * y = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by rw [← hg]; group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
      _ = y * w := by rw [← hg]; group
  have hodd : ∀ Q : Sylow 2 G, (Q : Subgroup G) ≤ C → ¬ 2 ∣ (Q : Subgroup G).relIndex C := by
    intro Q hQ hd
    have h1 := Subgroup.relIndex_mul_index hQ
    exact Q.not_dvd_index (by rw [← h1]; exact Dvd.dvd.mul_right hd _)
  obtain ⟨c, hcC, hc⟩ := exists_conj_two_sylow (C := C) (P₁ := (P : Subgroup G))
    (P₂ := ((g • P : Sylow 2 G) : Subgroup G)) ⟨hPC, P.isPGroup', hodd P hPC⟩
    ⟨hP'C, (g • P).isPGroup', hodd (g • P) hP'C⟩
  have hmem : ∀ w, w ∈ ((g • P : Sylow 2 G) : Subgroup G) ↔ g⁻¹ * w * g ∈ (P : Subgroup G) := by
    intro w
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  refine ⟨c⁻¹ * g, fun w => ?_, ?_⟩
  · have hw1 : w ∈ (P : Subgroup G) ↔ g * w * g⁻¹ ∈ ((g • P : Sylow 2 G) : Subgroup G) := by
      rw [hmem]
      simp [mul_assoc]
    rw [show c⁻¹ * g * w * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * w * g⁻¹) * c by group]
    exact hw1.trans (hc _)
  · have hcy : c * y = y * c := (Subgroup.mem_centralizer_singleton_iff.1 hcC)
    calc c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
      _ = y := by rw [hg]; calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
                                  _ = c⁻¹ * (c * y) := by rw [hcy]
                                  _ = y := by group

omit [Finite G] in
theorem t_central : ∀ x ∈ T, t * x = x * t := by
  intro x hx
  rw [← h.mul, mul_assoc, h.z'_central x hx, ← mul_assoc, h.z_central x hx, mul_assoc]

theorem exists_sylow (hTp : IsPGroup 2 T) (hTH : T ≤ centralizer ({t} : Set G))
    (hTmax : ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) → IsPGroup 2 P → T ≤ P → P = T) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hTp.exists_le_sylow
  exact ⟨P, h.eq_of_le hTH hTmax P.isPGroup' hP⟩

theorem eq_of_conj (P : Sylow 2 G) (hP : (P : Subgroup G) = T) {g : G}
    (hg : ∀ w ∈ T, (g * t * g⁻¹) * w = w * (g * t * g⁻¹)) : g * t * g⁻¹ = t := by
  obtain ⟨n, hn, hnt⟩ := exists_normalizing_conj P (x := t) (y := g * t * g⁻¹) (g := g)
    (fun w hw => h.t_central w (hP ▸ hw)) (fun w hw => hg w (hP ▸ hw)) rfl
  rw [← hnt]
  exact h.conj_fix (fun w => by rw [← hP]; exact hn w)

end SqData

end Sylow

end CFSG.EvenSporadicStandard.M22Std
