module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.Certificates

open Subgroup

theorem perfect_hom_comm_trivial {G A : Type*} [Group G] [Group A] [IsMulCommutative A]
    [Group.IsPerfect G] (f : G →* A) (g : G) : f g = 1 := by
  have := Abelianization.commutator_subset_ker f
  have hg : g ∈ commutator G := by simp
  exact this hg

theorem perfect_perm_trivial {G α : Type*} [Group G] [Group.IsPerfect G] [Finite α]
    (hα : Nat.card α ≤ 4) (κ : G →* Equiv.Perm α) (g : G) : κ g = 1 := by
  classical
  have := Fintype.ofFinite α
  have hsign : ∀ x, Equiv.Perm.sign (κ x) = 1 := fun x =>
    perfect_hom_comm_trivial (Equiv.Perm.sign.comp κ) x
  have hmem : ∀ x, κ x ∈ alternatingGroup α := fun x => by
    rw [alternatingGroup, MonoidHom.mem_ker]; exact hsign x
  let κ' : G →* alternatingGroup α := κ.codRestrict _ hmem
  have hsolv : Group.IsSolvable (alternatingGroup α) := alternatingGroup.isSolvable hα
  have hp : Group.IsPerfect κ'.range := Group.IsPerfect.range κ'
  have hs : Group.IsSolvable κ'.range := inferInstance
  by_contra hne
  have hne' : κ' g ≠ 1 := by
    intro h
    apply hne
    have := congrArg Subtype.val h
    simpa [κ'] using this
  have hnt : Nontrivial κ'.range :=
    ⟨⟨⟨κ' g, g, rfl⟩, 1, fun h => hne' (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable κ'.range hs

theorem normal_le_center_of_card_le_four {E : Type*} [Group E] [Group.IsPerfect E]
    (Q : Subgroup E) [Q.Normal] [Finite Q] (hQ : Nat.card Q ≤ 4) : Q ≤ Subgroup.center E := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  have h := perfect_perm_trivial (G := E) (α := Q) hQ ((MulAut.toPerm Q).comp MulAut.conjNormal) g
  have h2 := congrArg (fun p : Equiv.Perm Q => ((p ⟨q, hq⟩ : Q) : E)) h
  have h3 : g * q * g⁻¹ = q := by
    have : (((MulAut.toPerm Q).comp MulAut.conjNormal) g) ⟨q, hq⟩ =
        (MulAut.conjNormal g : MulAut Q) ⟨q, hq⟩ := rfl
    simp only [this, MulAut.conjNormal_apply] at h2
    simpa using h2
  calc g * q = g * q * g⁻¹ * g := by group
    _ = q * g := by rw [h3]

theorem perfect_cover_card_le
    {E J F V : Type*} [Group E] [Group J] [Group F] [CommGroup V]
    [Finite J] [Finite F] [Finite V]
    (φ : E →* J) (hφ : Function.Surjective φ) (π : F →* E)
    (ψ : F →* V) (hψ : Function.Surjective ψ) (hV : Nat.card V = 4)
    [hE : Group.IsPerfect E]
    (hS : ⁅(φ.comp π).range, (φ.comp π).range⁆ = (φ.comp π).range)
    (hF2 : ∀ f : F, Abelianization.of f ^ 2 = 1)
    [hfi : π.range.FiniteIndex] {n m : ℕ} (hn : Odd n)
    (hidx : π.range.index ≤ n) (hF : Nat.card F ≤ 4 * m) (hJ : Nat.card J = n * m)
    (hm : 0 < m) :
    Finite E ∧ Nat.card E ≤ n * m := by
  classical
  set Sg : Subgroup E := π.range with hSg
  set S : Subgroup J := (φ.comp π).range with hSdef
  have hSgfin : Finite Sg := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have hEfin : Finite E := by
    have : Finite (E ⧸ Sg) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient Sg
  refine ⟨hEfin, ?_⟩
  have hn0 : 0 < n := hn.pos
  have hcardSg : Nat.card Sg ≤ Nat.card F :=
    Nat.card_le_card_of_surjective _ π.rangeRestrict_surjective
  have hESg : Nat.card Sg * Sg.index = Nat.card E := Sg.card_mul_index
  set Q : Subgroup E := φ.ker with hQdef
  have hEQ : Nat.card Q * Nat.card J = Nat.card E := by
    have h1 := Q.card_mul_index
    rw [hQdef, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hφ,
      Subgroup.card_top] at h1
    exact h1
  have hkerψ : Nat.card ψ.ker * 4 = Nat.card F := by
    have h1 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top,
      hV] at h1
    exact h1
  have hcommF : Nat.card (commutator F) ≤ m := by
    have h1 : Nat.card (commutator F) ≤ Nat.card ψ.ker :=
      Subgroup.card_le_of_le (Abelianization.commutator_subset_ker ψ)
    omega
  have hSeq : S = map (φ.comp π) (commutator F) := by
    rw [← hS, hSdef, MonoidHom.range_eq_map, ← map_commutator]
    rfl
  have hScard : Nat.card S ≤ m := by
    have h1 : Nat.card (map (φ.comp π) (commutator F)) ≤ Nat.card (commutator F) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective (φ.comp π) _)
    rw [hSeq]; omega
  have hSidx : Nat.card S * S.index = Nat.card J := S.card_mul_index
  have hnS : n ≤ S.index := by
    by_contra h
    push Not at h
    have h1 : S.index ≤ n - 1 := by omega
    have h2 : Nat.card S * S.index ≤ m * (n - 1) := Nat.mul_le_mul hScard h1
    have h3 : m * (n - 1) < n * m := by
      have : n - 1 < n := by omega
      nlinarith
    omega
  have hSmap : S = map φ Sg := by
    rw [hSdef, hSg, MonoidHom.range_comp]
  set T : Subgroup E := Sg ⊔ Q with hT
  have hSindex : S.index = T.index := by
    rw [hSmap, Subgroup.index_map, MonoidHom.range_eq_top_of_surjective φ hφ, Subgroup.index_top,
      mul_one]
  have hdvd : T.index ∣ Sg.index := Subgroup.index_dvd_of_le le_sup_left
  have hSgpos : 0 < Sg.index := Nat.pos_of_ne_zero hfi.index_ne_zero
  have hle1 : T.index ≤ Sg.index := Nat.le_of_dvd hSgpos hdvd
  have hidxeq : Sg.index = n := by omega
  have hSQ : T = Sg := by
    have h1 : T.index = Sg.index := by omega
    have hfin2 : Finite T := inferInstance
    have h2 : Nat.card T * T.index = Nat.card E := T.card_mul_index
    have h3 : Nat.card T = Nat.card Sg := by
      rw [h1] at h2
      exact Nat.eq_of_mul_eq_mul_right hSgpos (h2.trans hESg.symm)
    exact (Subgroup.eq_of_le_of_card_ge (le_sup_left : Sg ≤ T) h3.le).symm
  have hQSg : Q ≤ Sg := by rw [← hSQ]; exact le_sup_right
  have hQcard : Nat.card Q ≤ 4 := by
    have hEle : Nat.card E ≤ 4 * m * n := by
      rw [← hESg, hidxeq]
      exact Nat.mul_le_mul_right n (hcardSg.trans hF)
    have hJpos : 0 < Nat.card J := by rw [hJ]; exact Nat.mul_pos hn0 hm
    have : Nat.card Q * Nat.card J ≤ 4 * Nat.card J := by
      rw [hEQ]; calc Nat.card E ≤ 4 * m * n := hEle
        _ = 4 * Nat.card J := by rw [hJ]; ring
    exact Nat.le_of_mul_le_mul_right this hJpos
  have : Q.Normal := MonoidHom.normal_ker φ
  have : Finite Q := inferInstance
  have hQc : Q ≤ Subgroup.center E := normal_le_center_of_card_le_four Q hQcard
  let ϕ : Sg →* Abelianization Sg := Abelianization.of
  have hV' : ∀ g, MonoidHom.transfer ϕ g = 1 := perfect_hom_comm_trivial (MonoidHom.transfer ϕ)
  have hsq : ∀ s : Sg, ϕ s ^ 2 = 1 := by
    intro s
    obtain ⟨f, rfl⟩ := π.rangeRestrict_surjective s
    have h1 : ϕ (π.rangeRestrict f) =
        Abelianization.map π.rangeRestrict (Abelianization.of f) :=
      (Abelianization.map_of _ _).symm
    rw [h1, ← map_pow, hF2, map_one]
  have hz : ∀ z : Sg, (z : E) ∈ Q → z ∈ commutator Sg := by
    intro z hzQ
    have hcen : (z : E) ∈ Subgroup.center E := hQc hzQ
    have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * (z : E) ^ k * g₀ ∈ Sg →
        g₀⁻¹ * (z : E) ^ k * g₀ = (z : E) ^ k := by
      intro k g₀ _
      have h1 : (z : E) ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hcen k
      have h2 := Subgroup.mem_center_iff.mp h1 g₀
      calc g₀⁻¹ * (z : E) ^ k * g₀ = g₀⁻¹ * ((z : E) ^ k * g₀) := by group
        _ = g₀⁻¹ * (g₀ * (z : E) ^ k) := by rw [h2]
        _ = (z : E) ^ k := by group
    have h1 := MonoidHom.transfer_eq_pow ϕ (z : E) key
    rw [hV'] at h1
    have h2 : ϕ z ^ n = 1 := by
      have h3 : ϕ (⟨(z : E) ^ Sg.index, Subgroup.pow_mem _ z.2 _⟩ : Sg) = ϕ z ^ Sg.index := by
        rw [← map_pow]; rfl
      have h4 := h1.symm
      rw [h3, hidxeq] at h4
      exact h4
    have h5 : ϕ z = 1 := by
      obtain ⟨k, hk⟩ := hn
      calc ϕ z = ϕ z ^ (2 * k + 1) := by
            rw [pow_succ, pow_mul, hsq z, one_pow, one_mul]
        _ = 1 := by rw [← hk]; exact h2
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h5
  have hperf : commutator Sg = ⊤ := by
    rw [eq_top_iff]
    intro s _
    let φS : Sg →* J := φ.comp Sg.subtype
    have hrange : φS.range = S := by
      rw [hSmap, MonoidHom.range_comp, Subgroup.range_subtype]
    have hmapc : map φS (commutator Sg) = S := by
      rw [commutator_def, map_commutator, Subgroup.map_top, hrange, hS]
    have hs : φS s ∈ S := by rw [← hrange]; exact ⟨s, rfl⟩
    rw [← hmapc] at hs
    obtain ⟨c, hc, hcs⟩ := hs
    have h1 : s * c⁻¹ ∈ commutator Sg := by
      apply hz
      show ((s * c⁻¹ : Sg) : E) ∈ φ.ker
      rw [MonoidHom.mem_ker]
      have : φ (s : E) = φ (c : E) := hcs.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, this, mul_inv_cancel]
    have h2 : s * c⁻¹ * c ∈ commutator Sg := Subgroup.mul_mem _ h1 hc
    simpa using h2
  have hcardSg' : Nat.card Sg ≤ m := by
    have hmapc : map π.rangeRestrict (commutator F) = commutator Sg := by
      rw [commutator_def, commutator_def, map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ π.rangeRestrict_surjective]
    calc Nat.card Sg = Nat.card (⊤ : Subgroup Sg) := Subgroup.card_top.symm
      _ = Nat.card (map π.rangeRestrict (commutator F)) := by rw [hmapc, hperf]
      _ ≤ Nat.card (commutator F) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
      _ ≤ m := hcommF
  rw [← hESg, hidxeq, mul_comm n m]
  exact Nat.mul_le_mul_right n hcardSg'

end CFSG.Certificates
