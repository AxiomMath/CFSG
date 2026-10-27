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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open scoped commutatorElement MatrixGroups

section Commuting

variable {G : Type*} [Group G]

theorem exists_mul_eq_of_mem_sup_of_forall_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  have comm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
    hAB m m.2 n n.2
  have h := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
  have hg' : g ∈ (MonoidHom.noncommCoprod A.subtype B.subtype comm).range := by
    rw [h]
    exact hg
  obtain ⟨⟨a, b⟩, rfl⟩ := hg'
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem commutatorElement_mul_mul_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a₁ a₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  have comm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
    hAB m m.2 n n.2
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype comm with hφ
  have h := map_commutatorElement φ (⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩) (⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩)
  have e : (⁅((⟨a₁, ha₁⟩ : A), (⟨b₁, hb₁⟩ : B)), ((⟨a₂, ha₂⟩ : A), (⟨b₂, hb₂⟩ : B))⁆ : A × B) =
      (⁅(⟨a₁, ha₁⟩ : A), ⟨a₂, ha₂⟩⁆, ⁅(⟨b₁, hb₁⟩ : B), ⟨b₂, hb₂⟩⁆) := by
    ext <;> simp [commutatorElement_def]
  rw [e] at h
  simpa [hφ, commutatorElement_def] using h.symm

theorem commute_commutator_of_central_commutators {A : Subgroup G} {a u v : G} (ha : a ∈ A)
    (hu : u ∈ A) (hv : v ∈ A) (hzu : ∀ w ∈ A, ⁅u, a⁆ * w = w * ⁅u, a⁆)
    (hzv : ∀ w ∈ A, ⁅v, a⁆ * w = w * ⁅v, a⁆) : ⁅u, v⁆ * a = a * ⁅u, v⁆ := by
  set zu : G := ⁅u, a⁆ with hzu_def
  set zv : G := ⁅v, a⁆ with hzv_def
  have hzuA : zu ∈ A := by
    rw [hzu_def, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem hu ha) (A.inv_mem hu)) (A.inv_mem ha)
  have hzvA : zv ∈ A := by
    rw [hzv_def, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem hv ha) (A.inv_mem hv)) (A.inv_mem ha)
  have cu : u * a * u⁻¹ = zu * a := by rw [hzu_def, commutatorElement_def]; group
  have cv : v * a * v⁻¹ = zv * a := by rw [hzv_def, commutatorElement_def]; group
  have fu : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → ∀ x : G, u⁻¹ * (z * x) * u = z * (u⁻¹ * x * u) := by
    intro z hz hzc x
    have h1 : u⁻¹ * z * u = z := by
      have := hzc u hu
      rw [mul_assoc, this]
      group
    calc u⁻¹ * (z * x) * u = (u⁻¹ * z * u) * (u⁻¹ * x * u) := by group
      _ = z * (u⁻¹ * x * u) := by rw [h1]
  have fv : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → ∀ x : G, v * (z * x) * v⁻¹ = z * (v * x * v⁻¹) := by
    intro z hz hzc x
    have h1 : v * z * v⁻¹ = z := by
      have := hzc v hv
      rw [← this]
      group
    calc v * (z * x) * v⁻¹ = (v * z * v⁻¹) * (v * x * v⁻¹) := by group
      _ = z * (v * x * v⁻¹) := by rw [h1]
  have fu' : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → ∀ x : G,
      u * (z * x) * u⁻¹ = z * (u * x * u⁻¹) := by
    intro z hz hzc x
    have h1 : u * z * u⁻¹ = z := by
      have := hzc u hu
      rw [← this]
      group
    calc u * (z * x) * u⁻¹ = (u * z * u⁻¹) * (u * x * u⁻¹) := by group
      _ = z * (u * x * u⁻¹) := by rw [h1]
  have cu' : u⁻¹ * a * u = zu⁻¹ * a := by
    have h1 : a = u⁻¹ * (zu * a) * u := by
      rw [← cu]
      group
    rw [fu zu hzuA hzu a] at h1
    calc u⁻¹ * a * u = zu⁻¹ * (zu * (u⁻¹ * a * u)) := by group
      _ = zu⁻¹ * a := by rw [← h1]
  have cv' : v⁻¹ * a * v = zv⁻¹ * a := by
    have h1 : a = v⁻¹ * (zv * a) * v := by
      rw [← cv]
      group
    have e1 : v⁻¹ * (zv * a) * v = zv * (v⁻¹ * a * v) := by
      have h2 : v⁻¹ * zv * v = zv := by
        have := hzv v hv
        rw [mul_assoc, this]
        group
      calc v⁻¹ * (zv * a) * v = (v⁻¹ * zv * v) * (v⁻¹ * a * v) := by group
        _ = zv * (v⁻¹ * a * v) := by rw [h2]
    rw [e1] at h1
    calc v⁻¹ * a * v = zv⁻¹ * (zv * (v⁻¹ * a * v)) := by group
      _ = zv⁻¹ * a := by rw [← h1]
  have hzz : ∀ z₁ z₂ : G, z₁ ∈ A → (∀ w ∈ A, z₁ * w = w * z₁) → z₂ ∈ A → z₁ * z₂ = z₂ * z₁ :=
    fun z₁ z₂ _ h hz₂ => h z₂ hz₂
  have key : (u * v * u⁻¹ * v⁻¹) * a * (u * v * u⁻¹ * v⁻¹)⁻¹ = a := by
    calc (u * v * u⁻¹ * v⁻¹) * a * (u * v * u⁻¹ * v⁻¹)⁻¹
        = u * (v * (u⁻¹ * (v⁻¹ * a * v) * u) * v⁻¹) * u⁻¹ := by group
      _ = u * (v * (u⁻¹ * (zv⁻¹ * a) * u) * v⁻¹) * u⁻¹ := by rw [cv']
      _ = u * (v * (zv⁻¹ * (u⁻¹ * a * u)) * v⁻¹) * u⁻¹ := by
          rw [fu zv⁻¹ (A.inv_mem hzvA)
            (fun w hw => by
              have := hzv w hw
              calc zv⁻¹ * w = zv⁻¹ * (w * zv) * zv⁻¹ := by group
                _ = zv⁻¹ * (zv * w) * zv⁻¹ := by rw [this]
                _ = w * zv⁻¹ := by group)]
      _ = u * (v * (zv⁻¹ * (zu⁻¹ * a)) * v⁻¹) * u⁻¹ := by rw [cu']
      _ = u * (zv⁻¹ * (zu⁻¹ * (v * a * v⁻¹))) * u⁻¹ := by
          rw [fv zv⁻¹ (A.inv_mem hzvA) (fun w hw => by
              have := hzv w hw
              calc zv⁻¹ * w = zv⁻¹ * (w * zv) * zv⁻¹ := by group
                _ = zv⁻¹ * (zv * w) * zv⁻¹ := by rw [this]
                _ = w * zv⁻¹ := by group),
            fv zu⁻¹ (A.inv_mem hzuA) (fun w hw => by
              have := hzu w hw
              calc zu⁻¹ * w = zu⁻¹ * (w * zu) * zu⁻¹ := by group
                _ = zu⁻¹ * (zu * w) * zu⁻¹ := by rw [this]
                _ = w * zu⁻¹ := by group)]
      _ = u * (zv⁻¹ * (zu⁻¹ * (zv * a))) * u⁻¹ := by rw [cv]
      _ = u * (zu⁻¹ * a) * u⁻¹ := by
          have e : zv⁻¹ * (zu⁻¹ * (zv * a)) = zu⁻¹ * a := by
            have h1 : zu⁻¹ * zv = zv * zu⁻¹ := by
              have := hzu zv hzvA
              calc zu⁻¹ * zv = zu⁻¹ * (zv * zu) * zu⁻¹ := by group
                _ = zu⁻¹ * (zu * zv) * zu⁻¹ := by rw [← this]
                _ = zv * zu⁻¹ := by group
            calc zv⁻¹ * (zu⁻¹ * (zv * a)) = zv⁻¹ * ((zu⁻¹ * zv) * a) := by group
              _ = zv⁻¹ * ((zv * zu⁻¹) * a) := by rw [h1]
              _ = zu⁻¹ * a := by group
          rw [e]
      _ = zu⁻¹ * (u * a * u⁻¹) := by
          rw [fu' zu⁻¹ (A.inv_mem hzuA) (fun w hw => by
              have := hzu w hw
              calc zu⁻¹ * w = zu⁻¹ * (w * zu) * zu⁻¹ := by group
                _ = zu⁻¹ * (zu * w) * zu⁻¹ := by rw [this]
                _ = w * zu⁻¹ := by group)]
      _ = a := by rw [cu]; group
  have e2 : (u * v * u⁻¹ * v⁻¹) * a = a * (u * v * u⁻¹ * v⁻¹) := by
    have := key
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  simpa [commutatorElement_def] using e2

theorem commute_of_mem_center_of_isPerfect_of_le_sup {A B P : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hCA : ∀ a ∈ A, (∃ w ∈ A, a * w ≠ w * a) → ∀ u ∈ A, u * a = a * u → ∀ v ∈ A,
      v * a = a * v → u * v = v * u)
    (hP : P ≤ A ⊔ B) (hperf : ⁅P, P⁆ = P) {c : G} (hc : c ∈ P) (hcP : ∀ y ∈ P, c * y = y * c) :
    ∀ u ∈ A, c * u = u * c := by
  obtain ⟨a, haA, b, hbB, rfl⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hAB (hP hc)
  suffices hz : ∀ w ∈ A, a * w = w * a by
    intro u hu
    have e1 : a * b * u = (a * u) * b := by
      rw [mul_assoc, ← hAB u hu b hbB, ← mul_assoc]
    have e2 : u * (a * b) = (u * a) * b := by rw [mul_assoc]
    rw [e1, e2, hz u hu]
  by_contra hnc
  push Not at hnc
  obtain ⟨w₀, hw₀, hw₀ne⟩ := hnc
  set C : Subgroup G := A ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hCA' : ∀ u ∈ C, ∀ v ∈ C, u * v = v * u := by
    intro u hu v hv
    exact hCA a haA ⟨w₀, hw₀, hw₀ne⟩ u hu.1 (Subgroup.mem_centralizer_singleton_iff.1 hu.2) v hv.1
      (Subgroup.mem_centralizer_singleton_iff.1 hv.2)
  have hCB : ∀ u ∈ C, ∀ v ∈ B, u * v = v * u := fun u hu v hv => hAB u hu.1 v hv
  have central : ∀ g' ∈ P, ∀ a' b' : G, a' ∈ A → b' ∈ B → g' = a' * b' →
      ∀ w ∈ A, ⁅a', a⁆ * w = w * ⁅a', a⁆ := by
    intro g' hg' a' b' ha' hb' hg'e w hw
    have hcomm := hcP g' hg'
    rw [hg'e] at hcomm
    have h1 : ⁅a' * b', a * b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    rw [commutatorElement_mul_mul_of_commute hAB ha' haA hb' hbB] at h1
    have h2 : ⁅a', a⁆ = ⁅b', b⁆⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hbb : ⁅b', b⁆⁻¹ ∈ B := by
      rw [commutatorElement_inv, commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem hbB hb') (B.inv_mem hbB)) (B.inv_mem hb')
    rw [h2]
    exact (hAB w hw _ hbb).symm
  have hPQ : P ≤ C ⊔ B := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hAB (hP hg)
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hAB (hP hh)
    rw [commutatorElement_mul_mul_of_commute hAB ha₁ ha₂ hb₁ hb₂]
    have hbb : ⁅b₁, b₂⁆ ∈ B := by
      rw [commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
    have haa : ⁅a₁, a₂⁆ ∈ C := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (commute_commutator_of_central_commutators haA ha₁ ha₂
            (central _ hg a₁ b₁ ha₁ hb₁ rfl) (central _ hh a₂ b₂ ha₂ hb₂ rfl))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haa) (Subgroup.mem_sup_right hbb)
  have hPB : P ≤ B := by
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    obtain ⟨c₁, hc₁, b₁, hb₁, hg'⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hCB (hPQ hg)
    obtain ⟨c₂, hc₂, b₂, hb₂, hh'⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hCB (hPQ hh)
    rw [hg', hh', commutatorElement_mul_mul_of_commute hCB hc₁ hc₂ hb₁ hb₂,
      commutatorElement_eq_one_iff_mul_comm.2 (hCA' c₁ hc₁ c₂ hc₂), one_mul]
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
  have haB : a ∈ B := by
    have hcB : a * b ∈ B := hPB hc
    have := B.mul_mem hcB (B.inv_mem hbB)
    simpa using this
  exact hw₀ne (by
    have := hAB w₀ hw₀ a haB
    exact this.symm)

end Commuting

section Family

variable {G : Type*} [Group G] {ι : Type*}

theorem eq_one_or_eq_of_mem_center_of_le_iSup [Finite ι] (A : ι → Subgroup G) (x : G)
    (hcomm : Pairwise fun i j => ∀ u ∈ A i, ∀ v ∈ A j, u * v = v * u) (hx : ∀ i, x ∈ A i)
    (hx2 : x * x = 1) (hxc : ∀ i, ∀ u ∈ A i, x * u = u * x)
    (hZ : ∀ i, ∀ z ∈ A i, (∀ u ∈ A i, z * u = u * z) → z = 1 ∨ z = x)
    (hCA : ∀ i, ∀ a ∈ A i, (∃ w ∈ A i, a * w ≠ w * a) → ∀ u ∈ A i, u * a = a * u →
      ∀ v ∈ A i, v * a = a * v → u * v = v * u)
    {P : Subgroup G} (hP : P ≤ ⨆ i, A i) (hperf : ⁅P, P⁆ = P) {c : G} (hc : c ∈ P)
    (hcP : ∀ y ∈ P, c * y = y * c) : c = 1 ∨ c = x := by
  classical
  have := Fintype.ofFinite ι
  have hcA : ∀ i, ∀ u ∈ A i, c * u = u * c := by
    intro i
    have hAB : ∀ a ∈ A i, ∀ b ∈ (⨆ (j) (_ : j ≠ i), A j : Subgroup G), a * b = b * a := by
      intro a ha b hb
      have hle : (⨆ (j) (_ : j ≠ i), A j : Subgroup G) ≤ Subgroup.centralizer (A i : Set G) := by
        refine iSup₂_le fun j hj v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact hcomm (Ne.symm hj) u hu v hv
      exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha
    exact commute_of_mem_center_of_isPerfect_of_le_sup hAB (hCA i)
      (by rw [← iSup_split_single]; exact hP) hperf hc hcP
  have hS : ∀ S : Finset ι, ∀ c' ∈ (⨆ i ∈ S, A i : Subgroup G),
      (∀ i ∈ S, ∀ u ∈ A i, c' * u = u * c') → c' = 1 ∨ c' = x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro c' hc' _
      left
      simpa using hc'
    | insert j S hj ih =>
      intro c' hc' hc'comm
      rw [Finset.iSup_insert] at hc'
      have hAB : ∀ a ∈ A j, ∀ b ∈ (⨆ i ∈ S, A i : Subgroup G), a * b = b * a := by
        intro a ha b hb
        have hle : (⨆ i ∈ S, A i : Subgroup G) ≤ Subgroup.centralizer (A j : Set G) := by
          refine iSup₂_le fun i hi v hv => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro u hu
          exact hcomm (show j ≠ i from fun h => hj (by rw [h]; exact hi)) u hu v hv
        exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_forall_commute hAB hc'
      have haZ : ∀ u ∈ A j, a * u = u * a := by
        intro u hu
        have h1 := hc'comm j (Finset.mem_insert_self j S) u hu
        have h2 := hAB u hu b hb
        have e1 : a * b * u = a * u * b := by rw [mul_assoc, ← h2, ← mul_assoc]
        have e2 : u * (a * b) = u * a * b := by rw [mul_assoc]
        rw [e1, e2] at h1
        exact mul_right_cancel h1
      rcases hZ j a ha haZ with rfl | rfl
      · rw [one_mul] at hc' hc'comm ⊢
        refine ih b hb fun i hi u hu => hc'comm i (Finset.mem_insert_of_mem hi) u hu
      · have hb' : ∀ i ∈ S, ∀ u ∈ A i, b * u = u * b := by
          intro i hi u hu
          have h1 := hc'comm i (Finset.mem_insert_of_mem hi) u hu
          have h2 := hxc i u hu
          have : a * (b * u) = a * (u * b) := by
            calc a * (b * u) = a * b * u := by rw [mul_assoc]
              _ = u * (a * b) := h1
              _ = u * a * b := by rw [mul_assoc]
              _ = a * u * b := by rw [← h2]
              _ = a * (u * b) := by rw [mul_assoc]
          exact mul_left_cancel this
        rcases ih b hb hb' with rfl | rfl
        · right
          rw [mul_one]
        · left
          exact hx2
  have h := hS Finset.univ c (by simpa using hP hc) fun i _ u hu => hcA i u hu
  exact h

end Family

section SL2

variable {F : Type*} [Field F]

theorem matrix_commute_of_commute_of_not_scalar {a u v : Matrix (Fin 2) (Fin 2) F}
    (ha : ¬(a 0 1 = 0 ∧ a 1 0 = 0 ∧ a 0 0 = a 1 1)) (hu : u * a = a * u) (hv : v * a = a * v) :
    u * v = v * u := by
  have eu := fun i j => congrFun (congrFun hu i) j
  have ev := fun i j => congrFun (congrFun hv i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at eu ev
  have u1 := eu 0 0
  have u2 := eu 0 1
  have u3 := eu 1 0
  have v1 := ev 0 0
  have v2 := ev 0 1
  have v3 := ev 1 0
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hb : a 0 1 = 0
  · by_cases hg : a 1 0 = 0
    · have hd : a 0 0 ≠ a 1 1 := fun h => ha ⟨hb, hg, h⟩
      have hd' : a 0 0 - a 1 1 ≠ 0 := sub_ne_zero.2 hd
      have hq : u 0 1 = 0 := by
        have : u 0 1 * (a 0 0 - a 1 1) = 0 := by rw [hb] at u2; linear_combination -u2
        exact (mul_eq_zero.1 this).resolve_right hd'
      have hr : u 1 0 = 0 := by
        have : u 1 0 * (a 0 0 - a 1 1) = 0 := by rw [hg] at u3; linear_combination u3
        exact (mul_eq_zero.1 this).resolve_right hd'
      have hq' : v 0 1 = 0 := by
        have : v 0 1 * (a 0 0 - a 1 1) = 0 := by rw [hb] at v2; linear_combination -v2
        exact (mul_eq_zero.1 this).resolve_right hd'
      have hr' : v 1 0 = 0 := by
        have : v 1 0 * (a 0 0 - a 1 1) = 0 := by rw [hg] at v3; linear_combination v3
        exact (mul_eq_zero.1 this).resolve_right hd'
      fin_cases i <;> fin_cases j <;> simp [hq, hr, hq', hr'] <;> ring
    ·
      have hq : u 0 1 = 0 := by
        have : u 0 1 * a 1 0 = 0 := by rw [hb] at u1; linear_combination u1
        exact (mul_eq_zero.1 this).resolve_right hg
      have hq' : v 0 1 = 0 := by
        have : v 0 1 * a 1 0 = 0 := by rw [hb] at v1; linear_combination v1
        exact (mul_eq_zero.1 this).resolve_right hg
      have hs : u 1 1 = u 0 0 + u 1 0 * (a 1 1 - a 0 0) / a 1 0 := by
        field_simp
        linear_combination u3
      have hs' : v 1 1 = v 0 0 + v 1 0 * (a 1 1 - a 0 0) / a 1 0 := by
        field_simp
        linear_combination v3
      fin_cases i <;> fin_cases j <;> simp [hq, hq', hs, hs']
      all_goals ring
  · have hr : u 1 0 = u 0 1 * a 1 0 / a 0 1 := by
      field_simp
      linear_combination -u1
    have hr' : v 1 0 = v 0 1 * a 1 0 / a 0 1 := by
      field_simp
      linear_combination -v1
    have hs : u 1 1 = u 0 0 + u 0 1 * (a 1 1 - a 0 0) / a 0 1 := by
      field_simp
      linear_combination -u2
    have hs' : v 1 1 = v 0 0 + v 0 1 * (a 1 1 - a 0 0) / a 0 1 := by
      field_simp
      linear_combination -v2
    fin_cases i <;> fin_cases j <;> simp [hr, hr', hs, hs'] <;> field_simp <;> ring

theorem sl2_mem_center_iff_one_or_neg_one {A : SL(2, F)} :
    A ∈ Subgroup.center SL(2, F) ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    simp only [Fintype.card_fin] at hr
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h | h
    · left
      apply Subtype.ext
      rw [← hrA, sub_eq_zero.mp h, Matrix.SpecialLinearGroup.coe_one, map_one]
    · right
      apply Subtype.ext
      rw [← hrA, eq_neg_of_add_eq_zero_left h, Matrix.SpecialLinearGroup.coe_neg, map_neg,
        map_one]
      simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨-1, by simp, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem sl2_commute_of_commute_of_not_mem_center {a u v : SL(2, F)}
    (ha : a ∉ Subgroup.center SL(2, F)) (hu : u * a = a * u) (hv : v * a = a * v) :
    u * v = v * u := by
  refine Subtype.ext (matrix_commute_of_commute_of_not_scalar ?_ (congrArg Subtype.val hu)
    (congrArg Subtype.val hv))
  rintro ⟨hb, hg, hd⟩
  apply ha
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨a 0 0, ?_, ?_⟩
  · have h := a.det_coe
    rw [Matrix.det_fin_two, hb, hg, ← hd] at h
    simp only [Fintype.card_fin]
    linear_combination h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hg, hd]

end SL2

section Range

variable {G : Type*} [Group G] {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]

theorem eq_one_or_eq_of_isPerfect_of_le_iSup_range [Finite ι] (φ : ∀ i, SL(2, F i) →* G)
    (hinj : ∀ i, Function.Injective (φ i)) (x : G) (hx : ∀ i, φ i (-1) = x) (hx2 : x * x = 1)
    (hcomm : Pairwise fun i j => ∀ A B, φ i A * φ j B = φ j B * φ i A)
    {P : Subgroup G} (hP : P ≤ ⨆ i, (φ i).range) (hperf : ⁅P, P⁆ = P) {c : G} (hc : c ∈ P)
    (hcP : ∀ y ∈ P, c * y = y * c) : c = 1 ∨ c = x := by
  have hneg : ∀ (i) (B : SL(2, F i)), (-1 : SL(2, F i)) * B = B * (-1) := fun i B => by
    have := (sl2_mem_center_iff_one_or_neg_one (A := (-1 : SL(2, F i)))).2 (Or.inr rfl)
    exact Subgroup.mem_center_iff.1 this B |>.symm
  refine eq_one_or_eq_of_mem_center_of_le_iSup (fun i => (φ i).range) x ?_ ?_ hx2 ?_ ?_ ?_ hP
    hperf hc hcP
  · intro i j hij u hu v hv
    obtain ⟨A, rfl⟩ := hu
    obtain ⟨B, rfl⟩ := hv
    exact hcomm hij A B
  · intro i
    exact ⟨-1, hx i⟩
  · intro i u hu
    obtain ⟨A, rfl⟩ := hu
    rw [← hx i, ← map_mul, ← map_mul, hneg i A]
  · intro i z hz hzc
    obtain ⟨Z, rfl⟩ := hz
    have hZ : Z ∈ Subgroup.center SL(2, F i) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply hinj i
      rw [map_mul, map_mul]
      exact (hzc (φ i B) ⟨B, rfl⟩).symm
    rcases (sl2_mem_center_iff_one_or_neg_one).1 hZ with rfl | rfl
    · left
      exact map_one _
    · right
      exact hx i
  · intro i a ha hnc u hu hua v hv hva
    obtain ⟨A, rfl⟩ := ha
    obtain ⟨U, rfl⟩ := hu
    obtain ⟨V, rfl⟩ := hv
    have hA : A ∉ Subgroup.center SL(2, F i) := by
      intro hA
      obtain ⟨_, ⟨B, rfl⟩, hB⟩ := hnc
      apply hB
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hA B]
    have hUA : U * A = A * U := hinj i (by rw [map_mul, map_mul]; exact hua)
    have hVA : V * A = A * V := hinj i (by rw [map_mul, map_mul]; exact hva)
    rw [← map_mul, ← map_mul, sl2_commute_of_commute_of_not_mem_center hA hUA hVA]

end Range

end CFSG.ClassicalInvolution.Balance.Bootstrap
