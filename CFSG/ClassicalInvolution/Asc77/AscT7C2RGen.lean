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

namespace CFSG.ClassicalInvolution.Asc77.T7C2

open Subgroup

variable {S Q : Type*} [Group S] [Group Q]

@[expose] def GenLE (H : Subgroup S) (n : ℕ) : Prop :=
  ∃ s : Finset S, s.card ≤ n ∧ Subgroup.closure (s : Set S) = H

theorem GenLE.mono {H : Subgroup S} {m n : ℕ} (h : GenLE H m) (hmn : m ≤ n) : GenLE H n := by
  obtain ⟨s, hs, hsc⟩ := h
  exact ⟨s, hs.trans hmn, hsc⟩

open scoped Classical in
theorem exists_lift_finset (φ : S →* Q) (H : Subgroup S) (t : Finset Q)
    (ht : ∀ y ∈ t, y ∈ H.map φ) :
    ∃ L : Finset S, L.card ≤ t.card ∧ (∀ x ∈ L, x ∈ H) ∧ L.image φ = t := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert y t hy ih =>
    obtain ⟨L, hL, hLH, hLt⟩ := ih (fun z hz => ht z (Finset.mem_insert_of_mem hz))
    obtain ⟨h, hhH, hhy⟩ := ht y (Finset.mem_insert_self y t)
    refine ⟨insert h L, ?_, ?_, ?_⟩
    · calc (insert h L).card ≤ L.card + 1 := Finset.card_insert_le _ _
        _ ≤ t.card + 1 := by omega
        _ = (insert y t).card := (Finset.card_insert_of_notMem hy).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hhH
      · exact hLH x hx
    · rw [Finset.image_insert, hLt, hhy]

theorem GenLE.of_ker (φ : S →* Q) (H : Subgroup S) {a b : ℕ} (hk : GenLE (H ⊓ φ.ker) a)
    (hr : GenLE (H.map φ) b) : GenLE H (a + b) := by
  classical
  obtain ⟨s, hs, hsc⟩ := hk
  obtain ⟨t, ht, htc⟩ := hr
  have htmem : ∀ y ∈ t, y ∈ H.map φ := fun y hy => htc ▸ Subgroup.subset_closure hy
  obtain ⟨L, hL, hLH, hLt⟩ := exists_lift_finset φ H t htmem
  refine ⟨s ∪ L, ?_, ?_⟩
  · calc (s ∪ L).card ≤ s.card + L.card := Finset.card_union_le _ _
      _ ≤ a + b := by omega
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have : x ∈ H ⊓ φ.ker := hsc ▸ Subgroup.subset_closure hx
        exact this.1
      · exact hLH x hx
    · intro h hh
      have hφ : φ h ∈ Subgroup.closure (φ '' (L : Set S)) := by
        have : (φ '' (L : Set S)) = (t : Set Q) := by
          rw [← Finset.coe_image, hLt]
        rw [this, htc]
        exact ⟨h, hh, rfl⟩
      rw [← MonoidHom.map_closure] at hφ
      obtain ⟨n, hn, hnh⟩ := hφ
      have hnH : n ∈ H := by
        have : Subgroup.closure (L : Set S) ≤ H := by
          rw [Subgroup.closure_le]
          intro x hx
          exact hLH x hx
        exact this hn
      have hker : n⁻¹ * h ∈ H ⊓ φ.ker := by
        refine ⟨H.mul_mem (H.inv_mem hnH) hh, ?_⟩
        show φ (n⁻¹ * h) = 1
        rw [map_mul, map_inv, hnh, inv_mul_cancel]
      have h1 : n⁻¹ * h ∈ Subgroup.closure ((s ∪ L : Finset S) : Set S) := by
        have : n⁻¹ * h ∈ Subgroup.closure (s : Set S) := hsc ▸ hker
        exact Subgroup.closure_mono (by simp) this
      have h2 : n ∈ Subgroup.closure ((s ∪ L : Finset S) : Set S) :=
        Subgroup.closure_mono (by simp) hn
      have := (Subgroup.closure ((s ∪ L : Finset S) : Set S)).mul_mem h2 h1
      simpa using this

section Cyclic

theorem GenLE.of_subgroupOf {Z : Subgroup S} {B : Subgroup S} (hB : B ≤ Z) {n : ℕ}
    (h : GenLE (B.subgroupOf Z) n) : GenLE B n := by
  classical
  obtain ⟨s, hs, hsc⟩ := h
  refine ⟨s.image Z.subtype, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsc, Subgroup.map_subgroupOf_eq_of_le hB]

theorem GenLE.of_le_zpowers {a : S} {H : Subgroup S} (h : H ≤ Subgroup.zpowers a) :
    GenLE H 1 := by
  apply GenLE.of_subgroupOf h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(H.subgroupOf (Subgroup.zpowers a)))
  refine ⟨{(g : ↥(Subgroup.zpowers a))}, by simp, ?_⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    rw [hx]
    exact g.2
  · intro x hx
    obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
    have : x = (g : ↥(Subgroup.zpowers a)) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [this]
    exact zpow_mem (Subgroup.subset_closure (by simp)) k

end Cyclic

theorem GenLE.of_isCyclic [IsCyclic S] (H : Subgroup S) : GenLE H 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  exact GenLE.of_le_zpowers (a := g) (fun x _ => hg x)

section Abelian

theorem genLE_two_of_abelian {A : Type*} [Group A] {a b : A} (hab : a * b = b * a)
    (hgen : Subgroup.closure ({a, b} : Set A) = ⊤) (B : Subgroup A) : GenLE B 2 := by
  have hcentral : ∀ g : A, g * a = a * g := by
    intro g
    have hg : g ∈ Subgroup.closure ({a, b} : Set A) := hgen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rfl
      · exact hab.symm
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * a) * x⁻¹ := by rw [← hx]
        _ = a * x⁻¹ := by group
  have hnorm : (Subgroup.zpowers a).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g a := hcentral g
    have h1 : g * a ^ k = a ^ k * g := (Commute.zpow_right hc k).eq
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hker : (QuotientGroup.mk' (Subgroup.zpowers a)).ker = Subgroup.zpowers a :=
    QuotientGroup.ker_mk' _
  have h1 : GenLE (B ⊓ (QuotientGroup.mk' (Subgroup.zpowers a)).ker) 1 :=
    GenLE.of_le_zpowers (a := a) (fun x hx => by rw [← hker]; exact hx.2)
  have hcyc : IsCyclic (A ⧸ Subgroup.zpowers a) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨QuotientGroup.mk' (Subgroup.zpowers a) b, ?_⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : g ∈ Subgroup.closure ({a, b} : Set A) := hgen ▸ Subgroup.mem_top g
    have hle : Subgroup.closure ({a, b} : Set A) ≤
        (Subgroup.zpowers (QuotientGroup.mk' (Subgroup.zpowers a) b)).comap
          (QuotientGroup.mk' (Subgroup.zpowers a)) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · have h0 : (QuotientGroup.mk' (Subgroup.zpowers a)) x = 1 := by
          rw [← MonoidHom.mem_ker, hker, hx]
          exact Subgroup.mem_zpowers a
        exact Subgroup.mem_comap.mpr (by rw [h0]; exact Subgroup.one_mem _)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
    exact hle hg
  have h2 : GenLE (B.map (QuotientGroup.mk' (Subgroup.zpowers a))) 1 :=
    GenLE.of_isCyclic _
  exact GenLE.of_ker (QuotientGroup.mk' (Subgroup.zpowers a)) B h1 h2

end Abelian

section S4

open Equiv

@[expose] def invs4 : List (Perm (Fin 4)) :=
  [swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3, swap 0 1 * swap 2 3,
    swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem mem_invs4 : ∀ x : Perm (Fin 4), x * x = 1 → x ≠ 1 → x ∈ invs4 := by decide

theorem invs4_dependent : ∀ a ∈ invs4, ∀ b ∈ invs4, a ≠ b → a * b = b * a →
    ∀ c ∈ invs4, a * c = c * a → b * c = c * b → c = a ∨ c = b ∨ c = a * b := by
  decide +kernel

theorem pow_four_of_pow_eight : ∀ x : Perm (Fin 4), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

theorem genLE_two_of_isPGroup_perm4 (Q : Subgroup (Perm (Fin 4))) (hQ : IsPGroup 2 Q) :
    GenLE Q 2 := by
  classical
  have hdvd24 : Nat.card Q ∣ 24 := by
    have h24 : Nat.card (Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [← h24]
    exact Subgroup.card_subgroup_dvd_card Q
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd8 : Nat.card Q ∣ 8 := by
    rw [hk] at hdvd24 ⊢
    have hk3 : k ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h16.trans hdvd24
      norm_num at this
    exact (pow_dvd_pow 2 hk3 : 2 ^ k ∣ 2 ^ 3)
  have hx4 : ∀ x ∈ Q, x ^ 4 = 1 := fun x hx =>
    pow_four_of_pow_eight x
      (orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard Q hx).trans hdvd8))
  by_cases h4 : ∃ a ∈ Q, orderOf a = 4
  · obtain ⟨a, haQ, ha4⟩ := h4
    by_cases hqa : Subgroup.zpowers a = Q
    · exact (GenLE.of_le_zpowers (le_of_eq hqa.symm)).mono (by norm_num)
    · have hex : ∃ b ∈ Q, b ∉ Subgroup.zpowers a := by
        by_contra hcon
        push Not at hcon
        exact hqa (le_antisymm (Subgroup.zpowers_le.mpr haQ) hcon)
      obtain ⟨b, hbQ, hbn⟩ := hex
      refine ⟨{a, b}, Finset.card_le_two, ?_⟩
      have hle : Subgroup.closure (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) ≤ Q := by
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact haQ
        · exact hbQ
      have hz : Subgroup.zpowers a ≤
          Subgroup.closure (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      have hb : b ∈ Subgroup.closure (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) :=
        Subgroup.subset_closure (by simp)
      have hcardz : Nat.card (Subgroup.zpowers a) = 4 := by rw [Nat.card_zpowers, ha4]
      have hlt : 4 < Nat.card (Subgroup.closure
          (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))) := by
        by_contra hnot
        have hle2 : Nat.card (Subgroup.closure
            (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))) ≤
            Nat.card (Subgroup.zpowers a) := by omega
        exact hbn ((Subgroup.eq_of_le_of_card_ge hz hle2) ▸ hb)
      have hCdvd : Nat.card (Subgroup.closure
          (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))) ∣ 8 :=
        (Subgroup.card_dvd_of_le hle).trans hdvd8
      have hC8 : Nat.card (Subgroup.closure
          (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))) = 8 := by
        have hle8 := Nat.le_of_dvd (by norm_num) hCdvd
        generalize Nat.card (Subgroup.closure
          (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))) = c at hlt hCdvd hle8
        interval_cases c <;> omega
      have hQ8 : Nat.card Q ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  · push Not at h4
    have hsq : ∀ x ∈ Q, x * x = 1 := by
      intro x hx
      have h1 : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr (hx4 x hx)
      have h2 : orderOf x ≠ 4 := h4 x hx
      have h3 : orderOf x ∣ 2 := by
        have hle4 : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) h1
        have hpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
        interval_cases h : orderOf x <;> omega
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
      intro x hx y hy
      have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq (x * y) (Q.mul_mem hx hy))
      calc x * y = (x * y)⁻¹ := hxy'.symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
        _ = y * x := by rw [hx', hy']
    by_cases hbot : Q = ⊥
    · exact ⟨∅, by simp, by simp [hbot]⟩
    obtain ⟨⟨a, haQ⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
    by_cases hqa : Subgroup.zpowers a = Q
    · exact (GenLE.of_le_zpowers (le_of_eq hqa.symm)).mono (by norm_num)
    have hex : ∃ b ∈ Q, b ∉ Subgroup.zpowers a := by
      by_contra hcon
      push Not at hcon
      exact hqa (le_antisymm (Subgroup.zpowers_le.mpr haQ) hcon)
    obtain ⟨b, hbQ, hbn⟩ := hex
    refine ⟨{a, b}, Finset.card_le_two, ?_⟩
    have hle : Subgroup.closure (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) ≤ Q := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haQ
      · exact hbQ
    refine le_antisymm hle fun c hc => ?_
    by_contra hcn
    have hmem : ∀ x : Perm (Fin 4), x ∈ ({a, b} : Finset (Perm (Fin 4))) →
        x ∈ Subgroup.closure (({a, b} : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) :=
      fun x hx => Subgroup.subset_closure (by simpa using hx)
    have hb1 : b ≠ 1 := fun h => hbn (h ▸ Subgroup.one_mem _)
    have hc1 : c ≠ 1 := fun h => hcn (h ▸ Subgroup.one_mem _)
    have hab : a ≠ b := fun h => hbn (h ▸ Subgroup.mem_zpowers a)
    rcases invs4_dependent a (mem_invs4 a (hsq a haQ) ha1) b (mem_invs4 b (hsq b hbQ) hb1) hab
      (hcomm a haQ b hbQ) c (mem_invs4 c (hsq c hc) hc1) (hcomm a haQ c hc)
      (hcomm b hbQ c hc) with h | h | h
    · exact hcn (h ▸ hmem a (by simp))
    · exact hcn (h ▸ hmem b (by simp))
    · exact hcn (h ▸ Subgroup.mul_mem _ (hmem a (by simp)) (hmem b (by simp)))

end S4

section Four

theorem genLE_four_of_ker {S : Type*} [Group S] (hS : IsPGroup 2 S)
    (φ : S →* Equiv.Perm (Fin 4)) (A : Subgroup S) (hA : ∀ B : Subgroup S, B ≤ A → GenLE B 2)
    (hker : φ.ker ≤ A) (H : Subgroup S) : GenLE H 4 := by
  have h1 : GenLE (H ⊓ φ.ker) 2 := hA _ (inf_le_right.trans hker)
  have h2 : GenLE (H.map φ) 2 := by
    apply genLE_two_of_isPGroup_perm4
    intro y
    obtain ⟨h, -, hy⟩ := y.2
    obtain ⟨k, hk⟩ := hS h
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hy, ← map_pow, hk, map_one]
  exact GenLE.of_ker φ H h1 h2

theorem GenLE.map_mulEquiv {S' : Type*} [Group S'] (e : S ≃* S') {B : Subgroup S} {n : ℕ}
    (h : GenLE B n) : GenLE (B.map e.toMonoidHom) n := by
  classical
  obtain ⟨s, hs, hsc⟩ := h
  refine ⟨s.image e, Finset.card_image_le.trans hs, ?_⟩
  have himg : ((s.image e : Finset S') : Set S') = e.toMonoidHom '' (s : Set S) := by
    rw [Finset.coe_image]
    rfl
  rw [himg, ← MonoidHom.map_closure, hsc]

theorem GenLE.conj {B : Subgroup S} {n : ℕ} (h : GenLE B n) (x : S) :
    GenLE (B.map (MulAut.conj x).toMonoidHom) n :=
  GenLE.map_mulEquiv (MulAut.conj x) h

end Four

end CFSG.ClassicalInvolution.Asc77.T7C2
