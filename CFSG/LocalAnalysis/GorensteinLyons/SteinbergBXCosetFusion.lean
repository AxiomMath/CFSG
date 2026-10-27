module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Group.ConjFinite
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise

theorem prod_eq_one_of_mul_mem {E : Type*} [CommGroup E] [DecidableEq E]
    (hE : ∀ x : E, x * x = 1) {g h : E} (hg : g ≠ 1) (hh : h ≠ 1) (hgh : g ≠ h) :
    ∀ T : Finset E, (∀ x ∈ T, x * g ∈ T ∧ x * h ∈ T) → ∏ x ∈ T, x = 1 := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact Finset.prod_empty
    have hxg := (hT x hx).1
    have hxh := (hT x hx).2
    have hxgh := (hT _ hxg).2
    set B : Finset E := {x, x * g, x * h, x * g * h} with hB
    have hBT : B ⊆ T := by
      intro y hy
      simp only [hB, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    have hgg := hE g
    have hhh := hE h
    have h1 : x ≠ x * g := fun e => hg (by simpa using e.symm)
    have h2 : x ≠ x * h := fun e => hh (by simpa using e.symm)
    have h3 : x ≠ x * g * h := fun e => hgh (by
      have : g * h = 1 := by
        have := congrArg (x⁻¹ * ·) e
        simpa [mul_assoc] using this.symm
      calc g = g * (h * h) := by rw [hhh, mul_one]
        _ = (g * h) * h := by rw [mul_assoc]
        _ = h := by rw [this, one_mul])
    have h4 : x * g ≠ x * h := fun e => hgh (mul_left_cancel e)
    have h5 : x * g ≠ x * g * h := fun e => hh (by simpa using e.symm)
    have h6 : x * h ≠ x * g * h := fun e => hg (by
      have e' : h = g * h := mul_left_cancel (e.trans (mul_assoc x g h))
      exact mul_right_cancel (e'.symm.trans (one_mul h).symm))
    have hBprod : ∏ y ∈ B, y = 1 := by
      rw [hB, Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]),
        Finset.prod_insert (by simp [h6]), Finset.prod_singleton]
      calc x * (x * g * (x * h * (x * g * h))) = (x * x) * (x * x) * (g * g) * (h * h) := by
            simp only [mul_left_comm, mul_comm]
        _ = 1 := by rw [hE x, hgg, hhh]; simp
    have hTB : ∀ y ∈ T \ B, y * g ∈ T \ B ∧ y * h ∈ T \ B := by
      intro y hy
      rw [Finset.mem_sdiff] at hy
      have hyB : ∀ k : E, k * k = 1 → (∀ b ∈ B, b * k ∈ B) → y * k ∉ B := by
        intro k hk hBk hyk
        apply hy.2
        have := hBk _ hyk
        rwa [mul_assoc, hk, mul_one] at this
      have hBg : ∀ b ∈ B, b * g ∈ B := by
        intro b hb
        simp only [hB, Finset.mem_insert, Finset.mem_singleton] at hb ⊢
        rcases hb with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (by rw [mul_assoc, hgg, mul_one])
        · exact Or.inr (Or.inr (Or.inr (mul_right_comm x h g)))
        · exact Or.inr (Or.inr (Or.inl (by
            rw [mul_right_comm (x * g) h g, mul_assoc x g g, hgg, mul_one])))
      have hBh : ∀ b ∈ B, b * h ∈ B := by
        intro b hb
        simp only [hB, Finset.mem_insert, Finset.mem_singleton] at hb ⊢
        rcases hb with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inl (by rw [mul_assoc, hhh, mul_one])
        · exact Or.inr (Or.inl (by rw [mul_assoc (x * g) h h, hhh, mul_one]))
      exact ⟨Finset.mem_sdiff.mpr ⟨(hT y hy.1).1, hyB g hgg hBg⟩,
        Finset.mem_sdiff.mpr ⟨(hT y hy.1).2, hyB h hhh hBh⟩⟩
    rw [← Finset.prod_sdiff hBT, ih (T \ B) (Finset.sdiff_ssubset hBT ⟨x, by simp [hB]⟩) hTB,
      hBprod, one_mul]

variable {G : Type*} [Group G]

theorem class_two_involution_coset_fusion_product [Finite G] {Q : Subgroup G}
    (_hQ : IsPGroup 2 Q) {c : G} (hcQ : c ∈ Q) (hZ : (center Q).map Q.subtype = zpowers c)
    (hc4 : orderOf c = 4) (hQ' : ⁅Q, Q⁆ ≤ zpowers (c ^ 2)) {a : G}
    (_haNQ : a ∈ normalizer (Q : Set G))
    (haQ : a ∉ Q) (ha2 : orderOf a = 2) (hca : a⁻¹ * c * a = c⁻¹) {P D F E : Subgroup G}
    (hPdef : P = Q ⊓ centralizer {a}) (hDdef : D = closure {x | ∃ q ∈ Q, x = q⁻¹ * a⁻¹ * q * a})
    (hFdef : F = D ⊓ P) (hEdef : E = P ⊔ zpowers a) (hP : CFSG.IsElementaryAbelian 2 P)
    (_hDZP : D ≤ (center Q).map Q.subtype ⊔ P)
    (haQD : (fun q => q⁻¹ * a * q) '' (Q : Set G) = a • (D : Set G)) (hF4 : 4 ≤ Nat.card F)
    (hzG : ∀ x ∈ Q, IsConj (c ^ 2) x ↔ x = c ^ 2) :
    CFSG.IsElementaryAbelian 2 E ∧ P ⊓ zpowers a = ⊥ ∧
      (∀ p ∈ P, (fun q => q⁻¹ * (a * p) * q) ''
          ((Q ⊓ normalizer (E : Set G) : Subgroup G) : Set G) = (a * p) • (F : Set G)) ∧
      (∀ l : List G, l.Nodup → (∀ x, x ∈ l ↔ x ∈ E ∧ IsConj (c ^ 2) x) → l.prod = c ^ 2) ∧
      normalizer (E : Set G) ≤ centralizer {c ^ 2} := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set z := c ^ 2 with hzdef
  have hcZ : ∀ y ∈ Q, y * c = c * y := by
    intro y hy
    have : c ∈ (center Q).map Q.subtype := hZ ▸ mem_zpowers c
    obtain ⟨⟨c', hc'⟩, hcen, rfl⟩ := this
    exact congrArg Subtype.val (mem_center_iff.mp hcen ⟨y, hy⟩)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by
    rw [← pow_two, ← ha2, pow_orderOf_eq_one])
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hcc : c⁻¹ * c⁻¹ = z := by
    rw [hzdef, ← mul_inv_rev, ← pow_two, eq_comm, ← mul_eq_one_iff_eq_inv]
    rw [← pow_add, show 2 + 2 = orderOf c by rw [hc4], pow_orderOf_eq_one]
  have hzz : z * z = 1 := by
    rw [hzdef, ← pow_add, show 2 + 2 = orderOf c by rw [hc4], pow_orderOf_eq_one]
  have hzQ : z ∈ Q := pow_mem hcQ 2
  have hza : a * z = z * a := by
    have h1 : a⁻¹ * z * a = z := by
      calc a⁻¹ * z * a = (a⁻¹ * c * a) * (a⁻¹ * c * a) := by rw [hzdef, pow_two]; group
        _ = c⁻¹ * c⁻¹ := by rw [hca]
        _ = z := hcc
    calc a * z = a * (a⁻¹ * z * a) := by rw [h1]
      _ = z * a := by group
  have hzP : z ∈ P := by
    rw [hPdef, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨hzQ, hza.symm⟩
  have hPQ : P ≤ Q := hPdef ▸ inf_le_left
  have hPa : ∀ p ∈ P, a * p = p * a := by
    intro p hp
    rw [hPdef, mem_inf, mem_centralizer_singleton_iff] at hp
    exact hp.2.symm
  have hPcomm : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p := fun p hp p' hp' =>
    congrArg Subtype.val (hP.is_comm.comm ⟨p, hp⟩ ⟨p', hp'⟩)
  have hPsq : ∀ p ∈ P, p * p = 1 := fun p hp => by
    rw [← pow_two]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := P) p hp
  have hzpow : ∀ x ∈ zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    have hz1 : z ^ 2 = 1 := by rw [pow_two, hzz]
    rw [← zpow_mod_orderOf]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz1) with h | h
    · left; rw [orderOf_eq_one_iff.mp h, one_zpow]
    · rw [h]
      rcases Int.emod_two_eq_zero_or_one m with h' | h'
      · left; rw [Nat.cast_ofNat, h', zpow_zero]
      · right; rw [Nat.cast_ofNat, h', zpow_one]
  have hwP : ∀ w : G, (w = 1 ∨ w = z) → w ∈ P := by
    rintro w (rfl | rfl)
    · exact one_mem _
    · exact hzP
  have hconjP : ∀ q ∈ Q, ∀ p ∈ P, ∃ w : G, (w = 1 ∨ w = z) ∧ q⁻¹ * p * q = p * w := by
    intro q hq p hp
    have hw := hzpow _ (hQ' (commutator_mem_commutator (inv_mem (hPQ hp)) (inv_mem hq)))
    refine ⟨⁅p⁻¹, q⁻¹⁆, hw, ?_⟩
    rw [commutatorElement_def]
    group
  have hPnorm : ∀ q ∈ Q, ∀ p ∈ P, q⁻¹ * p * q ∈ P := by
    intro q hq p hp
    obtain ⟨w, hw, hpw⟩ := hconjP q hq p hp
    rw [hpw]
    exact mul_mem hp (hwP w hw)
  have haax : ∀ x : G, a * (a * x) = x := fun x => by rw [← mul_assoc, haa, one_mul]
  let E' : Subgroup G :=
    { carrier := {x | x ∈ P ∨ a * x ∈ P}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · right
          rw [← mul_assoc, hPa x hx, mul_assoc]
          exact mul_mem hx hy
        · right
          rw [← mul_assoc]
          exact mul_mem hx hy
        · left
          have : x * y = (a * x) * (a * y) := by
            calc x * y = a * (a * x) * y := by rw [haax]
              _ = (a * x) * a * y := by rw [hPa _ hx]
              _ = (a * x) * (a * y) := by rw [mul_assoc]
          rw [this]
          exact mul_mem hx hy
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · right
          have : a * x⁻¹ = (a * x)⁻¹ := by
            calc a * x⁻¹ = a * (a * (a * x))⁻¹ := by rw [haax]
              _ = a * ((a * x)⁻¹ * a) := by rw [mul_inv_rev, hainv]
              _ = a * (a * (a * x)⁻¹) := by rw [← hPa _ (inv_mem hx)]
              _ = (a * x)⁻¹ := haax _
          rw [this]
          exact inv_mem hx }
  have haP : a ∉ P := fun h => haQ (hPQ h)
  have hEmem : ∀ x, x ∈ E ↔ x ∈ P ∨ a * x ∈ P := by
    have hEE' : E = E' := by
      apply le_antisymm
      · rw [hEdef, sup_le_iff, zpowers_le]
        exact ⟨fun x hx => Or.inl hx, Or.inr (by rw [haa]; exact one_mem _)⟩
      · rintro x (hx | hx)
        · exact hEdef ▸ mem_sup_left hx
        · rw [← haax x]
          exact mul_mem (hEdef ▸ mem_sup_right (mem_zpowers a)) (hEdef ▸ mem_sup_left hx)
    intro x
    rw [hEE']
    rfl
  have hEclos : E = closure ((P : Set G) ∪ {a}) := by
    rw [hEdef, Subgroup.closure_union, Subgroup.closure_eq, zpowers_eq_closure]
  have hEMC : IsMulCommutative E := by
    rw [hEclos]
    refine isMulCommutative_closure ?_
    rintro x (hx | hx) y (hy | hy) -
    · exact hPcomm x hx y hy
    · rw [Set.mem_singleton_iff.mp hy]; exact (hPa x hx).symm
    · rw [Set.mem_singleton_iff.mp hx]; exact hPa y hy
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEMC.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    rcases (hEmem x).mp hx with hx | hx
    · exact hPsq x hx
    · calc x * x = a * (a * x) * (a * (a * x)) := by rw [haax]
        _ = (a * a) * ((a * x) * (a * x)) := by
          rw [mul_assoc a, ← mul_assoc (a * x) a, ← hPa _ hx]; group
        _ = 1 := by rw [haa, hPsq _ hx, one_mul]
  have hEA : CFSG.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEMC
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (by rw [SubgroupClass.coe_pow, pow_two, hEsq x x.2, OneMemClass.coe_one]) }
  have hPinf : P ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxa⟩ := mem_inf.mp hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxa
    rw [mem_bot, ← zpow_mod_orderOf, ha2]
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · rw [Nat.cast_ofNat, h, zpow_zero]
    · rw [← zpow_mod_orderOf, ha2, Nat.cast_ofNat, h, zpow_one] at hxP
      exact absurd hxP haP
  have hDgen : ∀ q ∈ Q, q⁻¹ * a⁻¹ * q * a ∈ D := fun q hq =>
    hDdef ▸ subset_closure ⟨q, hq, rfl⟩
  have hcommD : ∀ q ∈ Q, a * (q⁻¹ * a * q) ∈ D := by
    intro q hq
    have h := inv_mem (hDgen q hq)
    rwa [show (q⁻¹ * a⁻¹ * q * a)⁻¹ = a⁻¹ * (q⁻¹ * a * q) by group, hainv] at h
  have hzD : z ∈ D := by
    have h := hDgen c hcQ
    rwa [show c⁻¹ * a⁻¹ * c * a = c⁻¹ * (a⁻¹ * c * a) by group, hca, hcc] at h
  have hwF : ∀ w : G, (w = 1 ∨ w = z) → w ∈ F := by
    rintro w (rfl | rfl)
    · exact one_mem _
    · rw [hFdef]; exact mem_inf.mpr ⟨hzD, hzP⟩
  have hconjE : ∀ q ∈ Q, a * (q⁻¹ * a * q) ∈ P → ∀ x ∈ E, q⁻¹ * x * q ∈ E := by
    intro q hq hf x hx
    rcases (hEmem x).mp hx with hx | hx
    · exact (hEmem _).mpr (Or.inl (hPnorm q hq x hx))
    · refine (hEmem _).mpr (Or.inr ?_)
      have : a * (q⁻¹ * x * q) = (a * (q⁻¹ * a * q)) * (q⁻¹ * (a * x) * q) := by
        conv_lhs => rw [← haax x]
        group
      rw [this]
      exact mul_mem hf (hPnorm q hq _ hx)
  have hNE : ∀ q ∈ Q, q ∈ normalizer (E : Set G) ↔ a * (q⁻¹ * a * q) ∈ P := by
    intro q hq
    constructor
    · intro hqN
      have haE : a ∈ E := hEdef ▸ mem_sup_right (mem_zpowers a)
      rcases (hEmem _).mp ((mem_normalizer_iff''.mp hqN a).mp haE) with h | h
      · exact absurd (by
          have := mul_mem (mul_mem hq (hPQ h)) (inv_mem hq)
          rwa [show q * (q⁻¹ * a * q) * q⁻¹ = a by group] at this) haQ
      · exact h
    · intro hf
      set f₀ := a * (q⁻¹ * a * q) with hf₀
      have hqa : q⁻¹ * a * q = a * f₀ := (haax _).symm
      have hqa' : a * (q⁻¹⁻¹ * a * q⁻¹) ∈ P := by
        have h1 : q * a * q⁻¹ = a * (q * f₀⁻¹ * q⁻¹) := by
          have h2 : a = q * (a * f₀) * q⁻¹ := by rw [← hqa]; group
          calc q * a * q⁻¹ = (q * (a * f₀) * q⁻¹) * (q * f₀⁻¹ * q⁻¹) := by group
            _ = a * (q * f₀⁻¹ * q⁻¹) := by rw [← h2]
        rw [inv_inv, h1, haax]
        have := hPnorm q⁻¹ (inv_mem hq) f₀⁻¹ (inv_mem hf)
        rwa [inv_inv] at this
      refine mem_normalizer_iff''.mpr fun x => ⟨hconjE q hq hf x, fun hx => ?_⟩
      have := hconjE q⁻¹ (inv_mem hq) hqa' _ hx
      rwa [show q⁻¹⁻¹ * (q⁻¹ * x * q) * q⁻¹ = x by group] at this
  have hconj_ap : ∀ q ∈ Q, ∀ p ∈ P, a * (q⁻¹ * a * q) ∈ P → ∃ w : G, (w = 1 ∨ w = z) ∧
      q⁻¹ * (a * p) * q = (a * p) * ((a * (q⁻¹ * a * q)) * w) := by
    intro q hq p hp hf
    obtain ⟨w, hw, hpw⟩ := hconjP q hq p hp
    refine ⟨w, hw, ?_⟩
    set f₀ := a * (q⁻¹ * a * q) with hf₀
    calc q⁻¹ * (a * p) * q = (q⁻¹ * a * q) * (q⁻¹ * p * q) := by group
      _ = (a * f₀) * (p * w) := by rw [hpw, ← haax (q⁻¹ * a * q)]
      _ = (a * p) * (f₀ * w) := by
        rw [mul_assoc a f₀, ← mul_assoc f₀ p w, hPcomm f₀ hf p hp]
        group
  have hcac : c⁻¹ * a * c = a * z := by
    have h1 : c⁻¹ * a = a * c := by
      have : a⁻¹ * c⁻¹ * a = c := by
        rw [show a⁻¹ * c⁻¹ * a = (a⁻¹ * c * a)⁻¹ by group, hca, inv_inv]
      calc c⁻¹ * a = a * (a⁻¹ * c⁻¹ * a) := by group
        _ = a * c := by rw [this]
    rw [h1, mul_assoc, hzdef, pow_two]
  have hcN : c ∈ Q ⊓ normalizer (E : Set G) := by
    refine mem_inf.mpr ⟨hcQ, (hNE c hcQ).mpr ?_⟩
    rw [hcac, haax]
    exact hzP
  have hcx : ∀ x, a * x ∈ P → c⁻¹ * x * c = x * z := by
    intro x hx
    have h1 : c⁻¹ * (a * x) * c = a * x := by
      rw [mul_assoc, hcZ _ (hPQ hx), ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * x * c = (c⁻¹ * a * c) * (c⁻¹ * (a * x) * c) := by
          conv_lhs => rw [← haax x]
          group
      _ = x * z := by
        rw [h1, hcac, mul_assoc, hPcomm z hzP _ hx, ← mul_assoc, haax]
  have horbit : ∀ p ∈ P, (fun q => q⁻¹ * (a * p) * q) ''
      ((Q ⊓ normalizer (E : Set G) : Subgroup G) : Set G) = (a * p) • (F : Set G) := by
    intro p hp
    ext x
    rw [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqQ, hqN⟩ := mem_inf.mp hq
      have hf := (hNE q hqQ).mp hqN
      obtain ⟨w, hw, h⟩ := hconj_ap q hqQ p hp hf
      refine ⟨(a * (q⁻¹ * a * q)) * w, ?_, h.symm⟩
      rw [hFdef]
      refine mul_mem (mem_inf.mpr ⟨hcommD q hqQ, hf⟩) ?_
      have := hwF w hw
      rwa [hFdef] at this
    · rintro ⟨f, hf, rfl⟩
      have hf' := hf
      rw [hFdef] at hf'
      obtain ⟨hfD, hfP⟩ := mem_inf.mp hf'
      have : a * f ∈ (fun q => q⁻¹ * a * q) '' (Q : Set G) := by
        rw [haQD]
        exact Set.smul_mem_smul_set hfD
      obtain ⟨q, hqQ, hq⟩ := this
      have hq' : a * (q⁻¹ * a * q) = f := by
        rw [show q⁻¹ * a * q = a * f from hq, haax]
      have hqN : q ∈ Q ⊓ normalizer (E : Set G) := mem_inf.mpr ⟨hqQ, (hNE q hqQ).mpr (hq' ▸ hfP)⟩
      obtain ⟨w, hw, h⟩ := hconj_ap q hqQ p hp (hq' ▸ hfP)
      rw [hq'] at h
      rcases hw with rfl | rfl
      · exact ⟨q, hqN, by rw [h, mul_one]; rfl⟩
      · refine ⟨q * c, mul_mem hqN hcN, ?_⟩
        have hx : a * (a * p * (f * z)) ∈ P := by
          rw [mul_assoc a p, haax]
          exact mul_mem hp (mul_mem hfP hzP)
        change (q * c)⁻¹ * (a * p) * (q * c) = a * p * f
        calc (q * c)⁻¹ * (a * p) * (q * c) = c⁻¹ * (q⁻¹ * (a * p) * q) * c := by group
          _ = a * p * (f * z) * z := by rw [h, hcx _ hx]
          _ = a * p * f := by rw [mul_assoc (a * p) (f * z) z, mul_assoc f z z, hzz, mul_one]
  have hzE : z ∈ E := hEdef ▸ mem_sup_left hzP
  have hFE : F ≤ E := fun x hx => hEdef ▸ mem_sup_left (mem_inf.mp (hFdef ▸ hx)).2
  have := hEMC
  have hE2 : ∀ x : E, x * x = 1 := fun x => Subtype.ext (by
    rw [coe_mul, hEsq x x.2, OneMemClass.coe_one])
  have hprod : ∏ x ∈ (Finset.univ.filter fun x : E => IsConj z (x : G)), x = ⟨z, hzE⟩ := by
    set S := Finset.univ.filter fun x : E => IsConj z (x : G) with hS
    have hzS : (⟨z, hzE⟩ : E) ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, IsConj.refl z⟩
    rw [← Finset.mul_prod_erase S (fun x => x) hzS]
    have hcardF : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hF4
    obtain ⟨g, hg⟩ : ((Finset.univ : Finset F).erase 1).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
      omega
    obtain ⟨h, hh⟩ : (((Finset.univ : Finset F).erase 1).erase g).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hg,
        Finset.card_erase_of_mem (Finset.mem_univ _)]
      omega
    have hg1 : g ≠ 1 := (Finset.mem_erase.mp hg).1
    have hhg : h ≠ g := (Finset.mem_erase.mp hh).1
    have hh1 : h ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hh).2).1
    let g' : E := ⟨g, hFE g.2⟩
    let h' : E := ⟨h, hFE h.2⟩
    have hg1' : g' ≠ 1 := by
      intro e
      apply hg1
      ext
      simpa [g'] using congrArg Subtype.val e
    have hh1' : h' ≠ 1 := by
      intro e
      apply hh1
      ext
      simpa [h'] using congrArg Subtype.val e
    have hgh' : g' ≠ h' := by
      intro e
      apply hhg
      ext
      simpa [g', h'] using (congrArg Subtype.val e).symm
    have hTinv : ∀ x ∈ S.erase ⟨z, hzE⟩, ∀ f : F, x * ⟨f, hFE f.2⟩ ∈ S.erase ⟨z, hzE⟩ := by
      intro x hx f
      obtain ⟨hxz, hxS⟩ := Finset.mem_erase.mp hx
      rw [hS, Finset.mem_filter] at hxS
      have hxz' : (x : G) ≠ z := fun e => hxz (Subtype.ext e)
      have hxP : (x : G) ∉ P := fun hxP => hxz' ((hzG _ (hPQ hxP)).mp hxS.2)
      have hax : a * (x : G) ∈ P := ((hEmem _).mp x.2).resolve_left hxP
      have hmem : (x : G) * f ∈ (a * (a * x)) • (F : Set G) := by
        rw [haax]
        exact Set.smul_mem_smul_set f.2
      rw [← horbit _ hax] at hmem
      obtain ⟨q, -, hq⟩ := hmem
      simp only [haax] at hq
      refine Finset.mem_erase.mpr ⟨fun e => hxP ?_, ?_⟩
      · have h1 : (x : G) * f = z := congrArg Subtype.val e
        have h2 : (x : G) = z * (f : G)⁻¹ := by rw [← h1, mul_inv_cancel_right]
        rw [h2]
        have hFP : F ≤ P := hFdef ▸ inf_le_right
        have hfP : (f : G) ∈ P := hFP f.2
        exact mul_mem hzP (inv_mem hfP)
      · rw [hS, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hxS.2.trans ?_⟩
        rw [isConj_iff]
        exact ⟨q⁻¹, by rw [inv_inv, hq]; rfl⟩
    rw [prod_eq_one_of_mul_mem hE2 hg1' hh1' hgh' _ fun x hx => ⟨hTinv x hx g, hTinv x hx h⟩,
      mul_one]
  have hlist : ∀ l : List G, l.Nodup → (∀ x, x ∈ l ↔ x ∈ E ∧ IsConj z x) → l.prod = z := by
    intro l hl hmem
    have hlE : ∀ x ∈ l, x ∈ E := fun x hx => ((hmem x).mp hx).1
    set l' : List E := l.pmap (fun x hx => ⟨x, hx⟩) hlE with hl'
    have hl'nd : l'.Nodup := hl.pmap fun x _ y _ h => congrArg Subtype.val h
    have hl'eq : l'.map Subtype.val = l := by rw [hl', List.map_pmap]; simp
    have hfin : l'.toFinset = Finset.univ.filter fun x : E => IsConj z (x : G) := by
      ext x
      rw [List.mem_toFinset, Finset.mem_filter, hl', List.mem_pmap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Finset.mem_univ _, ((hmem y).mp hy).2⟩
      · rintro ⟨-, hx⟩
        exact ⟨x, (hmem x).mpr ⟨x.2, hx⟩, rfl⟩
    have := List.prod_toFinset (fun x => x) hl'nd
    rw [hfin, hprod, List.map_id'] at this
    calc l.prod = (l'.map Subtype.val).prod := by rw [hl'eq]
      _ = ((l'.prod : E) : G) := (Subgroup.val_list_prod E l').symm
      _ = z := by rw [← this]
  refine ⟨hEA, hPinf, horbit, hlist, fun g hg => ?_⟩
  set L : List G := (Finset.univ.filter fun x : G => x ∈ E ∧ IsConj z x).toList with hL
  have hLnd : L.Nodup := Finset.nodup_toList _
  have hLmem : ∀ x, x ∈ L ↔ x ∈ E ∧ IsConj z x := fun x => by
    rw [hL, Finset.mem_toList, Finset.mem_filter]
    simp
  have hL' : (L.map (MulAut.conj g)).prod = z := by
    refine hlist _ (hLnd.map (MulAut.conj g).injective) fun x => ?_
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyE, hyz⟩ := (hLmem y).mp hy
      refine ⟨(mem_normalizer_iff.mp hg y).mp hyE, hyz.trans ?_⟩
      exact isConj_iff.mpr ⟨g, rfl⟩
    · rintro ⟨hxE, hxz⟩
      refine ⟨g⁻¹ * x * g, (hLmem _).mpr ⟨?_, hxz.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩,
        by simp only [MulAut.conj_apply]; group⟩
      exact (mem_normalizer_iff''.mp hg x).mp hxE
  rw [← map_list_prod, hlist L hLnd hLmem, MulAut.conj_apply] at hL'
  rw [mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hL']

end CFSG.LocalAnalysis.GorensteinLyons
