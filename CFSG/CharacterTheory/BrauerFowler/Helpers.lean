module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

open scoped Pointwise

namespace BrauerFowler.Helpers

private theorem mul_fiber_card_le_centralizer
    {G : Type*} [Group G] [Finite G] [DecidableEq G] (X : Finset G)
    (hinv : ∀ a ∈ X, a⁻¹ = a) (x : G)
    (hne : ((X ×ˢ X).filter fun p : G × G => p.1 * p.2 = x).Nonempty) :
    ((X ×ˢ X).filter fun p : G × G => p.1 * p.2 = x).card ≤
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  let := Fintype.ofFinite G
  let F : Finset (G × G) := (X ×ˢ X).filter fun p : G × G => p.1 * p.2 = x
  let hTfinite : (↑(Subgroup.centralizer ({x} : Set G)) : Set G).Finite :=
    Set.toFinite _
  let T : Finset G := hTfinite.toFinset
  obtain ⟨p₀, hp₀F⟩ := hne
  have hp₀ : p₀.1 * p₀.2 = x := (Finset.mem_filter.mp hp₀F).2
  have hp₀X : p₀.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp hp₀F).1).1
  have hp₀X' : p₀.2 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp hp₀F).1).2
  have hp₀rel : p₀.1 * x = x⁻¹ * p₀.1 ∧ p₀.1 * x⁻¹ = x * p₀.1 :=
    by
      apply And.intro
      · have hsq : p₀.1 * p₀.1 = 1 := by
          calc
            p₀.1 * p₀.1 = p₀.1⁻¹ * p₀.1 := by rw [hinv _ hp₀X]
            _ = 1 := inv_mul_cancel _
        rw [← hp₀, ← mul_assoc, hsq, one_mul, mul_inv_rev,
          hinv _ hp₀X, hinv _ hp₀X', mul_assoc, hsq, mul_one]
      · rw [← hp₀, mul_inv_rev, hinv _ hp₀X, hinv _ hp₀X', mul_assoc]
  have hmaps : Set.MapsTo (fun p : G × G => p₀.1 * p.1) ↑F ↑T := by
    intro p hpF
    have hp : p.1 * p.2 = x := (Finset.mem_filter.mp hpF).2
    have hpX : p.1 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp hpF).1).1
    have hpX' : p.2 ∈ X := (Finset.mem_product.mp (Finset.mem_filter.mp hpF).1).2
    have hprel : p.1 * x = x⁻¹ * p.1 := by
      have hsq : p.1 * p.1 = 1 := by
        calc
          p.1 * p.1 = p.1⁻¹ * p.1 := by rw [hinv _ hpX]
          _ = 1 := inv_mul_cancel _
      rw [← hp, ← mul_assoc, hsq, one_mul, mul_inv_rev,
        hinv _ hpX, hinv _ hpX', mul_assoc, hsq, mul_one]
    have hmem : p₀.1 * p.1 ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (p₀.1 * p.1) * x = p₀.1 * (p.1 * x) := mul_assoc _ _ _
        _ = p₀.1 * (x⁻¹ * p.1) := by rw [hprel]
        _ = (p₀.1 * x⁻¹) * p.1 := (mul_assoc _ _ _).symm
        _ = (x * p₀.1) * p.1 := by rw [hp₀rel.2]
        _ = x * (p₀.1 * p.1) := mul_assoc _ _ _
    simpa [T] using hmem
  have hinj : Set.InjOn (fun p : G × G => p₀.1 * p.1) ↑F := by
    intro p hpF q hqF hpq
    have hp : p.1 * p.2 = x := (Finset.mem_filter.mp hpF).2
    have hq : q.1 * q.2 = x := (Finset.mem_filter.mp hqF).2
    have hfirst : p.1 = q.1 := mul_left_cancel hpq
    apply Prod.ext hfirst
    exact mul_left_cancel (hp.trans (hfirst ▸ hq.symm))
  have hcard := Finset.card_le_card_of_injOn
    (fun p : G × G => p₀.1 * p.1) hmaps hinj
  have hTcard : T.card = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    simpa [T, Nat.card_eq_fintype_card] using hTfinite.card_toFinset
  simpa [F, hTcard] using hcard

theorem exists_centralizer_index_le
    {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (htnc : t ∉ Subgroup.center G) :
    ∃ x : G, x ≠ 1 ∧
      (Subgroup.centralizer ({x} : Set G)).index ≤
        Nat.card (Subgroup.centralizer ({t} : Set G)) ^ 2 +
          Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  classical
  let := Fintype.ofFinite G
  let C := Subgroup.centralizer ({t} : Set G)
  let carrier : Set G := (ConjClasses.mk t).carrier
  let hXfinite : carrier.Finite := Set.toFinite _
  let X : Finset G := hXfinite.toFinset
  let D : Finset (G × G) := X.offDiag
  let prod : G × G → G := fun p => p.1 * p.2
  let I : Finset G := D.image prod
  have hinv : ∀ a ∈ X, a⁻¹ = a := by
    intro a haX
    have haCarrier : a ∈ (ConjClasses.mk t).carrier := by
      simpa [X, carrier] using haX
    have hmk : ConjClasses.mk a = ConjClasses.mk t :=
      ConjClasses.mem_carrier_iff_mk_eq.mp haCarrier
    have hac : IsConj a t := ConjClasses.mk_eq_mk_iff_isConj.mp hmk
    obtain ⟨g, hg⟩ := hac
    apply inv_eq_self_of_orderOf_eq_two
    rw [SemiconjBy.orderOf_eq (↑g : G) hg, ht]
  have htne : t ≠ 1 := by
    intro h
    have : orderOf t = 1 := orderOf_eq_one_iff.mpr h
    omega
  obtain ⟨g, hg⟩ : ∃ g : G, g * t ≠ t * g := by
    simpa only [Subgroup.mem_center_iff, not_forall] using htnc
  let q : G := g * t * g⁻¹
  have hqne : q ≠ t := by
    intro hq
    apply hg
    change g * t * g⁻¹ = t at hq
    calc
      g * t = (g * t * g⁻¹) * g := by simp [mul_assoc]
      _ = t * g := by rw [hq]
  have htX : t ∈ X := by
    simpa [X, carrier] using (ConjClasses.mem_carrier_mk (a := t))
  have hqX : q ∈ X := by
    have htq : IsConj t q := isConj_iff.mpr ⟨g, rfl⟩
    have hmk : ConjClasses.mk q = ConjClasses.mk t :=
      (ConjClasses.mk_eq_mk_iff_isConj.mpr htq).symm
    have : q ∈ (ConjClasses.mk t).carrier :=
      ConjClasses.mem_carrier_iff_mk_eq.mpr hmk
    simpa [X, carrier] using this
  have hDne : D.Nonempty := by
    refine ⟨(t, q), ?_⟩
    exact Finset.mem_offDiag.mpr ⟨htX, hqX, hqne.symm⟩
  have hIne : I.Nonempty := Finset.image_nonempty.mpr hDne
  let fiber : G → ℕ := fun y => (D.filter fun p => prod p = y).card
  obtain ⟨x, hxI, hmax⟩ := Finset.exists_max_image I fiber hIne
  obtain ⟨p₀, hp₀D, hp₀prod⟩ := Finset.mem_image.mp hxI
  have hxne : x ≠ 1 := by
    rw [← hp₀prod]
    intro hp
    have hpMem := Finset.mem_offDiag.mp hp₀D
    apply hpMem.2.2
    have hpeq : p₀.1 = p₀.2⁻¹ := mul_eq_one_iff_eq_inv.mp hp
    simpa [hinv _ hpMem.2.1] using hpeq
  have hmaps : Set.MapsTo prod ↑D ↑I := by
    intro p hp
    exact Finset.mem_image_of_mem prod hp
  have hsum : D.card = ∑ y ∈ I, fiber y := by
    simpa [fiber] using Finset.card_eq_sum_card_fiberwise hmaps
  have hcount_image : D.card ≤ I.card * fiber x := by
    rw [hsum]
    simpa using Finset.sum_le_card_nsmul I fiber (fiber x) hmax
  have hI_sub : I ⊆ (Finset.univ : Finset G).erase 1 := by
    intro y hyI
    obtain ⟨p, hpD, rfl⟩ := Finset.mem_image.mp hyI
    have hpMem := Finset.mem_offDiag.mp hpD
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hp
    apply hpMem.2.2
    have hpeq : p.1 = p.2⁻¹ := mul_eq_one_iff_eq_inv.mp hp
    simpa [hinv _ hpMem.2.1] using hpeq
  have hIcard : I.card ≤ Nat.card G - 1 := by
    calc
      I.card ≤ ((Finset.univ : Finset G).erase 1).card :=
        Finset.card_le_card hI_sub
      _ = Nat.card G - 1 := by simp [Nat.card_eq_fintype_card]
  have hcount : D.card ≤ (Nat.card G - 1) * fiber x :=
    hcount_image.trans (Nat.mul_le_mul_right (fiber x) hIcard)
  have hfiber_eq :
      D.filter (fun p => prod p = x) =
        (X ×ˢ X).filter (fun p : G × G => p.1 * p.2 = x) := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
            ⟨(Finset.mem_offDiag.mp hp'.1).1,
              (Finset.mem_offDiag.mp hp'.1).2.1⟩, hp'.2⟩
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpX : p.1 ∈ X := (Finset.mem_product.mp hp'.1).1
      have hpX' : p.2 ∈ X := (Finset.mem_product.mp hp'.1).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_offDiag.mpr ⟨hpX, hpX', ?_⟩, hp'.2⟩
      intro heq
      apply hxne
      rw [← hp'.2, heq]
      have hsquare : p.2 * p.2 = 1 := by
        calc
          p.2 * p.2 = p.2⁻¹ * p.2 := by rw [hinv _ hpX']
          _ = 1 := inv_mul_cancel _
      exact hsquare
  have hfull_ne :
      ((X ×ˢ X).filter fun p : G × G => p.1 * p.2 = x).Nonempty := by
    rw [← hfiber_eq]
    exact ⟨p₀, Finset.mem_filter.mpr ⟨hp₀D, hp₀prod⟩⟩
  have hfiber_le : fiber x ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    change (D.filter (fun p => prod p = x)).card ≤ _
    rw [hfiber_eq]
    exact mul_fiber_card_le_centralizer X hinv x hfull_ne
  let m := Nat.card ↑(ConjClasses.mk t).carrier
  let c := Nat.card C
  let z := Nat.card (Subgroup.centralizer ({x} : Set G))
  let k := (Subgroup.centralizer ({x} : Set G)).index
  have hXcard : X.card = m := by
    simpa [X, carrier, m, Nat.card_eq_fintype_card] using hXfinite.card_toFinset
  have hm2 : 2 ≤ m := by
    have : 1 < X.card :=
      Finset.one_lt_card.mpr ⟨t, htX, q, hqX, hqne.symm⟩
    omega
  have hmc : m * c = Nat.card G := by
    simpa [m, c, C] using BenderSuzuki.External.huppert_XI_6_6_class_card_mul_centralizer_card t
  have hzpos : 0 < z := Nat.card_pos
  have hmpos : 0 < m := by omega
  have hDcard : D.card = m * (m - 1) := by
    change X.offDiag.card = _
    rw [Finset.offDiag_card, hXcard]
    symm
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hbasic : m * (m - 1) ≤ (Nat.card G - 1) * fiber x := by
    rw [hDcard] at hcount
    exact hcount
  have hcancel : m - 1 ≤ c * z := by
    apply (Nat.mul_le_mul_left_iff hmpos).mp
    calc
      m * (m - 1) ≤ (Nat.card G - 1) * fiber x := hbasic
      _ ≤ Nat.card G * z := Nat.mul_le_mul (Nat.sub_le _ _) hfiber_le
      _ = m * (c * z) := by rw [← hmc]; ring
  have hm_bound : m ≤ c * z + 1 := by omega
  have hkz : k * z = Nat.card G := by
    simpa [k, z] using
      (Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G)))
  have hc_le_cz : c ≤ c * z := by
    have := Nat.mul_le_mul_left c (Nat.succ_le_iff.mpr hzpos)
    simpa using this
  have hproduct_bound : m * c ≤ (c * c + c) * z := by
    calc
      m * c ≤ (c * z + 1) * c := Nat.mul_le_mul_right c hm_bound
      _ = c * c * z + c := by ring
      _ ≤ c * c * z + c * z := Nat.add_le_add_left hc_le_cz _
      _ = (c * c + c) * z := by ring
  refine ⟨x, hxne, ?_⟩
  change k ≤ c ^ 2 + c
  apply (Nat.mul_le_mul_right_iff hzpos).mp
  rw [hkz, ← hmc]
  simpa [pow_two] using hproduct_bound

theorem natCard_le_factorial_index_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  let rho := MulAction.toPermHom G (G ⧸ H)
  have hcore : H.normalCore = ⊥ := by
    rcases (haveI := (Subgroup.normalCore_normal H); IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore) with h | h
    · exact h
    · exfalso
      apply hH
      apply top_unique
      rw [← h]
      exact Subgroup.normalCore_le H
  have hker : rho.ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker]
    exact hcore
  have hinj : Function.Injective rho :=
    (MonoidHom.ker_eq_bot_iff rho).mp hker
  have hcard := Nat.card_le_card_of_injective rho hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card] at hcard
  exact hcard

end BrauerFowler.Helpers

end CFSG
