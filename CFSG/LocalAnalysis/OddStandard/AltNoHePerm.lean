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
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.OddStandard.AltNoHe

open Subgroup Equiv Equiv.Perm Equiv.Perm.OnCycleFactors

section Involution

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_support_eq_two_of_mem_cycleFactorsFinset {g : Perm α} (hg : g * g = 1)
    {c : Perm α} (hc : c ∈ g.cycleFactorsFinset) : c.support.card = 2 := by
  obtain ⟨hcyc, hcg⟩ := mem_cycleFactorsFinset_iff.1 hc
  have hsq : c ^ 2 = 1 := by
    ext x
    by_cases hx : x ∈ c.support
    · have hcx : c x ∈ c.support := apply_mem_support.2 hx
      rw [sq, mul_apply, hcg _ hcx, hcg _ hx]
      exact DFunLike.congr_fun hg x
    · rw [sq, mul_apply, notMem_support.1 hx, notMem_support.1 hx]
      rfl
  have h2 : orderOf c = 2 := orderOf_eq_prime hsq hcyc.ne_one
  rw [← hcyc.orderOf, h2]

theorem apply_eq_or_apply_eq_of_mem_ker {g : Perm α} (hg : g * g = 1) (k : centralizer {g})
    (hk : k ∈ (toPermHom g).ker) (hfix : ∀ x, g x = x → (k : Perm α) x = x) (x : α) :
    (k : Perm α) x = x ∨ (k : Perm α) x = g x := by
  by_cases hx : g x = x
  · exact Or.inl (hfix x hx)
  · have hxs : x ∈ g.support := mem_support.2 hx
    have hc : g.cycleOf x ∈ g.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hxs
    have hcomm := (mem_ker_toPermHom_iff g k).1 hk _ hc
    have hcx : g.cycleOf x x = g x := cycleOf_apply_self g x
    have hcne : g.cycleOf x x ≠ x := by rw [hcx]; exact hx
    have hkx : (k : Perm α) x ∈ (g.cycleOf x).support := by
      rw [mem_support]
      intro h
      have h1 : g.cycleOf x ((k : Perm α) x) = (k : Perm α) (g.cycleOf x x) :=
        (DFunLike.congr_fun hcomm.eq x).symm
      rw [h] at h1
      exact hcne ((k : Perm α).injective h1).symm
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1
      (card_support_eq_two_of_mem_cycleFactorsFinset hg hc)
    have hxs' : x ∈ (g.cycleOf x).support := mem_support.2 hcne
    have hcxs : g.cycleOf x x ∈ (g.cycleOf x).support := apply_mem_support.2 hxs'
    rw [hs, Finset.mem_insert, Finset.mem_singleton] at hxs' hcxs hkx
    rw [← hcx]
    grind

omit [Fintype α] [DecidableEq α] in
theorem mul_comm_of_apply_eq_or_apply_eq {g : Perm α} (hg : g * g = 1) {a b : Perm α}
    (ha : a * g = g * a) (hb : b * g = g * b) (ha' : ∀ x, a x = x ∨ a x = g x)
    (hb' : ∀ x, b x = x ∨ b x = g x) : a * b = b * a := by
  have hag : ∀ y, a (g y) = g (a y) := fun y => DFunLike.congr_fun ha y
  have hbg : ∀ y, b (g y) = g (b y) := fun y => DFunLike.congr_fun hb y
  have hgg : ∀ y, g (g y) = y := fun y => DFunLike.congr_fun hg y
  ext x
  simp only [mul_apply]
  rcases ha' x with h1 | h1 <;> rcases hb' x with h2 | h2 <;> simp [h1, h2, hag, hbg, hgg]

def fixHom (g : Perm α) : centralizer {g} →* Perm (Function.fixedPoints g) where
  toFun k := (k : Perm α).subtypePerm fun _ => apply_mem_fixedPoints_iff_mem_of_mem_centralizer k.2
  map_one' := by ext; rfl
  map_mul' k l := (subtypePerm_mul _ _ _ _).symm

omit [Fintype α] in
theorem fixHom_surjective (g : Perm α) : Function.Surjective (fixHom g) := fun u =>
  ⟨⟨ofSubtype u, mem_centralizer_singleton_iff.2
    (disjoint_ofSubtype_of_memFixedPoints_self u).commute⟩, subtypePerm_ofSubtype u⟩

theorem toPermHom_surjective {g : Perm α} (hg : g * g = 1) :
    Function.Surjective (toPermHom g) := fun σ => by
  have : σ ∈ (toPermHom g).range := by
    rw [mem_range_toPermHom_iff]
    intro c
    rw [card_support_eq_two_of_mem_cycleFactorsFinset hg (σ c).2,
      card_support_eq_two_of_mem_cycleFactorsFinset hg c.2]
  exact this

theorem exists_even_adjust {g : Perm α} (hg1 : g ≠ 1) (hg2 : g * g = 1) (k : centralizer {g}) :
    ∃ k' : centralizer {g}, (k' : Perm α) ∈ alternatingGroup α ∧
      toPermHom g k' = toPermHom g k ∧ fixHom g k' = fixHom g k := by
  by_cases hs : sign (k : Perm α) = 1
  · exact ⟨k, mem_alternatingGroup.2 hs, rfl, rfl⟩
  · obtain ⟨c, hc⟩ : g.cycleFactorsFinset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun h => hg1 (cycleFactorsFinset_eq_empty_iff.1 h)
    have hcc : c ∈ centralizer {g} :=
      mem_centralizer_singleton_iff.2 (self_mem_cycle_factors_commute hc).eq
    refine ⟨k * ⟨c, hcc⟩, ?_, ?_, ?_⟩
    · have hsc : sign c = -1 := by
        rw [(mem_cycleFactorsFinset_iff.1 hc).1.sign,
          card_support_eq_two_of_mem_cycleFactorsFinset hg2 hc]
        simp
      have hsk : sign (k : Perm α) = -1 := by
        rcases Int.units_eq_one_or (sign (k : Perm α)) with h | h
        · exact absurd h hs
        · exact h
      rw [mem_alternatingGroup]
      change sign ((k : Perm α) * c) = 1
      rw [map_mul, hsc, hsk]
      rfl
    · have : toPermHom g ⟨c, hcc⟩ = 1 := by
        rw [← MonoidHom.mem_ker, mem_ker_toPermHom_iff]
        intro d hd
        exact cycleFactorsFinset_mem_commute' g hc hd
      rw [map_mul, this, mul_one]
    · have : fixHom g ⟨c, hcc⟩ = 1 := by
        ext ⟨x, hx⟩
        have hcx : c x = x := by
          by_contra hne
          have := (mem_cycleFactorsFinset_iff.1 hc).2 x (mem_support.2 hne)
          exact hne (this.trans hx)
        exact hcx
      rw [map_mul, this, mul_one]

section Hom

variable {G : Type*} [Group G] (ε : G →* Perm α)

def centHom (t : G) : centralizer {t} →* centralizer {ε t} :=
  (ε.comp (centralizer {t}).subtype).codRestrict (centralizer {ε t}) fun c => by
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 c.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, this]

def quotP (t : G) : centralizer {t} →* Perm (ε t).cycleFactorsFinset :=
  (toPermHom (ε t)).comp (centHom ε t)

def quotF (t : G) : centralizer {t} →* Perm (Function.fixedPoints (ε t)) :=
  (fixHom (ε t)).comp (centHom ε t)

variable {ε}

omit [Fintype α] [DecidableEq α] in
theorem mem_centralizer_of_eq {t x : G} (hinj : Function.Injective ε) {k : Perm α}
    (hk : k ∈ centralizer {ε t}) (hx : ε x = k) : x ∈ centralizer {t} := by
  rw [mem_centralizer_singleton_iff]
  apply hinj
  rw [map_mul, map_mul, hx]
  exact mem_centralizer_singleton_iff.1 hk

theorem quotP_surjective (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) {t : G}
    (ht1 : ε t ≠ 1) (ht2 : ε t * ε t = 1) : Function.Surjective (quotP ε t) := by
  intro σ
  obtain ⟨k, hk⟩ := toPermHom_surjective ht2 σ
  obtain ⟨k', hk'A, hk'1, -⟩ := exists_even_adjust ht1 ht2 k
  obtain ⟨x, hx⟩ := hsurj _ hk'A
  have hxc : x ∈ centralizer {t} := mem_centralizer_of_eq hinj k'.2 hx
  refine ⟨⟨x, hxc⟩, ?_⟩
  have : centHom ε t ⟨x, hxc⟩ = k' := Subtype.ext hx
  rw [quotP, MonoidHom.comp_apply, this, hk'1, hk]

theorem quotF_surjective (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) {t : G}
    (ht1 : ε t ≠ 1) (ht2 : ε t * ε t = 1) : Function.Surjective (quotF ε t) := by
  intro u
  obtain ⟨k, hk⟩ := fixHom_surjective (ε t) u
  obtain ⟨k', hk'A, -, hk'1⟩ := exists_even_adjust ht1 ht2 k
  obtain ⟨x, hx⟩ := hsurj _ hk'A
  have hxc : x ∈ centralizer {t} := mem_centralizer_of_eq hinj k'.2 hx
  refine ⟨⟨x, hxc⟩, ?_⟩
  have : centHom ε t ⟨x, hxc⟩ = k' := Subtype.ext hx
  rw [quotF, MonoidHom.comp_apply, this, hk'1, hk]

theorem quot_comm (hinj : Function.Injective ε) {t : G} (ht2 : ε t * ε t = 1)
    (a b : centralizer {t}) (ha₁ : quotP ε t a = 1) (ha₂ : quotF ε t a = 1)
    (hb₁ : quotP ε t b = 1) (hb₂ : quotF ε t b = 1) : a * b = b * a := by
  have key : ∀ c : centralizer {t}, quotP ε t c = 1 → quotF ε t c = 1 →
      ∀ x, ε c x = x ∨ ε c x = ε t x := by
    intro c hc₁ hc₂ x
    refine apply_eq_or_apply_eq_of_mem_ker ht2 (centHom ε t c) ?_ ?_ x
    · exact hc₁
    · intro y hy
      have := DFunLike.congr_fun hc₂ ⟨y, hy⟩
      exact congrArg Subtype.val this
  have hcomm : ε a * ε b = ε b * ε a :=
    mul_comm_of_apply_eq_or_apply_eq ht2
      (mem_centralizer_singleton_iff.1 (centHom ε t a).2)
      (mem_centralizer_singleton_iff.1 (centHom ε t b).2)
      (key a ha₁ ha₂) (key b hb₁ hb₂)
  apply Subtype.ext
  apply hinj
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact hcomm

end Hom

end Involution

end CFSG.OddStandard.AltNoHe
