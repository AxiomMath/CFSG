module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.QTGen4.Ku

section Linear

local instance zmod2_fact_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c
  decide

theorem zmod2_sum_swap (c d : ZMod 2) : c + d + (d + c) = 0 := by
  revert c d
  decide

theorem zmod2_cancel (X Y Z : ZMod 2) : X + Y + (Y + Z) = X + Z := by
  revert X Y Z
  decide

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem add_self_eq_zero_V (v : V) : v + v = 0 := by
  have h := (two_smul (ZMod 2) v).symm
  rwa [show (2 : ZMod 2) = 0 from rfl, zero_smul] at h

theorem eq_of_add_eq_zero_V {v w : V} (h : v + w = 0) : w = v := by
  calc w = w + (v + v) := by rw [add_self_eq_zero_V, add_zero]
    _ = (v + w) + v := by abel
    _ = v := by rw [h, zero_add]

abbrev kuDeltaLin (γ : V →ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V := LinearMap.id + γ

theorem kuDeltaLin_apply (γ : V →ₗ[ZMod 2] V) (v : V) : kuDeltaLin γ v = v + γ v := rfl

theorem kuDeltaLin_delta (γ : V →ₗ[ZMod 2] V) (hγ : ∀ v, γ (γ v) = v) (v : V) :
    kuDeltaLin γ (kuDeltaLin γ v) = 0 := by
  rw [kuDeltaLin_apply, kuDeltaLin_apply, map_add, hγ, add_comm (γ v) v, add_self_eq_zero_V]

theorem finrank_range_kuDeltaLin [Module.Finite (ZMod 2) V] (γ : V →ₗ[ZMod 2] V)
    (hγ : ∀ v, γ (γ v) = v) (hne : ∃ v, γ v ≠ v) (x : V →ₗ[ZMod 2] V)
    (hx3 : ∀ v, x (x (x v)) = v) (hxγ : ∀ v, γ (x v) = x (γ v))
    (hfix : ∀ v, x v = v → v = 0) (hV : Module.finrank (ZMod 2) V = 4) :
    Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin γ)) = 2 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (kuDeltaLin γ)
  rw [hV] at hrn
  have hle : LinearMap.range (kuDeltaLin γ) ≤ LinearMap.ker (kuDeltaLin γ) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact kuDeltaLin_delta γ hγ v
  have hup : Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin γ)) ≤ 2 := by
    have := Submodule.finrank_mono hle
    omega
  have hpos : Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin γ)) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hne
    have hmem : kuDeltaLin γ v ∈ LinearMap.range (kuDeltaLin γ) := ⟨v, rfl⟩
    have hbot := Submodule.finrank_eq_zero.mp h0
    rw [hbot, Submodule.mem_bot] at hmem
    apply hv
    exact eq_of_add_eq_zero_V (by rw [← kuDeltaLin_apply]; exact hmem)
  have hxS : ∀ s ∈ LinearMap.range (kuDeltaLin γ), x s ∈ LinearMap.range (kuDeltaLin γ) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨x w, ?_⟩
    rw [kuDeltaLin_apply, kuDeltaLin_apply, hxγ, map_add]
  have hne1 : Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin γ)) ≠ 1 := by
    intro h1
    have hpos1 : 0 < Module.finrank (ZMod 2) (LinearMap.range (kuDeltaLin γ)) := by
      rw [h1]
      exact one_pos
    have : Nontrivial (LinearMap.range (kuDeltaLin γ)) := Module.nontrivial_of_finrank_pos hpos1
    obtain ⟨s, hs0⟩ := exists_ne (0 : LinearMap.range (kuDeltaLin γ))
    have hs0' : (s : V) ≠ 0 := fun h => hs0 (Subtype.ext h)
    let xs : LinearMap.range (kuDeltaLin γ) := ⟨x s, hxS s s.2⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp h1 xs
    have hc' : c • (s : V) = x s := congrArg Subtype.val hc
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    ·
      rw [zero_smul] at hc'
      have hxs0 : x (s : V) = 0 := hc'.symm
      have := hx3 (s : V)
      rw [hxs0, map_zero, map_zero] at this
      exact hs0' this.symm
    · rw [one_smul] at hc'
      exact hs0' (hfix _ hc'.symm)
  omega

theorem B_delta_delta (γ : V →ₗ[ZMod 2] V) (hγ : ∀ v, γ (γ v) = v)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hBγ : ∀ a b, B (γ a) (γ b) = B a b) (a b : V) :
    B (a + γ a) (b + γ b) = 0 := by
  have e1 : B (γ a) (γ b) = B a b := hBγ a b
  have e2 : B (γ a) b = B a (γ b) := by
    have := hBγ a (γ b)
    rwa [hγ] at this
  simp only [map_add, LinearMap.add_apply]
  rw [e1, e2]
  exact zmod2_sum_swap _ _

theorem B_self_gamma_eq_zero [Module.Finite (ZMod 2) V] (γ : V →ₗ[ZMod 2] V)
    (hγ : ∀ v, γ (γ v) = v) (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hBγ : ∀ a b, B (γ a) (γ b) = B a b) (hBs : ∀ a b, B a b = B b a)
    (x : V →ₗ[ZMod 2] V) (hxγ : ∀ v, γ (x v) = x (γ v))
    (hBx : ∀ a b, B (x a) (x b) = B a b) (hfix : ∀ v, x v = v → v = 0) (a : V) :
    B a (γ a) = 0 := by
  have e2 : ∀ a b, B (γ a) b = B a (γ b) := by
    intro a b
    have := hBγ a (γ b)
    rwa [hγ] at this
  have fadd : ∀ a b, B (a + b) (γ (a + b)) = B a (γ a) + B b (γ b) := by
    intro a b
    simp only [map_add, LinearMap.add_apply]
    have c1 : B b (γ a) = B a (γ b) := by rw [hBs, e2]
    rw [c1]
    exact zmod2_cancel _ _ _
  have fx : ∀ a, B (x a) (γ (x a)) = B a (γ a) := by
    intro a
    rw [hxγ, hBx]
  let L : V →ₗ[ZMod 2] V := x + LinearMap.id
  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun v hv => ?_
    have hv' : x v + v = 0 := hv
    have hxv : x v = v := (eq_of_add_eq_zero_V hv').symm
    exact hfix v hxv
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (K := ZMod 2) (f := L)).mp hLinj
  obtain ⟨b, hb⟩ := hLsurj a
  have hb' : x b + b = a := hb
  rw [← hb', fadd, fx]
  exact zmod2_add_self _

theorem sum_orbit_eq_zero (σ : V →ₗ[ZMod 2] V) (hσ3 : ∀ v, σ (σ (σ v)) = v)
    (hfix : ∀ v, σ v = v → v = 0) (r : V) : r + σ r + σ (σ r) = 0 := by
  have h1 : σ (r + σ r + σ (σ r)) = r + σ r + σ (σ r) := by
    rw [map_add, map_add, hσ3]
    abel
  exact hfix _ h1

theorem indep_orbit_pair (σ : V →ₗ[ZMod 2] V) (hσ3 : ∀ v, σ (σ (σ v)) = v)
    (hfix : ∀ v, σ v = v → v = 0) {r : V} (hr0 : r ≠ 0) :
    LinearIndependent (ZMod 2) ![r, σ r] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases zmod2_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    simp only [zero_smul, one_smul, zero_add] at hst
    have : r = 0 := by
      rw [← hσ3 r, hst, map_zero, map_zero]
    exact hr0 this
  · exfalso
    simp only [one_smul, zero_smul, add_zero] at hst
    exact hr0 hst
  · exfalso
    simp only [one_smul] at hst
    exact hr0 (hfix r (eq_of_add_eq_zero_V hst))

theorem orbit_of_nonzero [Module.Finite (ZMod 2) V] (R : Submodule (ZMod 2) V)
    (hR : Module.finrank (ZMod 2) R = 2) (σ : V →ₗ[ZMod 2] V) (hσ3 : ∀ v, σ (σ (σ v)) = v)
    (hfix : ∀ v, σ v = v → v = 0) (hσR : ∀ v ∈ R, σ v ∈ R) {r : V} (hr : r ∈ R) (hr0 : r ≠ 0)
    {r' : V} (hr' : r' ∈ R) :
    r' = 0 ∨ r' = r ∨ r' = σ r ∨ r' = σ (σ r) := by
  have hli := indep_orbit_pair σ hσ3 hfix hr0
  have hsub : Set.range ![r, σ r] ⊆ (R : Set V) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hr
    · simpa using hσR r hr
  have h2 := linearIndependent_iff_card_eq_finrank_span.mp hli
  rw [Fintype.card_fin] at h2
  have hspan : Submodule.span (ZMod 2) (Set.range ![r, σ r]) = R := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr hsub
    · rw [hR]
      exact h2.symm
  have hset : Set.range ![r, σ r] = ({r, σ r} : Set V) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  have hmem : r' ∈ Submodule.span (ZMod 2) ({r, σ r} : Set V) := by
    rw [← hset, hspan]
    exact hr'
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  rcases zmod2_eq_zero_or_one a with h0 | h0 <;>
    rcases zmod2_eq_zero_or_one b with h1 | h1
  · left
    rw [← hab, h0, h1]
    simp
  · right; right; left
    rw [← hab, h0, h1]
    simp
  · right; left
    rw [← hab, h0, h1]
    simp
  · right; right; right
    rw [← hab, h0, h1, one_smul, one_smul]
    exact (eq_of_add_eq_zero_V (sum_orbit_eq_zero σ hσ3 hfix r)).symm

end Linear

end CFSG.GH74.QTGen4.Ku
