module

public import CFSG.Certificates.Kernel.YModel.ChainSem
import CFSG.Certificates.Kernel.YModel.SchCard
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

namespace CFSG.Certificates.TwDce

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.YModel.Chain

variable {G : Type*} [Group G] {n : ℕ} (ρ : G →* Equiv.Perm (Fin n)) (g : ℕ → G) (N : ℕ → ℕ)
  (L : List ℕ)

@[expose] def lgen : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure ((fun c => ρ (g c)) '' {c | c ∈ L})

variable {ρ g N L}

theorem mem_orbit_of_orbitOK (hv : ∀ c ∈ L, StagesValid 15 (N c))
    (hρ : ∀ c ∈ L, ∀ x : Fin n, benesPerm 15 (N c) x = (ρ (g c) x : ℕ))
    (hfix : ∀ c ∈ L, ∀ p, n ≤ p → p < 2 ^ 15 → benesPerm 15 (N c) p = p)
    {b R M : ℕ} (hb : b < n) (hn : n ≤ 2 ^ 15) (h : orbitOK 15 (L.map N) b R M = true) :
    ∀ p, M.testBit p = true → ∃ hp : p < n,
      (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit (lgen ρ g L) (⟨b, hb⟩ : Fin n) := by
  have hv' : ∀ N' ∈ L.map N, StagesValid 15 N' := by
    intro N' hN'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hN'
    exact hv c hc
  have spec := orbitOK_spec hv' (by omega) h
  refine spec.2.2.2 (fun p => ∃ hp : p < n,
    (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit (lgen ρ g L) (⟨b, hb⟩ : Fin n)) ⟨hb, ?_⟩ ?_
  · exact MulAction.mem_orbit_self _
  · intro p hp N' hN' ⟨hq, hmem⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hN'
    have hpn : p < n := by
      by_contra hpn
      rw [hfix c hc p (by omega) hp] at hq
      exact hpn hq
    refine ⟨hpn, ?_⟩
    have he : (⟨benesPerm 15 (N c) p, hq⟩ : Fin n) = ρ (g c) ⟨p, hpn⟩ :=
      Fin.ext (hρ c hc ⟨p, hpn⟩)
    rw [he] at hmem
    have hgc : ρ (g c) ∈ lgen ρ g L := Subgroup.subset_closure ⟨c, hc, rfl⟩
    have := MulAction.mem_orbit_of_mem_orbit (⟨ρ (g c), hgc⟩⁻¹ : lgen ρ g L) hmem
    convert this using 1
    change (⟨p, hpn⟩ : Fin n) = (ρ (g c))⁻¹ (ρ (g c) ⟨p, hpn⟩)
    simp

theorem le_ncard_orbit_of_orbitOK (hv : ∀ c ∈ L, StagesValid 15 (N c))
    (hρ : ∀ c ∈ L, ∀ x : Fin n, benesPerm 15 (N c) x = (ρ (g c) x : ℕ))
    (hfix : ∀ c ∈ L, ∀ p, n ≤ p → p < 2 ^ 15 → benesPerm 15 (N c) p = p)
    {b R M : ℕ} (hb : b < n) (hn : n ≤ 2 ^ 15) (h : orbitOK 15 (L.map N) b R M = true) :
    popc 15 M ≤ (MulAction.orbit (lgen ρ g L) (⟨b, hb⟩ : Fin n)).ncard := by
  have hmem := mem_orbit_of_orbitOK hv hρ hfix hb hn h
  have hM : M < 2 ^ 2 ^ 15 := Nat.lt_pow_two_of_testBit _ fun p hp => by
    cases e : M.testBit p
    · rfl
    · obtain ⟨hp', -⟩ := hmem p e
      omega
  rw [Sch.popc_eq 15 M hM]
  have hsum : ∑ r ∈ Finset.range (2 ^ 15), (M.testBit r).toNat =
      ((Finset.range (2 ^ 15)).filter fun r => M.testBit r = true).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro r _
    cases M.testBit r <;> rfl
  rw [hsum]
  have hn0 : 0 < n := by omega
  set S := (Finset.range (2 ^ 15)).filter fun r => M.testBit r = true
  let f : ℕ → Fin n := fun p => ⟨p % n, Nat.mod_lt _ hn0⟩
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro a ha b' hb' e
    have ha' := (hmem a (Finset.mem_filter.1 ha).2).1
    have hb'' := (hmem b' (Finset.mem_filter.1 hb').2).1
    have := congrArg Fin.val e
    simp only [f, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb''] at this
    exact this
  rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro x hx
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨hpn, hpo⟩ := hmem p (Finset.mem_filter.1 hp).2
  have : f p = ⟨p, hpn⟩ := Fin.ext (Nat.mod_eq_of_lt hpn)
  rw [this]
  exact hpo

end CFSG.Certificates.TwDce

end
