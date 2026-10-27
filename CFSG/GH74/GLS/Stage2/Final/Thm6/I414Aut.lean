module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Adapters.WholeGroupLayer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer perfect_action_inner)
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def fixedSubgroup {X : Type*} [Group X] (φ : MulAut X) : Subgroup X where
  carrier := {x | φ x = x}
  one_mem' := map_one φ
  mul_mem' := by
    intro a b ha hb
    change φ (a * b) = a * b
    change φ a = a at ha
    change φ b = b at hb
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change φ a⁻¹ = a⁻¹
    change φ a = a at ha
    rw [map_inv, ha]

theorem centralizer_generalizedFitting_le_fitting (A : Type*) [Group A] [Finite A] :
    Subgroup.centralizer ((generalizedFitting A : Subgroup A) : Set A) ≤ fittingSubgroup A :=
  CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup A

theorem eq_one_of_fixes_generalizedFitting {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hXp : p.Coprime (Nat.card X)) (φ : MulAut X) {n : ℕ} (hφ : φ ^ (p ^ n) = 1)
    (hfix : ∀ x ∈ generalizedFitting X, φ x = x) : φ = 1 := by
  ext g
  rw [MulAut.one_apply]
  set u : X := g⁻¹ * φ g with hu
  have hφg : φ g = g * u := by rw [hu]; group
  have hcent : u ∈ Subgroup.centralizer ((generalizedFitting X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hconj : g * f * g⁻¹ ∈ generalizedFitting X :=
      (generalized_fitting_characteristic.2).conj_mem f hf g
    have h1 : φ g * f * (φ g)⁻¹ = g * f * g⁻¹ := by
      have := hfix _ hconj
      rwa [map_mul, map_mul, map_inv, hfix f hf] at this
    have h2 : u * f = f * u :=
      calc u * f = g⁻¹ * (φ g * f * (φ g)⁻¹) * φ g := by rw [hu]; group
        _ = g⁻¹ * (g * f * g⁻¹) * φ g := by rw [h1]
        _ = f * u := by rw [hu]; group
    exact h2.symm
  have huF : u ∈ fittingSubgroup X := centralizer_generalizedFitting_le_fitting X hcent
  have hφu : φ u = u := hfix u ((le_sup_left : fittingSubgroup X ≤ generalizedFitting X) huF)
  have hiter : ∀ k : ℕ, (φ ^ k) g = g * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφu, hφg, pow_succ', mul_assoc]
  have hpow : u ^ (p ^ n) = 1 := by
    have h := hiter (p ^ n)
    rw [hφ, MulAut.one_apply] at h
    have : g * u ^ (p ^ n) = g * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have hord : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes (hXp.pow_left n) (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_natCard u)
  rw [orderOf_eq_one_iff.mp hord, mul_one] at hφg
  exact hφg

theorem act_trivial_on_quasisimple {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    {A : Type*} [Group A] [Group.IsPerfect A] (ψ : A →* MulAut L)
    (hOut : Group.IsSolvable (Outer (L ⧸ Subgroup.center L)))
    {p : ℕ} (hLp : p.Coprime (Nat.card L)) {a : A} {n : ℕ} (ha : a ^ (p ^ n) = 1) :
    ψ a = 1 := by
  have : Group.IsPerfect L := hL.1
  obtain ⟨-, hsimple, hnc⟩ := hL
  let ψ' : A →* MulAut (L ⧸ Subgroup.center L) := (centerQuotientHom L).comp ψ
  obtain ⟨l, hl⟩ := perfect_action_inner ψ' a
  have hpow : MulAut.conj (l ^ (p ^ n)) = 1 := by
    rw [map_pow, ← hl, ← map_pow, ha, map_one]
  have hZ : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hx : x ∈ Subgroup.center (L ⧸ Subgroup.center L) := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hlp : l ^ (p ^ n) = 1 := by
    have hmem : l ^ (p ^ n) ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun m : MulAut (L ⧸ Subgroup.center L) => m y) hpow
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * l ^ (p ^ n) = (l ^ (p ^ n) * y * (l ^ (p ^ n))⁻¹) * l ^ (p ^ n) := by rw [h1]
        _ = l ^ (p ^ n) * y := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hl1 : l = 1 := by
    have hdvd : orderOf l ∣ Nat.card L :=
      (orderOf_dvd_natCard l).trans (Subgroup.card_quotient_dvd_card _)
    have : orderOf l = 1 :=
      Nat.eq_one_of_dvd_coprimes (hLp.pow_left n) (orderOf_dvd_of_pow_eq_one hlp) hdvd
    exact orderOf_eq_one_iff.mp this
  apply onCenterQuotient_eq_one_imp
  have : ψ' a = onCenterQuotient (ψ a) := rfl
  rw [← this, hl, hl1, map_one]

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
