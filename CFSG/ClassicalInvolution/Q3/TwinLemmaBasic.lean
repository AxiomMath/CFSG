module

public import Mathlib.GroupTheory.IsSubnormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Q3.Twin

open CFSG
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

theorem isSolvable_of_sup_eq_top {J₁ J₂ : Subgroup Y} (h : J₁ ⊔ J₂ = ⊤) (h₁ : J₁.IsSubnormal)
    (h₂ : J₂.IsSubnormal) (s₁ : Group.IsSolvable J₁) (s₂ : Group.IsSolvable J₂) :
    Group.IsSolvable Y := by
  have h1 := SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal h₁ s₁
  have h2 := SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal h₂ s₂
  have htop : solvableRadical Y = ⊤ := top_le_iff.mp (h ▸ sup_le h1 h2)
  have hs := SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := Y)
  rw [htop] at hs
  exact SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
    (Subgroup.topEquiv (G := Y))

theorem le_pCore_of_isSubnormal {p : ℕ} [Fact p.Prime] {P : Subgroup Y} (hP : P.IsSubnormal)
    (hpg : IsPGroup p P) : P ≤ pCore p Y := by
  have hS : ∀ S : Sylow p Y, P ≤ (S : Subgroup Y) := by
    intro S x hx
    obtain ⟨R, hR⟩ := QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal S hP
    have hRtop : (R : Subgroup ↥P) = ⊤ := (R.is_maximal' (hpg.to_subgroup ⊤) le_top).symm
    have hxR : (⟨x, hx⟩ : ↥P) ∈ (R : Subgroup ↥P) := by rw [hRtop]; trivial
    have h2 : x ∈ (R : Subgroup ↥P).map P.subtype := ⟨⟨x, hx⟩, hxR, rfl⟩
    rw [hR] at h2
    exact h2.1
  have hN : ∀ S : Sylow p Y, Subgroup.normalClosure (P : Set Y) ≤ (S : Subgroup Y) := by
    intro S
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hmem := hS (c⁻¹ • S) hx
    have hconj : ∀ (g : Y) (T : Sylow p Y) (z : Y),
        z ∈ ((g • T : Sylow p Y) : Subgroup Y) ↔ g⁻¹ * z * g ∈ (T : Subgroup Y) := by
      intro g T z
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def]
    rw [hconj] at hmem
    rw [← hc]
    have h2 : c * x * c⁻¹ ∈ (S : Subgroup Y) := by simpa using hmem
    exact h2
  obtain ⟨S⟩ : Nonempty (Sylow p Y) := inferInstance
  have hpgN : IsPGroup p (Subgroup.normalClosure (P : Set Y)) := S.isPGroup'.to_le (hN S)
  exact (Subgroup.le_normalClosure).trans (le_sSup ⟨inferInstance, hpgN⟩)

theorem centralizer_pCore_le (hsolv : Group.IsSolvable Y)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) :
    Subgroup.centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y := by
  have hpp : pPrimeCore 2 Y = ⊥ := by
    refine sSup_eq_bot.mpr fun K hK => hO K hK.1 ?_
    exact Nat.coprime_two_left.mp hK.2
  have hF : fittingSubgroup Y = pCore 2 Y := Fitting_eq_pcore Y 2 hpp
  rw [← hF]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

theorem exists_mem_inf_sylow_three {J : Subgroup Y} (hJ : J.IsSubnormal) (h24 : Nat.card J = 24)
    (S : Sylow 3 Y) : ∃ s : Y, s ∈ (S : Subgroup Y) ∧ s ∈ J ∧ s ^ 3 = 1 ∧ s ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal S hJ
  have hcard : Nat.card (R : Subgroup ↥J) = 3 := by
    rw [Sylow.card_eq_multiplicity, h24]
    have : (24 : ℕ).factorization 3 = 1 := by decide +kernel
    rw [this, pow_one]
  have hcard' : Nat.card ((R : Subgroup ↥J).map J.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hcard]
  rw [hR] at hcard'
  have hne : (S : Subgroup Y) ⊓ J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard'
    omega
  obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hs1' : (s : Y) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hdvd : orderOf (s : Y) ∣ 3 := by
    have h := orderOf_dvd_natCard s
    rw [hcard'] at h
    rwa [Subgroup.orderOf_coe s]
  have hord : orderOf (s : Y) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs1'
    · exact h
  have hs3 : (s : Y) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (s : Y)
    rwa [hord] at this
  exact ⟨s, (Subgroup.mem_inf.mp s.2).1, (Subgroup.mem_inf.mp s.2).2, hs3, hs1'⟩

omit [Finite Y] in
theorem mem_normalizer_commutator {U : Subgroup Y} [U.Normal] {s : Y} (g : Y)
    (hgs : g * s = s * g) : g ∈ Subgroup.normalizer (⁅U, Subgroup.zpowers s⁆ : Subgroup Y) := by
  have hmap : (⁅U, Subgroup.zpowers s⁆ : Subgroup Y).map (MulAut.conj g).toMonoidHom =
      ⁅U, Subgroup.zpowers s⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    have hU : U.map (MulAut.conj g).toMonoidHom = U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.Normal.conj_mem ‹U.Normal› y hy g
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, ?_⟩
        · simpa using Subgroup.Normal.conj_mem ‹U.Normal› x hx g⁻¹
        · simp [MulAut.conj_apply, mul_assoc]
    have hs : (MulAut.conj g).toMonoidHom s = s := by
      simp [MulAut.conj_apply, hgs]
    rw [hU, hs]
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← hmap]
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  · intro hw
    rw [← hmap] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    have : w' = w := by simpa [MulAut.conj_apply] using hww'
    rwa [← this]

section Elementary

variable {G : Type*} [Group G]

theorem commute_commutator_of_central {x y g w : G} (hw : x * y * x⁻¹ * y⁻¹ = w)
    (hwc : ∀ t : G, w * t = t * w) (hxg : x * g = g * x) :
    x * (y * g * y⁻¹ * g⁻¹) = (y * g * y⁻¹ * g⁻¹) * x := by
  have e1 : x * y * x⁻¹ = w * y := by rw [← hw]; group
  have e2 : x * g * x⁻¹ = g := by rw [hxg]; group
  have e3 : x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ = y * g * y⁻¹ * g⁻¹ := by
    calc x * (y * g * y⁻¹ * g⁻¹) * x⁻¹
        = (x * y * x⁻¹) * (x * g * x⁻¹) * (x * y * x⁻¹)⁻¹ * (x * g * x⁻¹)⁻¹ := by group
      _ = (w * y) * g * (w * y)⁻¹ * g⁻¹ := by rw [e1, e2]
      _ = w * (y * g * y⁻¹) * w⁻¹ * g⁻¹ := by group
      _ = (y * g * y⁻¹) * w * w⁻¹ * g⁻¹ := by rw [hwc (y * g * y⁻¹)]
      _ = y * g * y⁻¹ * g⁻¹ := by group
  calc x * (y * g * y⁻¹ * g⁻¹) = x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ * x := by group
    _ = (y * g * y⁻¹ * g⁻¹) * x := by rw [e3]

theorem eq_one_of_commutator_central {x s w : G} (hw : x * s * x⁻¹ * s⁻¹ = w)
    (hwc : ∀ t : G, w * t = t * w) (hw2 : w ^ 2 = 1) (hs : s ^ 3 = 1) : w = 1 := by
  have e1 : x * s * x⁻¹ = w * s := by rw [← hw]; group
  have e2 : (x * s * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hs, mul_one, mul_inv_cancel]
  have e3 : (w * s) ^ 3 = w ^ 3 := by
    have hc : Commute w s := hwc s
    rw [hc.mul_pow, hs, mul_one]
  have e4 : w ^ 3 = 1 := by rw [← e3, ← e1, e2]
  calc w = w ^ 3 := by rw [pow_succ, hw2, one_mul]
    _ = 1 := e4

end Elementary

end CFSG.ClassicalInvolution.Q3.Twin
