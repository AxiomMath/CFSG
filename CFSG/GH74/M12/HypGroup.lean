module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.ElementaryAbelianTransport
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

namespace CFSG.GH74.M12.Hyp

open Subgroup

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_two {K : Type*} [Group K] {t x : K}
    (ht : orderOf t = 2) (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht]
  have : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem nonempty_mulEquiv_perm_three_of_card_six {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 6) (a b : K) (hab : a * b ≠ b * a) :
    Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hK]; norm_num)
  have hSc : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have hidx : (zpowers t).index = 3 := by
    have := (zpowers t).card_mul_index
    rw [hSc, hK] at this
    omega
  have hcardQ : Nat.card (K ⧸ zpowers t) = 3 := by rw [← Subgroup.index_eq_card, hidx]
  let φ : K →* Equiv.Perm (K ⧸ zpowers t) := MulAction.toPermHom K (K ⧸ zpowers t)
  have hker : φ.ker = (zpowers t).normalCore := (Subgroup.normalCore_eq_ker _).symm
  have hkerle : φ.ker ≤ zpowers t := by rw [hker]; exact Subgroup.normalCore_le _
  have hker_bot : φ.ker = ⊥ := by
    by_contra hne
    have hcd : Nat.card φ.ker ∣ 2 := by
      rw [← hSc]; exact Subgroup.card_dvd_of_le hkerle
    have hne1 : Nat.card φ.ker ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
    have h2 : Nat.card φ.ker = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hcd with h | h
      · exact absurd h hne1
      · exact h
    have hSeq : φ.ker = zpowers t :=
      Subgroup.eq_of_le_of_card_ge hkerle (by rw [hSc, h2])
    have hnorm : (zpowers t).Normal := hSeq ▸ φ.normal_ker
    have hcentral : ∀ k : K, k * t = t * k := by
      intro k
      have hmem : k * t * k⁻¹ ∈ zpowers t := hnorm.conj_mem t (Subgroup.mem_zpowers t) k
      have hord : orderOf (k * t * k⁻¹) = 2 := by
        have := MulEquiv.orderOf_eq (MulAut.conj k) t
        simpa [ht] using this
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht hmem with h | h
      · rw [h] at hord; simp at hord
      · rw [mul_inv_eq_iff_eq_mul] at h; exact h
    have hle : (QuotientGroup.mk' (zpowers t)).ker ≤ Subgroup.center K := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht hx with rfl | rfl
      · exact Subgroup.one_mem _
      · rw [Subgroup.mem_center_iff]
        intro g
        exact hcentral g
    have : IsCyclic (K ⧸ zpowers t) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card hcardQ
    have hcomm : IsMulCommutative K :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' (zpowers t)) hle
    exact hab (hcomm.is_comm.comm a b)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker_bot
  have hcardP : Nat.card (Equiv.Perm (K ⧸ zpowers t)) = 6 := by
    rw [Nat.card_perm, hcardQ]; rfl
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, by rw [hK, hcardP]⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hcardQ))⟩

theorem eq_bot_of_normal_isPGroup_perm_three (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  have hx1 : x ≠ 1 := fun h => hne (by rw [h]; exact Subgroup.one_mem _)
  have key : ∀ y : Equiv.Perm (Fin 3), y ≠ 1 → ∃ σ : Equiv.Perm (Fin 3),
      y * (σ * y * σ⁻¹) ≠ 1 ∧ (y * (σ * y * σ⁻¹)) ^ 3 = 1 := by decide +kernel
  obtain ⟨σ, h1, h3⟩ := key x hx1
  have hw : x * (σ * x * σ⁻¹) ∈ N := Subgroup.mul_mem _ hx (Normal.conj_mem inferInstance x hx σ)
  obtain ⟨k, hk⟩ := hN ⟨_, hw⟩
  have hk' : (x * (σ * x * σ⁻¹)) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf (x * (σ * x * σ⁻¹)) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rw [hcop] at hdvd
  exact h1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd))

theorem comm_mem_of_index_two {P : Type*} [Group P] (K : Subgroup P) (hK : K.index = 2)
    (e f : P) : e⁻¹ * f * e * f⁻¹ ∈ K := by
  have h1 : e⁻¹ * f * e * f⁻¹ ∈ K ↔ (e⁻¹ * f * e ∈ K ↔ f⁻¹ ∈ K) :=
    Subgroup.mul_mem_iff_of_index_two hK
  have h2 : e⁻¹ * f * e ∈ K ↔ (e⁻¹ * f ∈ K ↔ e ∈ K) := Subgroup.mul_mem_iff_of_index_two hK
  have h3 : e⁻¹ * f ∈ K ↔ (e⁻¹ ∈ K ↔ f ∈ K) := Subgroup.mul_mem_iff_of_index_two hK
  rw [h1, h2, h3, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem pCore_le_sylow {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    CFSG.pCore p G ≤ (S : Subgroup G) := by
  have hsup : IsPGroup p (((S : Subgroup G) ⊔ CFSG.pCore p G : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right S.isPGroup' (CFSG.pCore_isPGroup (G := G) (p := p))
  have heq : (S : Subgroup G) ⊔ CFSG.pCore p G = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_left
  exact sup_eq_left.mp heq

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsElementaryAbelian p A) : CFSG.IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem isExtraspecial_of_mulEquiv {p : ℕ} {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.IsExtraspecial p G) : CFSG.IsExtraspecial p G' where
  center_order_p := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact h.center_order_p
  quotient_elementary_abelian :=
    isElementaryAbelian_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center G') e (Subgroup.map_center_eq e))
      h.quotient_elementary_abelian
  quotient_nontrivial := by
    have := h.quotient_nontrivial
    exact (QuotientGroup.congr (Subgroup.center G) (Subgroup.center G') e
      (Subgroup.map_center_eq e)).symm.surjective.nontrivial

end CFSG.GH74.M12.Hyp
