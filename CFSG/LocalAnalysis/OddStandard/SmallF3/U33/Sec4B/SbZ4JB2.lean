module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JB1
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem mem_closure_pair_invol {a b x : H} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    x ∈ Subgroup.closure ({a, b} : Set H) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂)
include h

private theorem tau_ne_one : τ ≠ 1 :=
  fun hh => h.tau_not_mem_Q (hh.symm ▸ Q.one_mem)

private theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

private theorem t_comm_zpowers (g : H) (hg : g ∈ zpowers ρ) : t * g = g * t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (((commute_iff_eq t ρ).mpr h.t_rho).zpow_right n).eq

private theorem card_sup_Q_zpowers_tau :
    Nat.card ↥(Q ⊔ zpowers τ) = Nat.card Q * Nat.card ↥(zpowers τ) := by
  haveI : Q.Normal := ⟨fun n hn g => h.normal_Q g n hn⟩
  have hinf : Q ⊓ zpowers τ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    rw [← hn] at hxQ ⊢
    have htau2 : τ ^ 2 = 1 := by rw [pow_two]; exact h.tau_sq
    have hmod : τ ^ n = τ ^ (n % (2 : ℤ)) :=
      zpow_eq_zpow_emod' (x := τ) (m := n) (n := 2) htau2
    rw [hmod] at hxQ ⊢
    rcases Int.emod_two_eq_zero_or_one n with hh | hh
    · rw [hh]; simp
    · rw [hh, zpow_one] at hxQ
      exact absurd hxQ h.tau_not_mem_Q
  let f : ↥Q × ↥(zpowers τ) → ↥(Q ⊔ zpowers τ) :=
    fun p => ⟨(p.1 : H) * (p.2 : H), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨q₁, z₁⟩ ⟨q₂, z₂⟩ heq
    have hval : (q₁ : H) * (z₁ : H) = (q₂ : H) * (z₂ : H) := congrArg Subtype.val heq
    have h2 : (q₂ : H)⁻¹ * (q₁ : H) = (z₂ : H) * (z₁ : H)⁻¹ := by
      have h3 := congrArg (fun x => (q₂ : H)⁻¹ * x * (z₁ : H)⁻¹) hval
      simpa [mul_assoc] using h3
    have haQ : (q₂ : H)⁻¹ * (q₁ : H) ∈ Q := Q.mul_mem (Q.inv_mem q₂.2) q₁.2
    have haZ : (q₂ : H)⁻¹ * (q₁ : H) ∈ zpowers τ := by
      rw [h2]
      exact (zpowers τ).mul_mem z₂.2 ((zpowers τ).inv_mem z₁.2)
    have ha1 : (q₂ : H)⁻¹ * (q₁ : H) = 1 := by
      have hmem : (q₂ : H)⁻¹ * (q₁ : H) ∈ Q ⊓ zpowers τ :=
        Subgroup.mem_inf.mpr ⟨haQ, haZ⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hq : q₁ = q₂ := Subtype.ext (inv_mul_eq_one.mp ha1).symm
    have hz : z₁ = z₂ := by
      apply Subtype.ext
      have hz2 : (z₂ : H) * (z₁ : H)⁻¹ = 1 := by
        rw [← h2, congrArg Subtype.val hq]
        group
      exact (mul_inv_eq_one.mp hz2).symm
    exact Prod.ext hq hz
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨q, hq, zz, hzz, hx⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Q) (t := zpowers τ)).mp x.2
    exact ⟨(⟨q, hq⟩, ⟨zz, hzz⟩), Subtype.ext hx⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

theorem comm_E_rho_le_Q : ⁅centralizer (Y : Set H), zpowers ρ⁆ ≤ Q := by
  let E : Subgroup H := centralizer (Y : Set H)
  let C : Subgroup H := ⁅E, zpowers ρ⁆
  let D : Subgroup H := C ⊔ Q
  have hCE : C ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he g hg
    have hkey : ⁅e, g⁆ = e * (g * e⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]; group
    rw [hkey]
    exact mul_mem he (h.E_normal (g := g) (Subgroup.inv_mem _ he))
  have hDE : D ≤ E := sup_le hCE h.Q_le_E
  have hDinv : ∀ k ∈ D, t * k * t⁻¹ ∈ D := by
    have hCinv : C ≤ D.comap (MulAut.conj t : H →* H) := by
      rw [Subgroup.commutator_le]
      intro e he g hg
      rw [Subgroup.mem_comap]
      change t * ⁅e, g⁆ * t⁻¹ ∈ D
      rw [conjugate_commutatorElement]
      have hgt : t * g * t⁻¹ = g := by
        rw [t_comm_zpowers h g hg]; group
      rw [hgt]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (h.E_normal (g := t) he) hg)
    have hQinv : Q ≤ D.comap (MulAut.conj t : H →* H) := by
      intro q hq
      rw [Subgroup.mem_comap]
      change t * q * t⁻¹ ∈ D
      exact Subgroup.mem_sup_right (h.normal_Q t q hq)
    have hDsub : D ≤ D.comap (MulAut.conj t : H →* H) := sup_le hCinv hQinv
    intro k hk
    have hk' := hDsub hk
    rw [Subgroup.mem_comap] at hk'
    change t * k * t⁻¹ ∈ D at hk'
    exact hk'
  intro k hk
  have hkD : k ∈ D := Subgroup.mem_sup_left (hk : k ∈ C)
  have hkE : k ∈ E := hDE hkD
  let a : H := t * k * t⁻¹
  have haD : a ∈ D := hDinv k hkD
  have haE : a ∈ E := hDE haD
  have hta : t * a * t⁻¹ = k := by
    show t * (t * k * t⁻¹) * t⁻¹ = k
    calc t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t⁻¹ * t⁻¹) := by group
      _ = k := by simp [h.t_sq, t_inv h]
  have hkaQ : k * a ∈ Q := by
    apply h.K_triv (k * a)
    · exact D.mul_mem hkD haD
    · have hkey : t * (k * a) * t⁻¹ * (k * a)⁻¹ = a * k * a⁻¹ * k⁻¹ := by
        rw [mul_inv_rev]
        calc t * (k * a) * t⁻¹ * (a⁻¹ * k⁻¹)
            = (t * k * t⁻¹) * (t * a * t⁻¹) * a⁻¹ * k⁻¹ := by group
          _ = a * k * a⁻¹ * k⁻¹ := by rw [hta]
      rw [hkey]
      exact h.E_comm_mem_Q haE hkE
  have hakQ : a * k ∈ Q := by
    have h1 : a * k * a⁻¹ * k⁻¹ ∈ Q := h.E_comm_mem_Q haE hkE
    have h2 : a * k = (a * k * a⁻¹ * k⁻¹) * (k * a) := by group
    rw [h2]
    exact mul_mem h1 hkaQ
  have hQmem : t * k * t⁻¹ * k⁻¹ ∈ Q := by
    have h2 : t * k * t⁻¹ * k⁻¹ = (a * k) * (k * k)⁻¹ := by
      show t * k * t⁻¹ * k⁻¹ = (t * k * t⁻¹ * k) * (k * k)⁻¹
      group
    rw [h2]
    exact mul_mem hakQ (inv_mem (h.E_sq_mem_Q hkE))
  exact h.K_triv k hkD hQmem

theorem exists_fixed_coset {e : H} (he : e ∈ centralizer (Y : Set H)) :
    ∃ q ∈ Q, ρ * (e * q) * ρ⁻¹ = e * q := by
  have hwQ : e⁻¹ * ρ * e * ρ⁻¹ ∈ Q := by
    have hcQ : ρ * e * ρ⁻¹ * e⁻¹ ∈ Q := by
      apply h.comm_E_rho_le_Q
      rw [← commutatorElement_def, ← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator he (Subgroup.mem_zpowers ρ))
    have hkey : e⁻¹ * (ρ * e * ρ⁻¹ * e⁻¹) * e = e⁻¹ * ρ * e * ρ⁻¹ := by group
    rw [← hkey]
    simpa using h.normal_Q e⁻¹ (ρ * e * ρ⁻¹ * e⁻¹) hcQ
  let f : ↥Q → ↥Q := fun q =>
    ⟨ρ * (q : H) * ρ⁻¹ * (q : H)⁻¹,
      Q.mul_mem (h.rho_norm_Q (q : H) q.2) (Q.inv_mem q.2)⟩
  have hf_inj : Function.Injective f := by
    intro q₁ q₂ hq
    apply Subtype.ext
    have hval : ρ * (q₁ : H) * ρ⁻¹ * (q₁ : H)⁻¹
        = ρ * (q₂ : H) * ρ⁻¹ * (q₂ : H)⁻¹ := congrArg Subtype.val hq
    have h2 : (q₁ : H) * ρ⁻¹ * (q₁ : H)⁻¹ = (q₂ : H) * ρ⁻¹ * (q₂ : H)⁻¹ := by
      have h := congrArg (fun x => ρ⁻¹ * x) hval
      simpa [mul_assoc] using h
    have ha1 : (q₂ : H)⁻¹ * (q₁ : H) = 1 := by
      have h3 : ((q₂ : H)⁻¹ * (q₁ : H)) * ρ⁻¹ * ((q₂ : H)⁻¹ * (q₁ : H))⁻¹ = ρ⁻¹ := by
        calc ((q₂ : H)⁻¹ * (q₁ : H)) * ρ⁻¹ * ((q₂ : H)⁻¹ * (q₁ : H))⁻¹
            = (q₂ : H)⁻¹ * ((q₁ : H) * ρ⁻¹ * (q₁ : H)⁻¹) * (q₂ : H) := by group
          _ = (q₂ : H)⁻¹ * ((q₂ : H) * ρ⁻¹ * (q₂ : H)⁻¹) * (q₂ : H) := by rw [h2]
          _ = ρ⁻¹ := by group
      have h4 : ((q₂ : H)⁻¹ * (q₁ : H)) * ρ * ((q₂ : H)⁻¹ * (q₁ : H))⁻¹ = ρ := by
        have h := congrArg Inv.inv h3
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
      have hcomm : ρ * ((q₂ : H)⁻¹ * (q₁ : H)) * ρ⁻¹ = (q₂ : H)⁻¹ * (q₁ : H) := by
        have h5 : ((q₂ : H)⁻¹ * (q₁ : H)) * ρ = ρ * ((q₂ : H)⁻¹ * (q₁ : H)) := by
          have h := congrArg (fun x => x * ((q₂ : H)⁻¹ * (q₁ : H))) h4
          simpa [mul_assoc] using h
        rw [← h5]; group
      exact h.rho_fpf_Q ((q₂ : H)⁻¹ * (q₁ : H))
        (Q.mul_mem (Q.inv_mem q₂.2) q₁.2) hcomm
    exact (inv_mul_eq_one.mp ha1).symm
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  obtain ⟨q, hq⟩ := hf_surj ⟨(e⁻¹ * ρ * e * ρ⁻¹)⁻¹, Q.inv_mem hwQ⟩
  refine ⟨(q : H), q.2, ?_⟩
  have hfq : ρ * (q : H) * ρ⁻¹ * (q : H)⁻¹ = (e⁻¹ * ρ * e * ρ⁻¹)⁻¹ :=
    congrArg Subtype.val hq
  have hρq : ρ * (q : H) * ρ⁻¹ = (e⁻¹ * ρ * e * ρ⁻¹)⁻¹ * (q : H) := by
    rw [← hfq]; group
  have hρe : ρ * e * ρ⁻¹ = e * (e⁻¹ * ρ * e * ρ⁻¹) := by group
  calc ρ * (e * (q : H)) * ρ⁻¹
      = (ρ * e * ρ⁻¹) * (ρ * (q : H) * ρ⁻¹) := by group
    _ = (e * (e⁻¹ * ρ * e * ρ⁻¹)) * ((e⁻¹ * ρ * e * ρ⁻¹)⁻¹ * (q : H)) := by
        rw [hρe, hρq]
    _ = e * (q : H) := by group

theorem centralizer_rho_inf_E :
    centralizer ({ρ} : Set H) ⊓ centralizer (Y : Set H) = zpowers τ := by
  let P : Subgroup H := centralizer ({ρ} : Set H) ⊓ centralizer (Y : Set H)
  have hP2 : IsPGroup 2 P := h.E_isPGroup.to_le (fun x hx => (Subgroup.mem_inf.mp hx).2)
  obtain ⟨c, hcρ, hcjt⟩ := h.tt_sylow P (fun x hx => (Subgroup.mem_inf.mp hx).1) hP2
  have hτP : τ ∈ P := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr h.tau_rho, h.tau_mem_E⟩
  have hx : ∀ x ∈ P, c * x * c⁻¹ = 1 ∨ c * x * c⁻¹ = τ := by
    intro x hxP
    have hcl : c * x * c⁻¹ ∈ closure ({t, τ} : Set H) := hcjt x hxP
    have hcxE : c * x * c⁻¹ ∈ centralizer (Y : Set H) := h.E_normal (Subgroup.mem_inf.mp hxP).2
    rw [mem_closure_pair_invol h.t_sq h.tau_sq h.t_tau] at hcl
    rcases hcl with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd (h1 ▸ hcxE) h.t_not_mem_E
    · exact Or.inr h1
    · exact absurd (h1 ▸ hcxE) h.tt_not_mem_E
  have hτ_neq : c * τ * c⁻¹ ≠ 1 := by
    intro h1
    apply tau_ne_one h
    have h := congrArg (fun x => c⁻¹ * x * c) h1
    simpa [mul_assoc] using h
  have hcτ : c * τ * c⁻¹ = τ := by
    rcases hx τ hτP with h1 | h1
    · exact absurd h1 hτ_neq
    · exact h1
  apply le_antisymm
  · intro p hp
    rcases hx p hp with h1 | h1
    · refine Subgroup.mem_zpowers_iff.mpr ⟨0, ?_⟩
      have hp1 : p = 1 := by
        have h := congrArg (fun x => c⁻¹ * x * c) h1
        simpa [mul_assoc] using h
      rw [hp1]; simp
    · refine Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩
      have hpτ : p = τ := by
        have h : c * p * c⁻¹ = c * τ * c⁻¹ := by rw [h1, hcτ]
        have h := congrArg (fun x => c⁻¹ * x * c) h
        simpa [mul_assoc] using h
      rw [hpτ]; simp
  · refine Subgroup.zpowers_le.mpr ?_
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr h.tau_rho, h.tau_mem_E⟩

theorem E_eq : centralizer (Y : Set H) = Q ⊔ zpowers τ := by
  apply le_antisymm
  · intro e he
    obtain ⟨q, hq, hfix⟩ := h.exists_fixed_coset he
    have hqE : q ∈ centralizer (Y : Set H) := h.Q_le_E hq
    have heq_cent : e * q ∈ centralizer ({ρ} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun x => x * ρ) hfix
      rw [mul_assoc (ρ * (e * q)) ρ⁻¹ ρ, inv_mul_cancel, mul_one] at h
      exact h.symm
    have heqE : e * q ∈ centralizer (Y : Set H) := mul_mem he hqE
    have hmem : e * q ∈ zpowers τ := by
      have hinf : e * q ∈ centralizer ({ρ} : Set H) ⊓ centralizer (Y : Set H) :=
        Subgroup.mem_inf.mpr ⟨heq_cent, heqE⟩
      rwa [h.centralizer_rho_inf_E] at hinf
    have heq : e = (e * q) * q⁻¹ := by group
    rw [heq]
    have hsup : (e * q) * q⁻¹ ∈ zpowers τ ⊔ Q :=
      Subgroup.mul_mem_sup hmem (Q.inv_mem hq)
    rwa [sup_comm] at hsup
  · refine sup_le h.Q_le_E ?_
    exact Subgroup.zpowers_le.mpr h.tau_mem_E

theorem card_E : Nat.card (centralizer (Y : Set H)) = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htau2 : τ ^ 2 = 1 := by rw [pow_two]; exact h.tau_sq
  have hord : orderOf τ = 2 := orderOf_eq_prime htau2 (tau_ne_one h)
  rw [h.E_eq, card_sup_Q_zpowers_tau h]
  norm_num [h.card_Q, Nat.card_zpowers, hord]

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
