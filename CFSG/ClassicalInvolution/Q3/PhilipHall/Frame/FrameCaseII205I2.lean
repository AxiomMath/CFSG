module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205I1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205IQ8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Psi

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem act_rhoK_eq_of_psiK_eq {x x' : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hx' : x' ∈ Subgroup.normalizer (K : Set G))
    (hpsi : psiK K ⟨x, hx⟩ = psiK K ⟨x', hx'⟩) :
    Idx2.act (rhoK K ⟨x, hx⟩) = Idx2.act (rhoK K ⟨x', hx'⟩) := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have h1 : psiK K (⟨x, hx⟩⁻¹ * ⟨x', hx'⟩) = 1 := by
    rw [map_mul, map_inv, hpsi, inv_mul_cancel]
  obtain ⟨k, hk, hkk⟩ := (psiK_eq_one_iff K e _).mp h1
  have h3 : rhoK K (⟨x, hx⟩⁻¹ * ⟨x', hx'⟩) = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) :=
    (rhoK_eq_conj_iff K _ ⟨k, hk⟩).mpr (fun w => hkk w w.2)
  have h4 : Idx2.act (rhoK K (⟨x, hx⟩⁻¹ * ⟨x', hx'⟩)) = 1 := by
    rw [h3]; exact Idx2.act_inner _
  rw [map_mul, map_mul, map_inv, map_inv] at h4
  exact inv_mul_eq_one.mp h4

theorem psiK_dihedral {x v : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hv : v ∈ Subgroup.normalizer (K : Set G))
    (hw : (v * x) * v * (v * x)⁻¹ ∈ Subgroup.normalizer (K : Set G))
    (hp : psiK K ⟨x, hx⟩ * psiK K ⟨x, hx⟩ = 1) (hp1 : psiK K ⟨x, hx⟩ ≠ 1)
    (hq : psiK K ⟨v, hv⟩ * psiK K ⟨v, hv⟩ = 1) (hq1 : psiK K ⟨v, hv⟩ ≠ 1) :
    psiK K ⟨(v * x) * v * (v * x)⁻¹, hw⟩ = psiK K ⟨x, hx⟩ := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have hY : v * x ∈ Subgroup.normalizer (K : Set G) := mul_mem hv hx
  have key : psiK K ⟨v * x, hY⟩ = psiK K ⟨v, hv⟩ * psiK K ⟨x, hx⟩ := by
    rw [← map_mul]; rfl
  have e2 : (⟨(v * x) * v * (v * x)⁻¹, hw⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨v * x, hY⟩ * ⟨v, hv⟩ * (⟨v * x, hY⟩)⁻¹ := rfl
  rw [e2, map_mul, map_mul, map_inv, key]
  exact dihedral_idx2 (card_idx2_of_equiv_q8 e) _ _ hp hp1 hq hq1

theorem sq_inv_mul_mem_trivialOnQuot {x x' : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hx' : x' ∈ Subgroup.normalizer (K : Set G))
    (hact : psiK K ⟨x, hx⟩ = psiK K ⟨x', hx'⟩) (h4 : x ^ 4 = 1) (h4' : x' ^ 4 = 1)
    (hs : x * x ∉ trivialOnQuot K) (hs' : x' * x' ∉ trivialOnQuot K) :
    (x * x)⁻¹ * (x' * x') ∈ trivialOnQuot K := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  have hxx : x * x ∈ Subgroup.normalizer (K : Set G) := mul_mem hx hx
  have hxx' : x' * x' ∈ Subgroup.normalizer (K : Set G) := mul_mem hx' hx'
  have hmem : (x * x)⁻¹ * (x' * x') ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (inv_mem hxx) hxx'
  have hsq2 : (⟨x, hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = ⟨x * x, hxx⟩ :=
    Subtype.ext (pow_two x)
  have hsq2' : (⟨x', hx'⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = ⟨x' * x', hxx'⟩ :=
    Subtype.ext (pow_two x')
  have h4s : (⟨x, hx⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
    Subtype.ext (by simpa using h4)
  have h4s' : (⟨x', hx'⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 4 = 1 :=
    Subtype.ext (by simpa using h4')
  have hα4 : rhoK K ⟨x, hx⟩ ^ 4 = 1 := by rw [← map_pow, h4s, map_one]
  have hβ4 : rhoK K ⟨x', hx'⟩ ^ 4 = 1 := by rw [← map_pow, h4s', map_one]
  have hα2 : rhoK K ⟨x, hx⟩ ^ 2 ≠ 1 := by
    intro h
    apply hs
    apply mem_trivialOnQuot_of_rhoK_eq_one d hxx
    rw [← hsq2, map_pow]
    exact h
  have hβ2 : rhoK K ⟨x', hx'⟩ ^ 2 ≠ 1 := by
    intro h
    apply hs'
    apply mem_trivialOnQuot_of_rhoK_eq_one d hxx'
    rw [← hsq2', map_pow]
    exact h
  have hact' := act_rhoK_eq_of_psiK_eq d hx hx' hact
  have hsqeq := sq_eq_of_act_eq_of_equiv e (rhoK K ⟨x, hx⟩) (rhoK K ⟨x', hx'⟩) hact'
    hα4 hα2 hβ2
  apply mem_trivialOnQuot_of_rhoK_eq_one d hmem
  have e1 : (⟨(x * x)⁻¹ * (x' * x'), hmem⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      (⟨x * x, hxx⟩)⁻¹ * ⟨x' * x', hxx'⟩ := rfl
  rw [e1, map_mul, map_inv, ← hsq2, ← hsq2', map_pow, map_pow, hsqeq, inv_mul_cancel]

theorem conj_mem_sup_of_mem {y x : G} (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hyK' : y ∈ Subgroup.normalizer (K' : Set G)) (hx : x ∈ K ⊔ K') :
    y * x * y⁻¹ ∈ K ⊔ K' := by
  have hx' : x ∈ ((K ⊔ K' : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' d.late_K_le] at hx'
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hx'
  have h1 : y * k₁ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyK k₁).mp hk₁
  have h2 : y * k₂ * y⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp hyK' k₂).mp hk₂
  have e : y * (k₁ * k₂) * y⁻¹ = (y * k₁ * y⁻¹) * (y * k₂ * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

end Psi

section Conj

theorem exists_conj_pow_of_mul_eq {N : Subgroup G} {s v n : G} (hs : s * s = 1) (hv : v * v = 1)
    (hn : n ∈ N) (hodd : Odd (orderOf n)) (h : s * v = n) : ∃ m ∈ N, m⁻¹ * v * m = s := by
  obtain ⟨k, hk⟩ := exists_pow_conj_eq_of_odd_orderOf hs hv (by rw [h]; exact hodd)
  refine ⟨n ^ k, N.pow_mem hn k, ?_⟩
  rw [h] at hk
  have e : s = (n ^ k)⁻¹ * v * n ^ k := by rw [← hk]; group
  exact e.symm

theorem exists_conj_of_one_case {X : Subgroup G} {s v n y t : G} (hs : s * s = 1)
    (hv : v * v = 1) (hnX : n ∈ X) (hodd : Odd (orderOf n)) (hsv : s * v = n) (hy : y ∈ X)
    (hvt : v = y * t * y⁻¹) : ∃ x ∈ X, x * t * x⁻¹ = s := by
  obtain ⟨m, hm, hmv⟩ := exists_conj_pow_of_mul_eq hs hv hnX hodd hsv
  refine ⟨m⁻¹ * y, X.mul_mem (X.inv_mem hm) hy, ?_⟩
  rw [← hmv, hvt]
  group

theorem exists_conj_of_z_case {X : Subgroup G} {z s v n t y r : G} (hz : z * z = 1)
    (hs : s * s = 1) (hsz : s * z = z * s) (hv : v * v = 1)
    (hmz : ∀ m ∈ X, z * m = m * z) (hvz : v * z = z * v)
    (hnX : n ∈ X) (hodd : Odd (orderOf n)) (hsv : (s * z) * v = n)
    (hyr : y * r ∈ X) (hP : z * v = (y * r) * t * (y * r)⁻¹) :
    ∃ x ∈ X, x * t * x⁻¹ = s := by
  have hsz2 : (s * z) * (s * z) = 1 := by
    calc (s * z) * (s * z) = s * (z * s) * z := by group
      _ = s * (s * z) * z := by rw [hsz]
      _ = (s * s) * (z * z) := by group
      _ = 1 := by rw [hs, hz, mul_one]
  obtain ⟨m, hm, hmv⟩ := exists_conj_pow_of_mul_eq hsz2 hv hnX hodd hsv
  have hsE : s = m⁻¹ * (z * v) * m := by
    calc s = (m⁻¹ * v * m) * z := by rw [hmv, mul_assoc, hz, mul_one]
      _ = m⁻¹ * v * (m * z) := by group
      _ = m⁻¹ * v * (z * m) := by rw [← hmz m hm]
      _ = m⁻¹ * (v * z) * m := by group
      _ = m⁻¹ * (z * v) * m := by rw [hvz]
  refine ⟨m⁻¹ * (y * r), X.mul_mem (X.inv_mem hm) hyr, ?_⟩
  rw [hsE, hP]
  group

theorem conj_inv_pow (g x : G) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  induction n with
  | zero => group
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem pow_four_eq' (x : G) : x ^ 4 = x * x * (x * x) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem eq_mul_of_invol_mul_eq {s v n : G} (hs : s * s = 1) (h : s * v = n) : v = s * n := by
  rw [← h, ← mul_assoc, hs, one_mul]

end Conj

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
