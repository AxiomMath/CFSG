module

import CFSG.GroupTheory.ThompsonAxBFaithful
import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.Quasithin
open CFSG.Quasithin.A4
open scoped commutatorElement

variable {Ω : Type*} [Group Ω]

private theorem normalizes_inf_centralizer_tab {V P N : Subgroup Ω}
    (hNV : N ≤ Subgroup.normalizer (V : Set Ω))
    (hPN : ⁅P, N⁆ ≤ Subgroup.centralizer (V : Set Ω)) :
    N ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω) := by
  refine Subgroup.le_normalizer_iff.mpr fun n hn w hw => ?_
  rw [Subgroup.mem_inf] at hw ⊢
  refine ⟨Subgroup.le_normalizer_iff.mp hNV n hn w hw.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hthis : ⁅y, n⁻¹⁆ ∈ Subgroup.centralizer (V : Set Ω) :=
    Subgroup.commutator_le.mp hPN y hy n⁻¹ (N.inv_mem hn)
  have hc : n⁻¹ * y * n * y⁻¹ ∈ Subgroup.centralizer (V : Set Ω) := by
    have h1 : ⁅n⁻¹, y⁆ ∈ Subgroup.centralizer (V : Set Ω) := by
      have := Subgroup.inv_mem _ hthis
      rwa [commutatorElement_inv] at this
    simpa [commutatorElement_def] using h1
  have hcw : w * (n⁻¹ * y * n * y⁻¹) = (n⁻¹ * y * n * y⁻¹) * w :=
    Subgroup.mem_centralizer_iff.mp hc w hw.1
  have hwy : w * y = y * w := (Subgroup.mem_centralizer_iff.mp hw.2 y hy).symm
  have hcy : (n⁻¹ * y * n * y⁻¹) * y = n⁻¹ * y * n := by group
  have hcn : w * (n⁻¹ * y * n) = (n⁻¹ * y * n) * w := by
    calc w * (n⁻¹ * y * n) = w * ((n⁻¹ * y * n * y⁻¹) * y) := by rw [hcy]
      _ = (w * (n⁻¹ * y * n * y⁻¹)) * y := by group
      _ = ((n⁻¹ * y * n * y⁻¹) * w) * y := by rw [hcw]
      _ = (n⁻¹ * y * n * y⁻¹) * (w * y) := by group
      _ = (n⁻¹ * y * n * y⁻¹) * (y * w) := by rw [hwy]
      _ = ((n⁻¹ * y * n * y⁻¹) * y) * w := by group
      _ = (n⁻¹ * y * n) * w := by rw [hcy]
  calc y * (n * w * n⁻¹) = n * ((n⁻¹ * y * n) * w) * n⁻¹ := by group
    _ = n * (w * (n⁻¹ * y * n)) * n⁻¹ := by rw [← hcn]
    _ = (n * w * n⁻¹) * y := by group

private theorem normalizer_inf_centralizer_tab {V P N : Subgroup Ω}
    (hNV : N ≤ Subgroup.normalizer (V : Set Ω))
    (hPN : ⁅P, N⁆ ≤ Subgroup.centralizer (V : Set Ω)) :
    N ≤ Subgroup.normalizer
      (((N ⊓ Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω)) : Subgroup Ω) :
        Set Ω) := by
  have hNW := normalizes_inf_centralizer_tab (V := V) (P := P) (N := N) hNV hPN
  have hNC : N ≤ Subgroup.normalizer
      ((Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω)) : Set Ω) :=
    fun n hn => mem_normalizer_centralizer (hNW hn)
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro d
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hdN, hdC⟩
    exact ⟨N.mul_mem (N.mul_mem hn hdN) (N.inv_mem hn),
      (Subgroup.mem_normalizer_iff.mp (hNC hn) d).mp hdC⟩
  · rintro ⟨hdN, hdC⟩
    have hmem : n⁻¹ * (n * d * n⁻¹) * n ∈ N :=
      N.mul_mem (N.mul_mem (N.inv_mem hn) hdN) hn
    have heq : n⁻¹ * (n * d * n⁻¹) * n = d := by group
    exact ⟨heq ▸ hmem, (Subgroup.mem_normalizer_iff.mp (hNC hn) d).mpr hdC⟩

private theorem isPGroup_autOn_tab {p : ℕ} {V P : Subgroup Ω}
    (hP : ∀ y ∈ P, ∃ k : ℕ, y ^ p ^ k ∈ Subgroup.centralizer (V : Set Ω)) :
    IsPGroup p (autOn P V) := by
  intro g
  obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨k, hk⟩ := hP z.1 (Subgroup.mem_subgroupOf.mp hz)
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hzg, ← map_pow, conjAct_eq_one_iff]
  simpa using hk

private theorem actionOn_fix_tab {V P N : Subgroup Ω}
    (hPV : P ≤ Subgroup.normalizer (V : Set Ω))
    (hNV : N ≤ Subgroup.normalizer (V : Set Ω))
    {a : Ω} (haN : a ∈ N)
    (haW : a ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω)) :
    ∀ w : V, (∀ a' ∈ autOn P V, a' w = w) →
      actionOn V N hNV ⟨a, haN⟩ w = w := by
  intro w hwfix
  have hW : (w : Ω) ∈ V ⊓ Subgroup.centralizer (P : Set Ω) := by
    refine ⟨w.2, ?_⟩
    change (w : Ω) ∈ Subgroup.centralizer (P : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hmem : actionOn V P hPV ⟨y, hy⟩ ∈ autOn P V :=
      (mem_autOn_iff hPV).mpr ⟨⟨y, hy⟩, rfl⟩
    have hv := congrArg Subtype.val (hwfix _ hmem)
    rw [actionOn_apply_coe] at hv
    have hyw : y * (w : Ω) = (w : Ω) * y := by
      calc y * (w : Ω) = (y * (w : Ω) * y⁻¹) * y := by group
        _ = (w : Ω) * y := by rw [hv]
    exact hyw
  have hcomm : a * (w : Ω) = (w : Ω) * a :=
    (Subgroup.mem_centralizer_iff.mp haW w hW).symm
  apply Subtype.ext
  rw [actionOn_apply_coe, hcomm]
  group

private theorem mem_centralizer_of_coprime_order_tab {p : ℕ} [Fact p.Prime] [Finite Ω]
    {V P N : Subgroup Ω} (hV : IsPGroup p V)
    (hPV : P ≤ Subgroup.normalizer (V : Set Ω))
    (hNV : N ≤ Subgroup.normalizer (V : Set Ω))
    (hP : ∀ y ∈ P, ∃ k : ℕ, y ^ p ^ k ∈ Subgroup.centralizer (V : Set Ω))
    (hPN : ⁅P, N⁆ ≤ Subgroup.centralizer (V : Set Ω))
    {a : Ω} (haN : a ∈ N)
    (haW : a ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (P : Set Ω) : Subgroup Ω) : Set Ω))
    (hcop : Nat.Coprime (orderOf a) p) :
    a ∈ Subgroup.centralizer (V : Set Ω) := by
  let b : MulAut V := actionOn V N hNV ⟨a, haN⟩
  have hA : IsPGroup p (autOn P V) := isPGroup_autOn_tab (V := V) (P := P) hP
  have hcent := autOn_le_centralizer_autOn (V := V) (X := P) (R := N) hPN
  have hb_mem : b ∈ autOn N V := (mem_autOn_iff hNV).mpr ⟨⟨a, haN⟩, rfl⟩
  have hAb : ∀ a' ∈ autOn P V, a' * b = b * a' :=
    fun a' ha' => Subgroup.mem_centralizer_iff.mp (hcent hb_mem) a' ha'
  have hdvd : orderOf b ∣ orderOf a := by
    have := orderOf_map_dvd (actionOn V N hNV) ⟨a, haN⟩
    simpa [b, Subgroup.orderOf_coe] using this
  have hbp : Nat.Coprime (orderOf b) p := hcop.coprime_dvd_left hdvd
  have hfix := actionOn_fix_tab (V := V) (P := P) (N := N) hPV hNV haN haW
  have hb1 : b = 1 := eq_one_of_forall_fixed_of_coprime hV hA hbp hAb hfix
  have hb1' : actionOn V N hNV ⟨a, haN⟩ = 1 := by simpa [b] using hb1
  simpa using (actionOn_eq_one_iff hNV ⟨a, haN⟩).mp hb1'

private theorem exists_pow_mem_centralizer_tab {p : ℕ} [Fact p.Prime] [Finite Ω]
    {V D : Subgroup Ω}
    (hD : ∀ x ∈ D, Nat.Coprime (orderOf x) p →
      x ∈ Subgroup.centralizer (V : Set Ω)) :
    ∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ Subgroup.centralizer (V : Set Ω) := by
  intro x hx
  obtain ⟨a, b, hab, hcomm, ⟨e, he⟩, hb, -, -⟩ :=
    CFSG.Quasithin.F6.exists_mul_eq_pPart (Fact.out : p.Prime) (⟨x, hx⟩ : D)
  refine ⟨e, ?_⟩
  have hbC : (b : Ω) ∈ Subgroup.centralizer (V : Set Ω) :=
    hD (b : Ω) b.2 (by simpa [Subgroup.orderOf_coe] using hb)
  have hpow : (⟨x, hx⟩ : D) ^ p ^ e = b ^ p ^ e := by
    rw [← hab, hcomm.mul_pow (p ^ e), he, one_mul]
  have hcoe := congrArg Subtype.val hpow
  rw [show x ^ p ^ e = (b : Ω) ^ p ^ e by simpa using hcoe]
  exact pow_mem hbC (p ^ e)

theorem inf_centralizer_le_centralizer_of_commutator_le {p : ℕ} [Fact p.Prime] [Finite Ω]
    {V P N : Subgroup Ω} (hV : IsPGroup p V) (hPV : P ≤ normalizer (V : Set Ω))
    (hNV : N ≤ normalizer (V : Set Ω))
    (hP : ∀ y ∈ P, ∃ k : ℕ, y ^ p ^ k ∈ centralizer (V : Set Ω))
    (hPN : ⁅P, N⁆ ≤ centralizer (V : Set Ω))
    (hN : ∀ D : Subgroup Ω, D ≤ N → N ≤ normalizer (D : Set Ω) →
      (∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ centralizer (V : Set Ω)) →
        D ≤ centralizer (V : Set Ω)) :
    N ⊓ centralizer ((V ⊓ centralizer (P : Set Ω) : Subgroup Ω) : Set Ω) ≤
      centralizer (V : Set Ω) := by
  let D : Subgroup Ω := N ⊓ centralizer
    ((V ⊓ centralizer (P : Set Ω) : Subgroup Ω) : Set Ω)
  have hD_le : D ≤ N := inf_le_left
  have hnorm : N ≤ normalizer (D : Set Ω) := by
    simpa [D] using normalizer_inf_centralizer_tab (V := V) (P := P) (N := N) hNV hPN
  have hpwr : ∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ centralizer (V : Set Ω) := by
    refine exists_pow_mem_centralizer_tab (V := V) (D := D) ?_
    intro x hx hcop
    exact mem_centralizer_of_coprime_order_tab (V := V) (P := P) (N := N)
      hV hPV hNV hP hPN hx.1 hx.2 hcop
  simpa [D] using hN D hD_le hnorm hpwr

end CFSG.GroupTheory
