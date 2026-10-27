module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Easy

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open scoped commutatorElement

theorem kaU1_inf_eq_bot_of_pPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X E : Subgroup G} (hX : IsPGroup p ↥X)
    (hEX : ∀ e ∈ E, e ∈ normalizer (X : Set G)) (hE : CFSG.pPrimeCore 2 ↥E = ⊥) :
    X ⊓ E = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  let N : Subgroup ↥E := (X ⊓ E).subgroupOf E
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, (g * n * g⁻¹ : ↥E).2⟩
    have := (Subgroup.mem_normalizer_iff.1 (hEX g g.2) n).1 hn.1
    simpa using this
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N = Nat.card ↥(X ⊓ E) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ E ≤ E)).toEquiv
    have h2 : IsPGroup p ↥(X ⊓ E) := hX.to_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    rw [h1, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hbot : N = ⊥ := (CFSG.pPrimeCore_eq_bot_iff.mp hE) N hN hcop
  rw [eq_bot_iff]
  intro y hy
  have hyN : (⟨y, hy.2⟩ : ↥E) ∈ N := Subgroup.mem_subgroupOf.mpr hy
  rw [hbot, Subgroup.mem_bot] at hyN
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hyN)

theorem kaU1_commute_of_inf_bot {G : Type*} [Group G] {X E : Subgroup G} (hXE : X ⊓ E = ⊥)
    (hEX : ∀ e ∈ E, e ∈ normalizer (X : Set G)) (hXE' : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    ∀ x ∈ X, ∀ e ∈ E, x * e = e * x := by
  intro x hx e he
  have h1 : e * x⁻¹ * e⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hEX e he) x⁻¹).1 (X.inv_mem hx)
  have h2 : x * (e * x⁻¹ * e⁻¹) ∈ X := X.mul_mem hx h1
  have h3 : x * e * x⁻¹ * e⁻¹ ∈ E := E.mul_mem (hXE' x hx e he) (E.inv_mem he)
  have h4 : x * e * x⁻¹ * e⁻¹ ∈ X ⊓ E := ⟨by simpa [mul_assoc] using h2, h3⟩
  rw [hXE, Subgroup.mem_bot] at h4
  calc x * e = (x * e * x⁻¹ * e⁻¹) * (e * x) := by group
    _ = e * x := by rw [h4, one_mul]

theorem kaU1_X0_hRp {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup (StatedProj (StatedSp 2 F))}
    (hX : IsPGroup p ↥X) (hXle : X ≤ X0 F)
    (hnorm : ∀ r ∈ X0 F, r ∈ normalizer (X : Set (StatedProj (StatedSp 2 F)))) : X = ⊥ := by
  have hE1 : X ⊓ E1 F = ⊥ :=
    kaU1_inf_eq_bot_of_pPrimeCore hp hp2 hX (fun e he => hnorm e (E1_le_X0 h2 he))
      (pPrimeCore_E1 h2 h4)
  have hE2 : X ⊓ E2 F = ⊥ :=
    kaU1_inf_eq_bot_of_pPrimeCore hp hp2 hX (fun e he => hnorm e (E2_le_X0 h2 he))
      (pPrimeCore_E2 h2 h4)
  have hc2 : ∀ x ∈ X, ∀ e ∈ E2 F, x * e = e * x :=
    kaU1_commute_of_inf_bot hE2 (fun e he => hnorm e (E2_le_X0 h2 he))
      (fun x hx e he => conj_mem_E2 h2 (hXle hx) he)
  rw [eq_bot_iff]
  intro x hx
  have hxE1 : x ∈ E1 F := mem_E1_of_commute_E2 h2 (hXle hx) (fun y hy => hc2 x hx y hy)
  have hx1 : x ∈ X ⊓ E1 F := ⟨hx, hxE1⟩
  rwa [hE1] at hx1

theorem kaU1_perfect_centralizer_T1 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) :
    ⁅centralizer ({T1 F} : Set (StatedSp 2 F)), centralizer ({T1 F} : Set (StatedSp 2 F))⁆ =
      centralizer ({T1 F} : Set (StatedSp 2 F)) := by
  have hrange : centralizer ({T1 F} : Set (StatedSp 2 F)) = (blkSL F).range := by
    ext x
    exact mem_centralizer_T1_iff h2
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl
      (Or.inr (exists_finset_card_four h4))
  have hprod : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Group.isPerfect_def, _root_.commutator_def, ← Subgroup.top_prod_top,
      Subgroup.commutator_prod_prod, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  rw [hrange]
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (blkSL F))

theorem kaSp4U1_thm : KASp4U1 := by
  intro F _ _ hodd h5
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have h4 : 4 ≤ Nat.card F := by omega
  refine kaAll_sp4_of_fix hodd (MulAut.conj (T1 F)) (MulAut.conj (u1 F)) ?_ ?_ ?_
  · intro g
    have hu : u1 F = proj 2 F (T1 F) := rfl
    rw [hu, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · rw [fixOf_conj]
    exact kaU1_perfect_centralizer_T1 h2 h4
  · intro p hp hp2 X hX hXle hnorm
    rw [fixOf_conj] at hXle hnorm
    exact kaU1_X0_hRp h2 h4 hp hp2 hX hXle hnorm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
