module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S4CEToolTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

section Flag

variable {G : Type*} [Group G]

theorem card_sup_of_le_normalizer_of_inf_eq_bot {N T : Subgroup G}
    (hT : T ≤ normalizer (N : Set G)) (hNT : N ⊓ T = ⊥) :
    Nat.card ↥(N ⊔ T) = Nat.card N * Nat.card T := by
  let f : N × T → ↥(N ⊔ T) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨n, t⟩ ⟨n', t'⟩ heq
      have e : (n : G) * t = n' * t' := congrArg Subtype.val heq
      have h1 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
        calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
          _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [e]
          _ = t' * (t : G)⁻¹ := by group
      have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
        mem_inf.mpr ⟨mul_mem (inv_mem n'.2) n.2, h1 ▸ mul_mem t'.2 (inv_mem t.2)⟩
      rw [hNT, mem_bot, inv_mul_eq_one] at hmem
      have hn : n = n' := Subtype.ext hmem.symm
      subst hn
      have ht : t = t' := Subtype.ext (mul_left_cancel e)
      rw [ht]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
      rw [coe_mul_of_right_le_normalizer_left N T hT] at hx'
      obtain ⟨n, hn, t, ht, rfl⟩ := hx'
      exact ⟨(⟨n, hn⟩, ⟨t, ht⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem card_iSup_eq_prod : ∀ {r : ℕ} (R F : Fin r → Subgroup G),
    (∀ i j : Fin r, i < j → R j ≤ normalizer (R i : Set G)) →
    (∀ i j : Fin r, i < j → R j ≤ F i) → (∀ i, R i ⊓ F i = ⊥) →
      Nat.card ↥(⨆ i, R i) = ∏ i, Nat.card (R i)
  | 0, R, F, _, _, _ => by simp
  | r + 1, R, F, hN, hF, hRF => by
    set T : Subgroup G := ⨆ i : Fin r, R i.succ
    have hsup : (⨆ i, R i) = R 0 ⊔ T := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact le_sup_of_le_right (le_iSup (fun j : Fin r => R j.succ) j)
      · exact sup_le (le_iSup R 0) (iSup_le fun j => le_iSup R j.succ)
    have hTN : T ≤ normalizer (R 0 : Set G) := iSup_le fun j => hN 0 j.succ (Fin.succ_pos j)
    have hTF : T ≤ F 0 := iSup_le fun j => hF 0 j.succ (Fin.succ_pos j)
    have hinf : R 0 ⊓ T = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hTF).trans (hRF 0).le)
    have hIH := card_iSup_eq_prod (fun j : Fin r => R j.succ) (fun j : Fin r => F j.succ)
      (fun i j hij => hN _ _ (Fin.succ_lt_succ_iff.mpr hij))
      (fun i j hij => hF _ _ (Fin.succ_lt_succ_iff.mpr hij)) (fun i => hRF i.succ)
    rw [hsup, Fin.prod_univ_succ, card_sup_of_le_normalizer_of_inf_eq_bot hTN hinf, hIH]

end Flag

section Roots

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] def eichlerRoot (Q : QuadraticForm (ZMod 2) V) (e : V) (D : Submodule (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∃ d ∈ D, polar Q e d = 0 ∧ eichler Q e d = g}
  mul_mem' := by
    rintro _ _ ⟨d, hd, hed, rfl⟩ ⟨d', hd', hed', rfl⟩
    exact ⟨d + d', D.add_mem hd hd', by rw [polar_add_right, hed, hed', add_zero],
      (eichler_mul hed hed').symm⟩
  one_mem' := ⟨0, D.zero_mem, by simp, eichler_zero_right Q e⟩
  inv_mem' := by
    rintro _ ⟨d, hd, hed, rfl⟩
    exact ⟨-d, D.neg_mem hd, by rw [polar_neg_right, hed, neg_zero], (eichler_inv hed).symm⟩

@[expose] def flagRoot (P : ℕ → HypPair Q) (i : ℕ) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  eichlerRoot Q (P i).e (tailSpace P (i + 1))

variable {P : ℕ → HypPair Q} {r : ℕ}

theorem mem_flagRoot {i : ℕ} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ flagRoot P i ↔ ∃ d ∈ tailSpace P (i + 1), eichler Q (P i).e d = g := by
  refine ⟨fun ⟨d, hd, _, hg⟩ => ⟨d, hd, hg⟩, fun ⟨d, hd, hg⟩ => ⟨d, hd, ?_, hg⟩⟩
  exact polar_e_tailSpace (Nat.lt_succ_self i) hd

theorem flagRoot_le_pointRadical (i : ℕ) : flagRoot P i ≤ pointRadical Q (P i).e := by
  rintro _ ⟨d, -, hd, rfl⟩
  exact eichler_mem_pointRadical (P i).Q_e hd

theorem flagRoot_le_orthogonalGroup (i : ℕ) :
    flagRoot P i ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨d, -, -, rfl⟩
  exact eichler_mem_orthogonalGroup Q _ d

section Family

variable (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
include hP

theorem flagRoot_apply_e {i j : ℕ} (hij : i < j) (hj : j < r) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ flagRoot P j) : g (P i).e = (P i).e := by
  obtain ⟨d, hd, rfl⟩ := mem_flagRoot.mp hg
  exact eichler_apply_of_polar_eq_zero (hP i j (by omega) hj (by omega)).ee
    (polar_e_tailSpace (by omega) hd)

theorem flagRoot_apply_f {i j : ℕ} (hij : i < j) (hj : j < r) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ flagRoot P j) : g (P i).f = (P i).f := by
  obtain ⟨d, hd, rfl⟩ := mem_flagRoot.mp hg
  exact eichler_apply_of_polar_eq_zero (hP i j (by omega) hj (by omega)).fe
    (polar_f_tailSpace (by omega) hd)

theorem conj_mem_flagRoot {i j : ℕ} (hij : i < j) (hj : j < r) {g x : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ flagRoot P j) (hx : x ∈ flagRoot P i) : g * x * g⁻¹ ∈ flagRoot P i := by
  obtain ⟨d, hd, rfl⟩ := mem_flagRoot.mp hx
  have hgO := flagRoot_le_orthogonalGroup j hg
  rw [eichler_conj hgO, flagRoot_apply_e hP hij hj hg]
  refine mem_flagRoot.mpr ⟨g d, apply_mem_tailSpace hgO (fun k hk => ?_) hd, rfl⟩
  exact ⟨flagRoot_apply_e hP (by omega) hj hg, flagRoot_apply_f hP (by omega) hj hg⟩

theorem flagRoot_le_normalizer {i j : ℕ} (hij : i < j) (hj : j < r) :
    flagRoot P j ≤ normalizer (flagRoot P i : Set (V ≃ₗ[ZMod 2] V)) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_flagRoot hP hij hj hg, fun hx => ?_⟩
  have := conj_mem_flagRoot hP hij hj (inv_mem hg) hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

end Family

theorem eichler_apply_f {i : ℕ} {d : V} (hd : d ∈ tailSpace P (i + 1)) :
    eichler Q (P i).e d (P i).f = (P i).f + d - Q d • (P i).e := by
  rw [eichler_apply (P i).Q_e (polar_e_tailSpace (Nat.lt_succ_self i) hd), (P i).polar_fe,
    polar_f_tailSpace (Nat.lt_succ_self i) hd]
  module

theorem eq_of_eichler_eq {i : ℕ} {d d' : V} (hd : d ∈ tailSpace P (i + 1))
    (hd' : d' ∈ tailSpace P (i + 1)) (h : eichler Q (P i).e d = eichler Q (P i).e d') :
    d = d' := by
  have h1 := LinearEquiv.congr_fun h (P i).f
  rw [eichler_apply_f hd, eichler_apply_f hd'] at h1
  have h2 : d - d' = (Q d - Q d') • (P i).e := by
    linear_combination (norm := module) h1
  have h3 := congrArg (polar Q (P i).f) h2
  rw [polar_sub_right, polar_f_tailSpace (Nat.lt_succ_self i) hd,
    polar_f_tailSpace (Nat.lt_succ_self i) hd', polar_smul_right_eq, (P i).polar_fe, mul_one,
    sub_zero, eq_comm, sub_eq_zero] at h3
  rw [h3, sub_self, zero_smul, sub_eq_zero] at h2
  exact h2

theorem flagRoot_inf_stabIn (i : ℕ) : flagRoot P i ⊓ stabIn ⊤ (P i).f = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg, -, hgf⟩
  obtain ⟨d, hd, rfl⟩ := mem_flagRoot.mp hg
  rw [eichler_apply_f hd] at hgf
  have h2 : d = Q d • (P i).e := by linear_combination (norm := module) hgf
  have h3 := congrArg (polar Q (P i).f) h2
  rw [polar_f_tailSpace (Nat.lt_succ_self i) hd, polar_smul_right_eq, (P i).polar_fe,
    mul_one] at h3
  rw [← h3, zero_smul] at h2
  rw [h2, eichler_zero_right]
  exact one_mem _

theorem card_flagRoot (i : ℕ) : Nat.card (flagRoot P i) = Nat.card (tailSpace P (i + 1)) := by
  set φ : tailSpace P (i + 1) → flagRoot P i := fun d =>
    ⟨eichler Q (P i).e d, mem_flagRoot.mpr ⟨d, d.2, rfl⟩⟩ with hφ
  have hbij : Function.Bijective φ := by
    refine ⟨fun d d' hdd => Subtype.ext (eq_of_eichler_eq d.2 d'.2 (congrArg Subtype.val hdd)),
      ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨d, hd, rfl⟩ := mem_flagRoot.mp hg
    exact ⟨⟨d, hd⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

theorem card_tailSpace [FiniteDimensional (ZMod 2) V] (j : ℕ) :
    Nat.card (tailSpace P j) = 2 ^ finrank (ZMod 2) (tailSpace P j) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_tailSpace [FiniteDimensional (ZMod 2) V]
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) {j : ℕ} (hj : j ≤ r) :
    finrank (ZMod 2) (tailSpace P j) + 2 * j = finrank (ZMod 2) V := by
  induction j with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero]
    exact finrank_top (ZMod 2) V
  | succ j ih =>
    have h := CFSG.LocalAnalysis.ComponentInitial.finrank_inf_perp_add_two (P j)
      (e_mem_tailSpace hP le_rfl (by omega)) (f_mem_tailSpace hP le_rfl (by omega))
    rw [← tailSpace_succ] at h
    have := ih (by omega)
    omega

theorem sum_range_two_mul_sub (r : ℕ) :
    ∑ i ∈ Finset.range r, (2 * r - 2 * i) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ', Finset.sum_congr rfl
      (fun i _ => show 2 * (r + 1) - 2 * (i + 1) = 2 * r - 2 * i by omega), ih,
      Nat.mul_zero, Nat.sub_zero]
    ring

theorem prod_card_flagRoot [FiniteDimensional (ZMod 2) V]
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hdim : finrank (ZMod 2) V = 2 * (r + 1)) :
    ∏ i : Fin r, Nat.card (flagRoot P i) = 2 ^ (r * (r + 1)) := by
  have hc : ∀ i : Fin r, Nat.card (flagRoot P i) = 2 ^ (2 * r - 2 * (i : ℕ)) := by
    intro i
    rw [card_flagRoot, card_tailSpace]
    congr 1
    have := finrank_tailSpace hP (j := i + 1) (by omega)
    omega
  rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i => 2 * r - 2 * i) r, sum_range_two_mul_sub]

theorem card_iSup_flagRoot [FiniteDimensional (ZMod 2) V]
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hdim : finrank (ZMod 2) V = 2 * (r + 1)) :
    Nat.card ↥(⨆ i : Fin r, flagRoot P i) = 2 ^ (r * (r + 1)) := by
  rw [card_iSup_eq_prod (fun i : Fin r => flagRoot P i) (fun i : Fin r => stabIn ⊤ (P i).f)
    (fun i j hij => flagRoot_le_normalizer hP hij j.2)
    (fun i j hij g hg => ⟨mem_top g, flagRoot_apply_f hP hij j.2 hg⟩)
    (fun i => flagRoot_inf_stabIn i)]
  exact prod_card_flagRoot hP hdim

end Roots

end CFSG.LargeExtraspecial.S4
