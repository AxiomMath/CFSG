module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12SurvGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgFin

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem center_eq_bot_of_simple {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hns : ¬ Group.IsSolvable Y) : center Y = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center Y) with h | h
  · exact h
  · exfalso
    apply hns
    refine Group.isSolvable_of_comm (G := Y) (fun a b => ?_)
    have : a ∈ center Y := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

section Det

variable {K : Type} [Field K]

theorem det_monoGL (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hdet : ε 0 * ε 1 * ε 2 * ε 3 = 1) :
    ((monoGL g ε hε : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [coe_monoGL, det_mono_kperm, Fin.prod_univ_four, hdet]

theorem monoGL_mem_statedSL (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hdet : ε 0 * ε 1 * ε 2 * ε 3 = 1) : monoGL g ε hε ∈ StatedSL 4 K :=
  Subgroup.subset_closure (det_monoGL g ε hε hdet)

theorem mono_transpose_mul_self (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → K)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : (mono σ ε)ᵀ * mono σ ε = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mono, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : i = j
    · subst h
      simp only [↓reduceIte, Matrix.one_apply_eq]
      exact pm_mul_self (hε i)
    · have h' : ¬ σ i = σ j := fun h' => h (σ.injective h')
      simp [h', Matrix.one_apply_ne h]
  · intro k _ hk
    simp [hk]
  · simp

theorem mono_map_pow_three (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → K)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : (mono σ ε).map (· ^ (3 ^ 1)) = mono σ ε := by
  ext i j
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  by_cases h : i = σ j
  · simp only [h, ↓reduceIte]
    rcases hε j with h1 | h1 <;> rw [h1] <;> norm_num
  · simp [h]

theorem monoGL_mem_statedSU (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hdet : ε 0 * ε 1 * ε 2 * ε 3 = 1) : monoGL g ε hε ∈ StatedSU 4 (3 ^ 1) K :=
  Subgroup.subset_closure ⟨det_monoGL g ε hε hdet, by
    rw [coe_monoGL, mono_map_pow_three _ _ hε]
    exact mono_transpose_mul_self _ _ hε⟩

end Det

theorem not_sylCfgOf_L43 {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hns : ¬ Group.IsSolvable Y) (hM : LieModel Y .PSL 4 3 1) : ¬ SylCfgOf Y := by
  have hc : center Y = ⊥ := center_eq_bot_of_simple hs hns
  rcases hM with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hout := (linear_model_outer_two_part_bound Y 4 3 1 hcm).2.2.2.2 (by norm_num)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
    have h4 : 2 * 1 * Nat.gcd 4 (3 ^ 1 - 1) = 2 ^ 2 := by norm_num
    rw [h4] at hout
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
      rw [← Nat.card_eq_fintype_card, hK])
    exact not_sylCfgOf_of_stated hc hout (StatedSL 4 K) e fun g ε hε hdet =>
      monoGL_mem_statedSL g ε hε hdet
  all_goals exact absurd h0 (by norm_num)

theorem not_sylCfgOf_U43 {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hns : ¬ Group.IsSolvable Y) (hM : LieModel Y .PSU 4 3 1) : ¬ SylCfgOf Y := by
  have hc : center Y = ⊥ := center_eq_bot_of_simple hs hns
  rcases hM with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hout := (unitary_model_outer_two_part_bound Y 4 3 1 hcm).2.2.1
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
    have h8 : 2 * 1 * Nat.gcd 4 (3 ^ 1 + 1) = 2 ^ 3 := by norm_num
    rw [h8] at hout
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 3 := charP_of_card_eq_prime_pow (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hK, pow_one])
    exact not_sylCfgOf_of_stated hc (k := 3) (dvd_of_eq hout) (StatedSU 4 (3 ^ 1) K) e
      fun g ε hε hdet => monoGL_mem_statedSU g ε hε hdet
  all_goals exact absurd h0 (by norm_num)

theorem cellAbs_lieModel_L43 : CellAbs (fun (Y : Type) [Group Y] => LieModel Y .PSL 4 3 1) := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  exfalso
  obtain ⟨hs, hcfg⟩ := hfr.sylCfg hJ hnc
  exact not_sylCfgOf_L43 hs (not_isSolvable_quot_of_quasisimple hJ.1) hF hcfg

theorem cellAbs_lieModel_U43 : CellAbs (fun (Y : Type) [Group Y] => LieModel Y .PSU 4 3 1) := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hF
  exfalso
  obtain ⟨hs, hcfg⟩ := hfr.sylCfg hJ hnc
  exact not_sylCfgOf_U43 hs (not_isSolvable_quot_of_quasisimple hJ.1) hF hcfg

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
