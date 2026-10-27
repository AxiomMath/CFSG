module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E elt_zero)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

section RootElements

variable {F : Type} [Field F] {n : ℕ}

theorem diagSp_eq_equivStatedSp_diagonal (s : Fin n → Fˣ) :
    diagSp F n s = equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal s) := by
  apply mat_injective
  rw [mat_diagSp, CFSG.LieType.Universal.Symplectic.SpExtras.mat_equiv_diagonal]
  rfl

theorem diagSp_mul_elt_mul_inv (s : Fin n → Fˣ) (r : RootSubgroupIndex n) (c : F) :
    diagSp F n s * elt r c * (diagSp F n s)⁻¹ = elt r ((r.character s : F) * c) := by
  rw [diagSp_eq_equivStatedSp_diagonal, elt, elt, ← map_mul, ← map_inv, ← map_mul,
    TauCeti.GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv]
  rfl

theorem rootTorusHom_mul_elt_difference_mul_inv {i j : Fin n} (hij : i ≠ j) (κ : Fˣ) (c : F) :
    rootTorusHom F n i κ * elt (.difference i j hij) c * (rootTorusHom F n i κ)⁻¹ =
      elt (.difference i j hij) ((κ : F) * c) := by
  rw [rootTorusHom_apply, diagSp_mul_elt_mul_inv,
    TauCeti.GLSymplecticFin.RootSubgroupIndex.character_difference, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne hij.symm, inv_one, mul_one]

theorem elt_difference_eq_conj {i j : Fin n} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    elt (.difference i j hij) c =
      rootTorusHom F n i (Units.mk0 c hc) * elt (.difference i j hij) 1 *
        (rootTorusHom F n i (Units.mk0 c hc))⁻¹ := by
  rw [rootTorusHom_mul_elt_difference_mul_inv, Units.val_mk0, mul_one]

theorem rootTorusHom_mem_spBlock_singleton (i : Fin n) (κ : Fˣ) :
    rootTorusHom F n i κ ∈ spBlock F {i} := by
  rw [spBlock_singleton]
  exact rootTorusSp_le_longRootSp2 i (rootTorusHom_mem_rootTorusSp i κ)

theorem E_map {K : Type} [Field K] (ι : K →+* F) (r : RootSubgroupIndex n) :
    (E K r).map ι = E F r := by
  ext a b
  rw [Matrix.map_apply]
  cases r <;> simp only [E, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply] <;>
    split_ifs <;> simp

theorem spFieldMap_elt {K : Type} [Field K] (ι : K →+* F) (r : RootSubgroupIndex n) (c : K) :
    spFieldMap n ι (elt r c) = elt r (ι c) := by
  apply mat_injective
  rw [mat_spFieldMap, mat_elt, mat_elt, Matrix.map_add _ (map_add ι),
    Matrix.map_one _ (map_zero ι) (map_one ι),
    ← E_map ι r]
  congr 1
  ext a b
  simp

end RootElements

section Levi

variable {F : Type} [Field F] {n : ℕ}

theorem spBlock_inf_spBlock (N M : Finset (Fin n)) :
    spBlock F N ⊓ spBlock F M = spBlock F (N ∩ M) := by
  ext x
  rw [mem_inf, spBlock, spBlock, spBlock, mem_suppGroup_iff (parClosed_planeCoords N),
    mem_suppGroup_iff (parClosed_planeCoords M), mem_suppGroup_iff (parClosed_planeCoords _)]
  simp only [mem_planeCoords, Finset.mem_inter, not_and_or]
  constructor
  · rintro ⟨h1, h2⟩ t ht r
    rcases ht with ht | ht
    · exact h1 t ht r
    · exact h2 t ht r
  · intro h
    exact ⟨fun t ht r => h t (Or.inl ht) r, fun t ht r => h t (Or.inr ht) r⟩

theorem perfectCore_spBlock_inf_centralizer_nsElt [Finite F] [CharP F 2] (N : Finset (Fin n))
    (l : Fin n)
    (hperf : ⁅spBlock F (N ∩ {l}ᶜ), spBlock F (N ∩ {l}ᶜ)⁆ = spBlock F (N ∩ {l}ᶜ)) :
    perfectCore (spBlock F N ⊓ centralizer ({nsElt l} : Set (StatedSp n F))) =
      spBlock F (N ∩ {l}ᶜ) := by
  set H := spBlock F N ⊓ centralizer ({nsElt l} : Set (StatedSp n F)) with hH
  have hcomm : ⁅H, H⁆ ≤ spBlock F (N ∩ {l}ᶜ) := by
    rw [← spBlock_inf_spBlock, spBlock_compl_singleton]
    refine commutator_le.2 fun g hg g' hg' => mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg.1 hg'.1) (inv_mem hg.1)) (inv_mem hg'.1)
    · rw [commutatorElement_def]
      exact commutator_mem_complSp_of_commute_nsElt (mem_centralizer_singleton_iff.1 hg.2)
        (mem_centralizer_singleton_iff.1 hg'.2)
  have hle : spBlock F (N ∩ {l}ᶜ) ≤ H := by
    rw [← spBlock_inf_spBlock, spBlock_compl_singleton]
    exact inf_le_inf_left _ fun y hy => mem_centralizer_nsElt_of_mem_complSp hy
  apply le_antisymm
  · calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := hcomm
  · exact le_perfectCore_of_perfect hle hperf

end Levi

section Generation

variable {F : Type} [Field F] {n : ℕ}

theorem spBlock_pair_le_sup {a b : Fin n} (hab : a ≠ b) {H : Subgroup (StatedSp n F)}
    (h1 : elt (.difference a b hab) 1 ∈ H) (h2 : elt (.difference b a hab.symm) 1 ∈ H) :
    spBlock F ({a, b} : Finset (Fin n)) ≤ spBlock F {a} ⊔ spBlock F {b} ⊔ H := by
  classical
  set σ : Fin 2 → Fin n := ![a, b] with hσ
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hσinj : Function.Injective σ := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd hxy hab
    · exact absurd hxy hab.symm
    · rfl
  have hσrange : Set.range σ = (({a, b} : Finset (Fin n)) : Set (Fin n)) := by
    ext x
    rw [Set.mem_range, Fin.exists_fin_two, hσ0, hσ1, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  have hblock : spBlock F ({a, b} : Finset (Fin n)) = (spEmbed (K := F) σ hσinj).range := by
    rw [range_spEmbed, range_sumMap_eq_planeCoords hσrange, spBlock]
  rw [hblock]
  rintro _ ⟨g, rfl⟩
  set M := spBlock F {a} ⊔ spBlock F {b} ⊔ H with hM
  have hA : spBlock F {a} ≤ M := le_sup_left.trans le_sup_left
  have hB : spBlock F {b} ≤ M := le_sup_right.trans le_sup_left
  have hH : H ≤ M := le_sup_right
  have hshort : ∀ (i j : Fin n) (hij : i ≠ j), spBlock F {i} ≤ M →
      elt (.difference i j hij) 1 ∈ M → ∀ c : F, elt (.difference i j hij) c ∈ M := by
    intro i j hij hi h1 c
    by_cases hc : c = 0
    · rw [hc, elt_zero]
      exact one_mem M
    · rw [elt_difference_eq_conj hij hc]
      have hd := hi (rootTorusHom_mem_spBlock_singleton i (Units.mk0 c hc))
      exact mul_mem (mul_mem hd h1) (inv_mem hd)
  have htop : M.comap (spEmbed (K := F) σ hσinj) = ⊤ := by
    refine eq_top_of_adjacent_of_long_statedSp _ (0 : Fin 2) (fun i j hij c _ => ?_)
      (fun c => ?_) (fun c => ?_)
    · rw [mem_comap, spEmbed_elt_difference]
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hshort a b hab hA (hH h1) c
      · exact hshort b a hab.symm hB (hH h2) c
      · exact absurd rfl hij
    · rw [mem_comap, spEmbed_elt_positiveLong]
      exact hA (elt_positiveLong_mem_spBlock (Finset.mem_singleton_self _) c)
    · rw [mem_comap, spEmbed_elt_negativeLong]
      exact hA (elt_negativeLong_mem_spBlock (Finset.mem_singleton_self _) c)
  have hg : g ∈ M.comap (spEmbed (K := F) σ hσinj) := by
    rw [htop]
    exact mem_top g
  exact hg

theorem spBlock_pair_le_sup_map_spFieldMap {K : Type} [Field K] (ι : K →+* F) {a b : Fin n}
    (hab : a ≠ b) :
    spBlock F ({a, b} : Finset (Fin n)) ≤ spBlock F {a} ⊔ spBlock F {b} ⊔
      (spBlock K ({a, b} : Finset (Fin n))).map (spFieldMap n ι) := by
  refine spBlock_pair_le_sup hab ?_ ?_
  · refine ⟨elt (.difference a b hab) 1, elt_difference_mem_spBlock hab (by simp) (by simp) 1, ?_⟩
    rw [spFieldMap_elt, map_one]
  · refine ⟨elt (.difference b a hab.symm) 1,
      elt_difference_mem_spBlock hab.symm (by simp) (by simp) 1, ?_⟩
    rw [spFieldMap_elt, map_one]

end Generation

end CFSG.SeitzReduction.SymplecticPilot
