module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidEich
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_add_bar_eq {c : K} (hc : h.bar c = c) : ∃ d, d + h.bar d = c := by
  obtain ⟨d, hd⟩ := h.traceLin_surjective ⟨c, (h.mem_fixedField).mpr hc⟩
  exact ⟨d, congrArg Subtype.val hd⟩

theorem bar_sum_norm (a : Fin ε → K) :
    h.bar (∑ k, h.bar (a k) * a k) = ∑ k, h.bar (a k) * a k := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, h.bar_bar, mul_comm]

theorem exists_valid (a : Fin ε → K) : ∃ c, c + h.bar c = ∑ k, h.bar (a k) * a k :=
  exists_add_bar_eq h (bar_sum_norm h a)

theorem coe_inv_hypSU (x : hypSU h 1 ε) :
    (((x⁻¹ : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
      ((x : GL (HypIndex 1 ε) K)⁻¹ : GL (HypIndex 1 ε) K) := rfl

theorem eich_zero_mem_commutator [CharP K 2] (hε : 1 ≤ ε) {d : K}
    (hd : d + h.bar d = ∑ k, h.bar ((0 : Fin ε → K) k) * (0 : Fin ε → K) k) :
    eich h hd ∈ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ := by
  have hdσ : h.bar d = d := by
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero] at hd
    exact (eq_of_add_eq_zero_two hd).symm
  obtain ⟨s, hs⟩ := exists_add_bar_eq h hdσ
  set k₀ : Fin ε := ⟨0, hε⟩
  obtain ⟨c₁, hc₁⟩ := exists_valid h (Pi.single k₀ 1)
  obtain ⟨c₂, hc₂⟩ := exists_valid h (Pi.single k₀ s)
  have hmem := Subgroup.commutator_mem_commutator (eich_mem_stabE h hc₁) (eich_mem_stabE h hc₂)
  convert hmem using 1
  refine Subtype.ext (Units.ext ?_)
  simp only [commutatorElement_def, Subgroup.coe_mul, Units.val_mul, coe_inv_hypSU, coe_eich]
  change eichM h.bar 0 d = eichM h.bar (Pi.single k₀ 1) c₁ * eichM h.bar (Pi.single k₀ s) c₂ *
    eichM h.bar (Pi.single k₀ 1) (c₁ + _) * eichM h.bar (Pi.single k₀ s) (c₂ + _)
  rw [eichM_commutator]
  congr 1
  rw [← hs]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem exists_single_mem_commutator [CharP K 2] (hε : 2 ≤ ε) (k : Fin ε) (t : K) :
    ∃ g : hypSU h 1 ε, g ∈ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ ∧ ∃ d,
      ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
        eichM h.bar (Pi.single k t) d := by
  have : Finite K := h.finite
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one (f := f) h.card_eq_sq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  obtain ⟨k', hk'⟩ : ∃ k' : Fin ε, k' ≠ k := by
    by_cases hk : k = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [hk] at h'; simp [Fin.ext_iff] at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => hk h'.symm⟩
  set dv : Fin ε → K := fun i => (if i = k then ζ else 1) * (if i = k' then ζ⁻¹ else 1)
  have hdv : ∀ i, dv i ^ 2 ^ f * dv i = 1 := by
    intro i
    have hinv : (ζ ^ 2 ^ f)⁻¹ * ζ⁻¹ = 1 := by rw [← mul_inv, hζ, inv_one]
    simp only [dv, mul_pow]
    split_ifs <;> simp [hζ, hinv, mul_mul_mul_comm]
  have hdet : ∏ i, dv i = 1 := by
    simp only [dv, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact mul_inv_cancel₀ hζ0
  obtain ⟨C, hC⟩ := exists_diagonal_mem (f := f) hdv hdet
  have hCu := ((mem_unitarySU_iff h).mp C.2).2
  have hCinv : (((C : GL (Fin ε) K)⁻¹ : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) =
      ((C : GL (Fin ε) K).val.map h.bar)ᵀ := Units.inv_eq_of_mul_eq_one_left hCu
  set s := t / (ζ + 1) with hs
  have hζ1' : ζ + 1 ≠ 0 := fun h' => hζ1 (eq_of_add_eq_zero_two h')
  obtain ⟨c, hc⟩ := exists_valid h (Pi.single k s)
  have hmem := Subgroup.commutator_mem_commutator (blkZHom_mem_stabE h C) (eich_mem_stabE h hc)
  have key : (((⁅blkZHom h C, eich h hc⁆ : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
      Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = eichM h.bar (Pi.single k t)
        ((∑ m, h.bar ((Pi.single k s : Fin ε → K) m) * (Pi.single k s : Fin ε → K) m) +
          ∑ m, h.bar (((C : GL (Fin ε) K).val *ᵥ Pi.single k s) m) *
            (Pi.single k s : Fin ε → K) m) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Units.val_mul, coe_inv_hypSU]
    change blkZM (C : GL (Fin ε) K).val * eichM h.bar (Pi.single k s) c *
      blkZM (((C : GL (Fin ε) K)⁻¹ : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *
        eichM h.bar (Pi.single k s) (c + _) = _
    rw [hCinv, blkZM_eichM_commutator hCu]
    congr 1
    rw [hC, diagonal_mulVec_single, ← Pi.single_add]
    congr 1
    simp only [dv, ↓reduceIte, Ne.symm hk', mul_one, hs]
    field_simp
  exact ⟨_, hmem, _, key⟩

theorem exists_eichM_mem_commutator [CharP K 2] (hε : 2 ≤ ε) (a : Fin ε → K) :
    ∃ g : hypSU h 1 ε, g ∈ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ ∧ ∃ d,
      ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = eichM h.bar a d := by
  rw [← Finset.univ_sum_single a]
  refine Finset.sum_induction _ (fun b => ∃ g : hypSU h 1 ε,
      g ∈ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ ∧ ∃ d,
        ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
          eichM h.bar b d) ?_ ?_ ?_
  · rintro b b' ⟨g, hg, d, hgd⟩ ⟨g', hg', d', hgd'⟩
    exact ⟨g * g', mul_mem hg hg', _, by rw [Subgroup.coe_mul, Units.val_mul, hgd, hgd', eichM_mul]⟩
  · exact ⟨1, one_mem _, 0, by rw [eichM_zero]; rfl⟩
  · intro k _
    exact exists_single_mem_commutator h hε k (a k)

theorem eich_mem_commutator [CharP K 2] (hε : 2 ≤ ε) {a : Fin ε → K} {c : K}
    (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) :
    eich h hc ∈ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ := by
  obtain ⟨g, hg, d, hgd⟩ := exists_eichM_mem_commutator h hε a
  have hd : d + h.bar d = ∑ k, h.bar (a k) * a k := by
    have := (mem_hypSU.mp g.2).1
    rw [hgd] at this
    exact eichM_valid this
  have h0 : (c + d) + h.bar (c + d) =
      ∑ k, h.bar ((0 : Fin ε → K) k) * (0 : Fin ε → K) k := by
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, map_add]
    rw [show c + d + (h.bar c + h.bar d) = (c + h.bar c) + (d + h.bar d) by ring, hc, hd,
      CharTwo.add_self_eq_zero]
  have hmem := mul_mem hg (eich_zero_mem_commutator h (by omega) h0)
  convert hmem using 1
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, hgd, coe_eich, coe_eich, eichM_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  congr 1
  · simp
  · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    linear_combination (-d) * h2

theorem stabE_le_commutator [CharP K 2] (hf : 2 ≤ f) (hε : 2 ≤ ε) :
    stabE (ε := ε) h ≤ ⁅stabE (ε := ε) h, stabE (ε := ε) h⁆ := by
  have : Finite K := h.finite
  intro g hg
  obtain ⟨a, c, hc, C, rfl⟩ := exists_eq_eich_mul_blkZHom h hg
  refine mul_mem (eich_mem_commutator h hε hc) ?_
  have hSU := commutator_statedSU (f := f) h.card_eq_sq hf hε
  have hC : C ∈ commutator (StatedSU ε (2 ^ f) K) := hSU ▸ Subgroup.mem_top C
  have hmem := Subgroup.mem_map_of_mem (blkZHom h) hC
  rw [commutator_def, Subgroup.map_commutator] at hmem
  have hle : (⊤ : Subgroup (StatedSU ε (2 ^ f) K)).map (blkZHom h) ≤ stabE h := by
    rintro _ ⟨C', -, rfl⟩
    exact blkZHom_mem_stabE h C'
  exact Subgroup.commutator_mono hle hle hmem

end CFSG.ComponentClassification.RankTwoClassical.URigid
