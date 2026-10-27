module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical (radicalGroup
  radicalGroup_le mem_radicalGroup mem_radicalW radicalMatrix radicalMatrix_mulVec_single
  radicalMatrix_zero onesVec onesVec_apply card_radicalGroup)
open CFSG.ComponentClassification.OutcomeLocal (conj_mem_radicalGroup oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)

variable {m : ℕ} {F : Type} [Field F]

variable (m F) in
@[expose] noncomputable def extendOneHom :
    Matrix (Fin m) (Fin m) F →* Matrix (Fin (m + 1)) (Fin (m + 1)) F where
  toFun M := reindexAlgEquiv F F (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))
    (fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) F))
  map_one' := by rw [fromBlocks_one, map_one]
  map_mul' M N := by
    rw [← map_mul, fromBlocks_multiply]
    simp

variable (m F) in
@[expose] noncomputable def extendOneGL : GL (Fin m) F →* GL (Fin (m + 1)) F :=
  Units.map (extendOneHom m F)

theorem coe_extendOneGL (g : GL (Fin m) F) :
    (extendOneGL m F g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (g : Matrix (Fin m) (Fin m) F) 0 0 (1 : Matrix (Fin 1) (Fin 1) F)) := by
  change reindexAlgEquiv F F _ _ = _
  rw [coe_reindexAlgEquiv]

theorem extendOneGL_injective : Function.Injective (extendOneGL m F) := by
  intro g g' h
  have h' := congrArg (fun x : GL (Fin (m + 1)) F => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) h
  simp only [coe_extendOneGL] at h'
  exact Units.ext ((fromBlocks_inj.1 ((reindex _ _).injective h')).1)

theorem extendOneGL_mem {g : GL (Fin m) F}
    (hg : g ∈ matrixIsometryGroup (1 : Matrix (Fin m) (Fin m) F)) :
    extendOneGL m F g ∈ matrixIsometryGroup (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  rw [mem_matrixIsometryGroup, Matrix.mul_one] at hg ⊢
  rw [coe_extendOneGL, reindex_apply, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_transpose, fromBlocks_multiply, hg]
  simp

theorem extendOneGL_mulVec_single_last (g : GL (Fin m) F) :
    (extendOneGL m F g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ Pi.single (Fin.last m) 1 =
      Pi.single (Fin.last m) 1 := by
  rw [mulVec_single_one]
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
  rw [Matrix.col_apply, coe_extendOneGL, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    finSumFinEquiv_symm_last]
  rcases j with a | b
  · have hne : Fin.castAdd 1 a ≠ Fin.last m := fun h => by
      have h1 := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_last] at h1
      exact absurd h1 a.isLt.ne
    rw [fromBlocks_apply₁₂, Matrix.zero_apply, finSumFinEquiv_apply_left,
      Pi.single_eq_of_ne hne]
  · rw [fromBlocks_apply₂₂, Subsingleton.elim b 0, Matrix.one_apply_eq,
      finSumFinEquiv_apply_right]
    have : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext (by simp)
    rw [this, Pi.single_eq_same]

theorem card_radicalGroup_mul_dvd [Finite F] [CharP F 2] (hm : Even (m + 1)) :
    Nat.card (radicalGroup (K := F) (Fin.last m)) *
        Nat.card (matrixIsometryGroup (1 : Matrix (Fin m) (Fin m) F)) ∣
      Nat.card (matrixIsometryGroup (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by
  set O := matrixIsometryGroup (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hO
  set O' := matrixIsometryGroup (1 : Matrix (Fin m) (Fin m) F) with hO'
  set R₀ := radicalGroup (K := F) (Fin.last m) with hR₀
  have hR₀O : R₀ ≤ O := radicalGroup_le hm (Fin.last m)
  set R := R₀.subgroupOf O with hR
  have hRn : R.Normal := ⟨fun x hx g => by
    rw [hR, mem_subgroupOf] at hx ⊢
    exact conj_mem_radicalGroup hm g.2 hx⟩
  let ι : O' →* O :=
    ((extendOneGL m F).comp O'.subtype).codRestrict O fun g => extendOneGL_mem g.2
  have hιc : ∀ g : O', ((ι g : GL (Fin (m + 1)) F)) = extendOneGL m F g := fun _ => rfl
  let π : O' →* O ⧸ R := (QuotientGroup.mk' R).comp ι
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgR : ι g ∈ R := (QuotientGroup.eq_one_iff _).1 hg
    rw [hR, mem_subgroupOf, hιc] at hgR
    obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hm).1 hgR
    have he := extendOneGL_mulVec_single_last (F := F) (g : GL (Fin m) F)
    rw [hc, radicalMatrix_mulVec_single hv c] at he
    have hvc : v + c • onesVec = 0 := by
      have h1 : Pi.single (Fin.last m) 1 + (v + c • onesVec) =
          Pi.single (Fin.last m) (1 : F) + 0 := by
        rw [add_zero, ← add_assoc]
        exact he
      exact add_left_cancel h1
    have hvl : v (Fin.last m) = 0 := (mem_radicalW.1 hv).2
    have hc0 : c = 0 := by
      have h1 := congrFun hvc (Fin.last m)
      simp only [Pi.add_apply, Pi.smul_apply, onesVec_apply, smul_eq_mul, mul_one, hvl,
        zero_add, Pi.zero_apply] at h1
      exact h1
    have hv0 : v = 0 := by
      rw [hc0, zero_smul, add_zero] at hvc
      exact hvc
    have h1 : extendOneGL m F (g : GL (Fin m) F) = 1 := by
      apply Units.ext
      rw [hc, hv0, hc0, radicalMatrix_zero, Units.val_one]
    have h2 : (g : GL (Fin m) F) = 1 := extendOneGL_injective (h1.trans (map_one _).symm)
    exact Subtype.ext h2
  have h1 : Nat.card O' ∣ Nat.card (O ⧸ R) := Subgroup.card_dvd_of_injective π hπ
  have h2 : Nat.card O = Nat.card (O ⧸ R) * Nat.card R :=
    R.card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card R = Nat.card R₀ := Nat.card_congr (subgroupOfEquivOfLe hR₀O).toEquiv
  rw [h2, h3, mul_comm (Nat.card (O ⧸ R))]
  exact Nat.mul_dvd_mul_left _ h1

theorem card_matrixIsometryGroup_one_of_odd [CharP F 2] {n r : ℕ} (hr : n = 2 * r + 1) :
    Nat.card (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) F)) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedSp r F) := by
  obtain ⟨e⟩ := nonempty_altIsometry_mulEquiv_statedSp _
    (dotForm_restrict_isAlt (k := F) (n := n)) (dotForm_restrict_nondegenerate hr)
    (finrank_dotForm_ker hr)
  exact (Nat.card_congr (oneRestrictEquiv hr).toEquiv).trans (Nat.card_congr e.toEquiv)

theorem card_matrixIsometryGroup_blockSwapJ [CharP F 2] {n r : ℕ} (hr : n = 2 * r) :
    Nat.card (matrixIsometryGroup (UnitaryHigher.blockSwapJ n r : Matrix (Fin n) (Fin n) F)) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedSp r F) :=
  Nat.card_congr
    (CFSG.ComponentClassification.OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega)).toEquiv

theorem pow_dvd_card_matrixIsometryGroup_one [Finite F] [CharP F 2] {n r : ℕ} (hr : n = 2 * r)
    (hr1 : 1 ≤ r) :
    Nat.card F ^ (r ^ 2) ∣ Nat.card (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) F)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hms : m = 2 * s + 1 := by omega
  have hev : Even (m + 1) := ⟨s + 1, by omega⟩
  have hdvd := card_radicalGroup_mul_dvd (F := F) hev
  rw [card_radicalGroup hev, Nat.add_sub_cancel, card_matrixIsometryGroup_one_of_odd hms] at hdvd
  have hpow : Nat.card F ^ ((s + 1) ^ 2) = Nat.card F ^ m * Nat.card F ^ (s ^ 2) := by
    rw [← pow_add, hms]
    ring_nf
  rw [hpow]
  exact (Nat.mul_dvd_mul_left _ (pow_dvd_card_statedSp s)).trans hdvd

end CFSG.SeitzReduction.LinearPilot
