module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Lift

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley
open scoped commutatorElement

section SL2

variable {K : Type} [Field K]

@[expose] def c3SL : SL2 K := ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem coe_c3SL : ((c3SL : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, -1] :=
  rfl

theorem c3SL_pow_three : (c3SL : SL2 K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_c3SL, Matrix.SpecialLinearGroup.coe_one, pow_three',
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext k l
  fin_cases k <;> fin_cases l <;> norm_num

theorem not_commute_c3SL_uSL : ¬ Commute (c3SL : SL2 K) (uSL 1) := by
  intro hc
  have h : ((c3SL * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((uSL 1 * c3SL : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    rw [hc.eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_c3SL, coe_uSL,
    Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  exact zero_ne_one (by simpa using h : (0 : K) = 1)

theorem coe_comm_uSL_WSL :
    ((⁅(uSL 1 : SL2 K), WSL⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![2, 1; 1, 1] := by
  rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, coe_uSL, coe_WSL, Matrix.adjugate_fin_two_of,
    Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext k l
  fin_cases k <;> fin_cases l <;> norm_num

theorem comm_uSL_WSL_pow_three [CharP K 2] : (⁅(uSL 1 : SL2 K), WSL⁆ : SL2 K) ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_comm_uSL_WSL, Matrix.SpecialLinearGroup.coe_one,
    pow_three', Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext k l
  fin_cases k <;> fin_cases l <;> simp <;>
    first | linear_combination | linear_combination h2 | linear_combination 2 * h2 |
      linear_combination 3 * h2 | linear_combination 4 * h2 | linear_combination 5 * h2 |
      linear_combination 6 * h2

theorem not_commute_comm_uSL_WSL [CharP K 2] :
    ¬ Commute (⁅(uSL 1 : SL2 K), WSL⁆ : SL2 K) WSL := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro hc
  have h : ((⁅(uSL 1 : SL2 K), WSL⁆ * WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((WSL * ⁅(uSL 1 : SL2 K), WSL⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    rw [hc.eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_comm_uSL_WSL,
    coe_WSL, Matrix.mul_fin_two, Matrix.mul_fin_two] at h
  have h' : (2 : K) = 1 := by simpa using h
  exact one_ne_zero (by linear_combination h2 - h' : (1 : K) = 0)

end SL2

@[expose] def d4Quad : Fin 4 → Fin Tag.D4.rank → ℤ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 1, 2, 1]]

theorem d4Quad_check : (∀ i, RootOps.isRootB Tag.D4 (d4Quad i) = true) ∧
    ∀ i j, i ≠ j → iform (d4Quad i) (d4Quad j) = 0 ∧
      RootOps.isRootB Tag.D4 (d4Quad i + d4Quad j) = false ∧
        RootOps.isRootB Tag.D4 (d4Quad i - d4Quad j) = false := by
  decide +kernel

set_option linter.unusedSectionVars false

variable (K : Type) [Field K]

@[expose] noncomputable def d4Block (i : Fin 4) : SL2 K →* adjointGroup Tag.D4 K :=
  (rootSL2 Tag.D4 K (d4Quad i)).codRestrict (adjointGroup Tag.D4 K)
    (exceptional_Lang_root_rank_one_data Tag.D4 K (d4Quad i)).2.2.2.2.1

theorem coe_d4Block (i : Fin 4) (A : SL2 K) :
    (d4Block K i A : ModGL Tag.D4 K) = rootSL2 Tag.D4 K (d4Quad i) A :=
  rfl

theorem d4Block_injective (i : Fin 4) : Function.Injective (d4Block K i) := by
  intro A B h
  have h' := congrArg (fun g : adjointGroup Tag.D4 K => (g : ModGL Tag.D4 K)) h
  simp only [coe_d4Block] at h'
  exact rootSL2_injective_of_field (d4Quad i) h'

theorem d4Block_commute {i j : Fin 4} (hij : i ≠ j) (A B : SL2 K) :
    Commute (d4Block K i A) (d4Block K j B) := by
  have hroot : ∀ i, IsRoot Tag.D4 (d4Quad i) := fun i => RootOps.isRootB_iff.1 (d4Quad_check.1 i)
  have hnot : ∀ {v : Fin Tag.D4.rank → ℤ}, RootOps.isRootB Tag.D4 v = false →
      ¬ IsRoot Tag.D4 v := fun hv hr => by
    rw [← RootOps.isRootB_iff, hv] at hr
    exact Bool.false_ne_true hr
  obtain ⟨h0, hp, hm⟩ := d4Quad_check.2 i j hij
  exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.D4 K
    (hroot i) (hroot j) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)

theorem commute_d4Block_zero_neg_one (i : Fin 4) (A : SL2 K) :
    Commute (d4Block K 0 (-1)) (d4Block K i A) := by
  by_cases hi : (0 : Fin 4) = i
  · subst hi
    exact (Commute.neg_one_left A).map (d4Block K 0)
  · exact d4Block_commute K hi _ _

theorem d4Block_zero_neg_one_sq : d4Block K 0 (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

theorem d4Block_zero_neg_one_ne_one (hK : ringChar K ≠ 2) : d4Block K 0 (-1) ≠ 1 := by
  intro h
  have h1 : (-1 : SL2 K) = 1 := d4Block_injective K 0 (h.trans (map_one _).symm)
  have h2 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h2
  exact hK (neg_one_eq_one_iff.1 h2)

theorem fixedBlocks_conj_d4Block [Finite K] (hK : 4 ≤ Nat.card K) :
    FixedBlocks 3 (MulAut.conj (d4Block K 0 (-1))) 4 := by
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  refine ⟨fun i => (d4Block K i).range, fun i => d4Block K i c3SL, ?_, ?_, fun i => ?_,
    fun i => ?_, fun i => ⟨d4Block K i (uSL 1), ⟨uSL 1, rfl⟩, fun hc => ?_⟩⟩
  · rintro i j hij _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact d4Block_commute K hij A B
  · rintro i _ ⟨A, rfl⟩
    rw [MulAut.conj_apply, (commute_d4Block_zero_neg_one K i A).eq, mul_inv_cancel_right]
  · show d4Block K i c3SL ∈ ⁅(d4Block K i).range, (d4Block K i).range⁆
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ (Group.IsPerfect.mem_commutator (G := SL2 K))
  · rw [← map_pow, c3SL_pow_three, map_one]
  · refine not_commute_c3SL_uSL (K := K) (d4Block_injective K i ?_)
    rw [map_mul, map_mul]
    exact hc.eq

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
