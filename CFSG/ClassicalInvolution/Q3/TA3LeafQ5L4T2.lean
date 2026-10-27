module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks Subgroup
open scoped commutatorElement

variable {K : Type} [Field K]

theorem range_bdHom_le_centralizer (P : GL (Fin 4) K) {X : SpecialLinearGroup (Fin 4) K}
    (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    ((proj 4 K).comp (bdHom P)).range ≤ centralizer {proj 4 K X} := by
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (bdHom_comm P hXP x)

theorem isPerfect_range_bdHom [Fintype K] (h4 : 4 ≤ Fintype.card K) (P : GL (Fin 4) K) :
    Group.IsPerfect ((proj 4 K).comp (bdHom P)).range := by
  rw [Subgroup.isPerfect_iff, MonoidHom.range_eq_map, ← map_commutator,
    commutator_top_prod h4]

theorem le_range_bdHom_of_perfect (h2 : (2 : K) ≠ 0) (P : GL (Fin 4) K)
    (X : SpecialLinearGroup (Fin 4) K)
    (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    {M : Subgroup (projectiveSL 4 K)} (hM : M ≤ centralizer {proj 4 K X}) (hMp : ⁅M, M⁆ = M) :
    M ≤ ((proj 4 K).comp (bdHom P)).range := by
  classical
  set CX := centralizer ({X} : Set (SpecialLinearGroup (Fin 4) K)) with hCX
  obtain ⟨δ, hδ⟩ := exists_blockDet P X hXP h2
  have hrange : ((proj 4 K).comp (bdHom P)).range = (bdHom P).range.map (proj 4 K) := by
    rw [MonoidHom.range_comp]
  have hC1 : ⁅centralizer {proj 4 K X}, centralizer {proj 4 K X}⁆ ≤ CX.map (proj 4 K) := by
    rw [commutator_le]
    intro u hu v hv
    obtain ⟨U, rfl⟩ := proj_surjective 4 K u
    obtain ⟨V, rfl⟩ := proj_surjective 4 K v
    refine ⟨⁅U, V⁆, ?_, by rw [map_commutatorElement]⟩
    have hsc : scalars 4 K ≤ center (SpecialLinearGroup (Fin 4) K) := scalars_le_center 4 K
    have hmem : ∀ Z : SpecialLinearGroup (Fin 4) K,
        proj 4 K Z ∈ centralizer {proj 4 K X} → Z * X * Z⁻¹ * X⁻¹ ∈ scalars 4 K := by
      intro Z hZ
      rw [mem_centralizer_singleton_iff] at hZ
      rw [← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hZ]
      group
    rw [SetLike.mem_coe, hCX, mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod hsc (hmem U hu) (hmem V hv)
  have hC2 : ⁅CX, CX⁆ ≤ (bdHom P).range := by
    rw [commutator_le]
    intro a ha b hb
    have : δ ⁅(⟨a, ha⟩ : CX), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact hδ _ this
  have hM2 : M = ⁅⁅M, M⁆, ⁅M, M⁆⁆ := by rw [hMp, hMp]
  rw [hM2, hrange]
  calc ⁅⁅M, M⁆, ⁅M, M⁆⁆ ≤ ⁅⁅centralizer {proj 4 K X}, centralizer {proj 4 K X}⁆,
        ⁅centralizer {proj 4 K X}, centralizer {proj 4 K X}⁆⁆ :=
        commutator_mono (commutator_mono hM hM) (commutator_mono hM hM)
    _ ≤ ⁅CX.map (proj 4 K), CX.map (proj 4 K)⁆ := commutator_mono hC1 hC1
    _ = (⁅CX, CX⁆).map (proj 4 K) := (map_commutator _ _ _).symm
    _ ≤ (bdHom P).range.map (proj 4 K) := map_mono hC2

theorem mem_center_of_mem_ker_bdHom (P : GL (Fin 4) K)
    {x : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
    (hx : x ∈ ((proj 4 K).comp (bdHom P)).ker) :
    x.1 ∈ center (SpecialLinearGroup (Fin 2) K) ∧ x.2 ∈ center (SpecialLinearGroup (Fin 2) K) := by
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hx
  obtain ⟨c, -, hc⟩ := hx
  rw [coe_bdHom] at hc
  have hbd : bd (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) =
      bd ((c : K) • 1) ((c : K) • 1) := by
    calc bd (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) =
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((P : Matrix (Fin 4) (Fin 4) K) *
          bd (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by
          simp only [← Matrix.mul_assoc]
          rw [hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = bd ((c : K) • 1) ((c : K) • 1) := by
          rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
            Matrix.mul_one, Matrix.smul_mul, hPP]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [bd]
  have e1 : (x.1 : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    have := congrArg ul hbd
    rwa [ul_bd, ul_bd] at this
  have e2 : (x.2 : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    have := congrArg lr hbd
    rwa [lr_bd, lr_bd] at this
  have hc2 : (c : K) ^ 2 = 1 := by
    have := x.1.2
    rw [e1, det_smul, det_one, mul_one, Fintype.card_fin] at this
    exact this
  refine ⟨Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc2,
    ?_⟩, Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc2,
    ?_⟩⟩
  · rw [e1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rw [e2, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem noOddNormal_range_bdHom [Fintype K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K)) (P : GL (Fin 4) K) :
    NoOddNormal ((proj 4 K).comp (bdHom P)).range := by
  classical
  intro M hMH hMn hMo
  refine eq_bot_of_odd_block hK ((proj 4 K).comp (bdHom P))
    (fun x hx => mem_center_of_mem_ker_bdHom P hx) M hMH (fun g hg r hr => ?_) hMo
  have := hMn.conj_mem ⟨r, hMH hr⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

end CFSG.ClassicalInvolution.Q3.TA3.Q5L4
