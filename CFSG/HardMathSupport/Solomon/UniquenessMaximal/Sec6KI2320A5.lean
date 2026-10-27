module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Good
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Gen
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Blk
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Fix
public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParModel
public import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

variable {k : Type} [Field k]

theorem coe_diagGL_eq (u : kˣ) :
    ((diagGL u : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Dm (u : k) := by
  rw [coe_diagGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dm, Matrix.diagonal]

theorem Dm_comm_iota (ω : k) (h : SpecialLinearGroup (Fin 2) k) :
    Dm ω * (iota h : Matrix (Fin 3) (Fin 3) k) = (iota h : Matrix (Fin 3) (Fin 3) k) * Dm ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dm, coe_iota, iotaMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def a5Sub : Subgroup (projectiveSL 3 k) :=
  ((proj 3 k).comp (iota : SpecialLinearGroup (Fin 2) k →* _)).range

theorem proj_iota_injective :
    Function.Injective ((proj 3 k).comp (iota : SpecialLinearGroup (Fin 2) k →* _)) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have h1 : proj 3 k (iota h) = 1 := hh
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  have h00 := congrFun (congrFun hc 0) 0
  have hc1 : (c : k) = 1 := by
    simpa [coe_iota, iotaMat] using h00.symm
  have : iota h = 1 := by
    apply Subtype.ext
    rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one]
    simp
  exact iota_injective (this.trans (map_one iota).symm)

theorem a5Sub_mul_equiv : Nonempty (a5Sub (k := k) ≃* SpecialLinearGroup (Fin 2) k) :=
  ⟨(MonoidHom.ofInjective proj_iota_injective).symm⟩

theorem proj_x12_mem_a5Sub (c : k) : proj 3 k (x12 c) ∈ a5Sub :=
  ⟨sl2x c, by simp [iota_sl2x]⟩

@[expose] def sl2y (c : k) : SpecialLinearGroup (Fin 2) k := ⟨!![1, 0; c, 1], by simp [det_fin_two]⟩

theorem coe_sl2x (c : k) : ((sl2x c : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
    !![1, c; 0, 1] := rfl

theorem coe_sl2y (c : k) : ((sl2y c : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
    !![1, 0; c, 1] := rfl

theorem sl2_noncomm : ∃ a b : SpecialLinearGroup (Fin 2) k, a * b ≠ b * a := by
  refine ⟨sl2x 1, sl2y 1, fun h => ?_⟩
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2x, coe_sl2y] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

theorem a5_piece (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    NormalSimple (c25Fix (Subgroup.zpowers (xDiag u))) (a5Sub (k := k)) := by
  have hω0 : (u : k) ≠ 0 := u.ne_zero
  have hω1 : (u : k) ≠ 1 := val_ne_one hu
  obtain ⟨e⟩ := a5Sub_mul_equiv (k := k)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, rfl⟩
    rw [mem_c25Fix_zpowers_iff]
    exact conjAut_proj_eq_of_comm (diagGL u) (iota h) (by rw [coe_diagGL_eq]; exact Dm_comm_iota _ h)
  · intro x hx n hn
    obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    obtain ⟨h, rfl⟩ := hn
    have hfix : conjAut' 3 k (diagGL u) (proj 3 k g) = proj 3 k g :=
      (mem_c25Fix_zpowers_iff _ _).1 hx
    obtain ⟨c, hc⟩ := exists_smul_of_conjAut_fix (diagGL u) g hfix
    rw [coe_diagGL_eq] at hc
    obtain ⟨-, hblock⟩ := block_of_comm hω0 hω1 hc
    obtain ⟨h', hh'⟩ := conj_mem_range_iota hblock h
    refine ⟨h', ?_⟩
    simp only [MonoidHom.comp_apply] at hh' ⊢
    rw [hh', map_mul, map_mul, map_inv]
  · exact (MulEquiv.isSimpleGroup_congr e).2 (CFSG.Quasithin.H13.KGL34P.isSimpleGroup_sl_two hk)
  · obtain ⟨a, b, hab⟩ := sl2_noncomm (k := k)
    refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.KGL34P.card_sl_two hk]
    norm_num

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
