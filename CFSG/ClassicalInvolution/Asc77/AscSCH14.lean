module

public import CFSG.ClassicalInvolution.Asc77.AscSCH13
public import CFSG.ClassicalInvolution.Asc77.AscSCH03

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent exists_sylow_unipotent)

variable {F : Type} [Field F]

@[expose] def slU (x : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_slU (x : F) :
    ((slU x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem slU_add (x y : F) : slU (x + y) = slU x * slU y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slU, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
    simp
  ring

theorem slU_zero : slU (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slU]

@[expose] def slUhom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun x := slU x.toAdd
  map_one' := slU_zero
  map_mul' _ _ := slU_add _ _

@[expose] noncomputable def leviSpU : Multiplicative F →* StatedSp 2 F :=
  leviSL.comp slUhom

theorem leviUnipotent_le_range : leviUnipotent 2 F ≤ (leviSpU (F := F)).range := by
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨h1, h2⟩ := mem_unitriangular.1 hA
  refine ⟨Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) F) 0 1), ?_⟩
  have : slUhom (Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) F) 0 1)) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slUhom, coe_slU, h2 0, h2 1, h1 1 0 (by decide)]
  exact congrArg leviSL this

theorem slU_inv (x : F) : (slU x)⁻¹ = slU (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← slU_add, add_neg_cancel, slU_zero])

theorem coe_slU_inv (x : F) :
    (((slU x)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, -x; 0, 1] := by
  rw [slU_inv]
  rfl

theorem spTorus_leviSpU (a : Fin 2 → Fˣ) (x : F) :
    spTorus a * leviSpU (Multiplicative.ofAdd x) * (spTorus a)⁻¹ =
      leviSpU (Multiplicative.ofAdd ((a 0 : F) * (((a 1)⁻¹ : Fˣ) : F) * x)) := by
  apply Subtype.ext
  change (torusGL a * ((leviSL (slU x) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * (torusGL a)⁻¹ :
      GL (Fin 2 ⊕ Fin 2) F) = ((leviSL (slU ((a 0 : F) * (((a 1)⁻¹ : Fˣ) : F) * x)) :
      StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusGL, coe_torusGL_inv, coe_leviSL, coe_leviSL,
    coe_slU_inv, coe_slU_inv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, Matrix.mul_diagonal, coe_slU]
    field_simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    field_simp

@[expose] def scaleSym (c : F) (v : symMatrices 2 F) : symMatrices 2 F :=
  ⟨c • (v : Matrix (Fin 2) (Fin 2) F), by
    rw [mem_symMatrices, Matrix.transpose_smul, mem_symMatrices.1 v.2]⟩

theorem coe_scaleSym (c : F) (v : symMatrices 2 F) :
    ((scaleSym c v : symMatrices 2 F) : Matrix (Fin 2) (Fin 2) F) =
      c • (v : Matrix (Fin 2) (Fin 2) F) := rfl

theorem levi_scalar_conj_siegel (τ : Fˣ) (v : symMatrices 2 F) :
    leviSp (Matrix.GeneralLinearGroup.scalar (Fin 2) τ) *
        siegelSpHom 2 F (Multiplicative.ofAdd v) *
        (leviSp (Matrix.GeneralLinearGroup.scalar (Fin 2) τ))⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (scaleSym ((τ : F) ^ 2) v)) :=
  levi_conj_siegelSp _ _ _ (by
    rw [coe_scaleSym, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_transpose,
      ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, ← pow_two])

theorem scaleSym_eq_self {c : F} (hc : c ≠ 1) {v : symMatrices 2 F}
    (h : scaleSym c v = v) : v = 0 := by
  have h1 : (c - 1) • (v : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [sub_smul, one_smul, ← coe_scaleSym, h, sub_self]
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact absurd (sub_eq_zero.1 h2) hc
  · exact Subtype.ext h2

section Main

variable {E : Type*} [Group E] {π : E →* StatedSp 2 F} (hπ : Function.Surjective π)
  (hZ : π.ker ≤ Subgroup.center E)

include hZ in
theorem leviSpU_liftPair_eq_one (hCp : IsPGroup 3 π.ker) (s t : F) :
    liftPair hπ (leviSpU (F := F)) s t = 1 :=
  liftPair_self_eq_one_of_full hπ leviSpU hZ (p := 3) (by norm_num) hCp (AddMonoidHom.id F)
    (fun c hc => ⟨spTorus ![Units.mk0 c hc, 1], fun s => by
      rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, spTorus_leviSpU]
      simp⟩) s t

theorem statedSp_two_perfect_ker_eq_bot_defining [Finite F] {f : ℕ} (hF : Nat.card F = 3 ^ f)
    (h4 : 4 ≤ Nat.card F) [Finite E] [Group.IsPerfect E]
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hF
      omega
    · exact h
  have := Fintype.ofFinite F
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨l, hl⟩ := CFSG.LinearGroups.field_scalar_with_nontrivial_square
    (CFSG.LinearGroups.exists_finset_card_eq_four h4)
  have hu2 : (l : F) ^ 2 ≠ 1 := fun h => hl (Units.ext (by simpa using h))
  obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp π hπ
    (coprime_orderOf_leviSp_scalar (r := 2) hp hF hf l)
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 3 2
  refine ker_eq_bot_of_unipotent π hπ hC hCp (siegelRadicalSp 2 F) (leviUnipotent 2 F)
    leviUnipotent_le_normalizer
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ (siegelSpHom 2 F) hC
      (siegelSp_liftPair_eq_one hπ hC hCp (l : F) l.ne_zero hu2) hx hy)
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ leviSpU hC
      (leviSpU_liftPair_eq_one hπ hC hCp) (leviUnipotent_le_range hx) (leviUnipotent_le_range hy))
    a hacop ?_ ?_ ?_ ?_
  · rw [ha]
    exact mem_normalizer_of_conj_mem fun x hx => leviSp_conj_mem_siegelRadicalSp _ hx
  · intro v hv
    rw [ha]
    obtain ⟨A, -, rfl⟩ := hv
    rw [mul_inv_eq_iff_eq_mul]
    exact leviSp_scalar_commute (r := 2) l A
  · intro r hr hrfix
    rw [ha] at hrfix
    obtain ⟨v, rfl⟩ := hr
    have h0 := levi_scalar_conj_siegel (F := F) l v.toAdd
    rw [ofAdd_toAdd] at h0
    rw [h0] at hrfix
    have h1 := congrArg Multiplicative.toAdd (siegelSpHom_injective hrfix)
    have h3 := scaleSym_eq_self hu2 h1
    rw [show v = 1 from Multiplicative.toAdd.injective h3, map_one]
  · have hRV : siegelRadicalSp 2 F ⊔ leviUnipotent 2 F = (P : Subgroup (StatedSp 2 F)) :=
      unipotent_eq_sup.symm.trans hP.symm
    rw [hRV, Sylow.card_eq_multiplicity]
    simp [Nat.factorization_pow, Nat.Prime.factorization_self hp]

end Main

end CFSG.ClassicalInvolution.Asc77.SCH
