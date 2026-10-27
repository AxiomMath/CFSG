module

public import CFSG.ClassicalInvolution.WeakCT.SpAut
public import CFSG.ClassicalInvolution.WeakCT.SignedLevisDL

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.LieType.Universal.Symplectic (rootDatum cartanC)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped commutatorElement MatrixGroups

section Torus

variable {F : Type} [Field F]

theorem torusHom_eq_w (t : Fˣ) :
    torusHom F t = (tv 0 1 (t : F) * tv 1 0 (-(t : F)⁻¹) * tv 0 1 (t : F)) *
      (tv 0 1 (-1) * tv 1 0 1 * tv 0 1 (-1)) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, tv01_eq_sl2Upper, tv10_eq_sl2Lower, coe_torusHom,
    coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t.ne_zero]

theorem spBlock_torus_eq (i : Fin 2) (t : Fˣ) :
    spBlock F i (torusHom F t) =
      Steinberg.weylElement (Steinberg.Sp.x 2 F) i t *
        Steinberg.weylElement (Steinberg.Sp.x 2 F) i (-1) := by
  rw [torusHom_eq_w]
  simp only [map_mul, spBlock_upper, spBlock_lower]
  simp [Steinberg.weylElement]

theorem diagConj2_torusHom (a b t : Fˣ) :
    diagConj2 a b (torusHom F t) = torusHom F t := by
  refine Subtype.ext ?_
  rw [coe_diagConj2, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [mul_comm (a : F) (t : F), mul_assoc, mul_inv_cancel₀ a.ne_zero, mul_one]
  · rw [mul_comm (b : F) ((t : F)⁻¹), mul_assoc, mul_inv_cancel₀ b.ne_zero, mul_one]

end Torus

section Conj

variable {F : Type} [Field F]

open CFSG.LieType.Steinberg in
theorem weyl_pair_conj_unit {K : Type} [Group K] {D : UniversalRootDatum K}
    {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) (k : Fin D.rank) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (t : Fˣ) (u : F) :
    (weylElement x k t * weylElement x k (-1)) * x β u *
        (weylElement x k t * weylElement x k (-1))⁻¹ =
      x β (((t : F) ^ (∑ m, D.cartan k m * β m)) * u) := by
  have h := weyl_pair_conj hE k hβ t.ne_zero u
  rwa [show Units.mk0 (t : F) t.ne_zero = t from Units.ext rfl] at h

theorem sp_pairing_s_long :
    ∑ m, (rootDatum 2 F).cartan spS m * (Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) m = -2 := by
  show ∑ m : Fin 2, cartanC 2 0 m * (Pi.single 1 1 : Fin 2 → ℤ) m = -2
  simp [Fin.sum_univ_two, cartanC]

theorem sp_pairing_s_neg_long :
    ∑ m, (rootDatum 2 F).cartan spS m * (-Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) m = 2 := by
  show ∑ m : Fin 2, cartanC 2 0 m * (-Pi.single 1 1 : Fin 2 → ℤ) m = 2
  simp [Fin.sum_univ_two, cartanC]

theorem sp_pairing_l_short :
    ∑ m, (rootDatum 2 F).cartan spL m * (Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) m = -1 := by
  show ∑ m : Fin 2, cartanC 2 1 m * (Pi.single 0 1 : Fin 2 → ℤ) m = -1
  simp [Fin.sum_univ_two, cartanC]

theorem sp_pairing_l_neg_short :
    ∑ m, (rootDatum 2 F).cartan spL m * (-Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) m = 1 := by
  show ∑ m : Fin 2, cartanC 2 1 m * (-Pi.single 0 1 : Fin 2 → ℤ) m = 1
  simp [Fin.sum_univ_two, cartanC]

theorem sp_torus0_conj (t : Fˣ) (A : SL(2, F)) :
    spBlock F 0 (torusHom F t) * spBlock F 1 A * (spBlock F 0 (torusHom F t))⁻¹ =
      spBlock F 1 (diagConj2 (t⁻¹ ^ 2) 1 A) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h : (MulAut.conj (spBlock F 0 (torusHom F t))).toMonoidHom.comp (spBlock F 1) =
      (spBlock F 1).comp (diagConj2 (t⁻¹ ^ 2) 1).toMonoidHom := by
    refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        spBlock_upper, diagConj2_tv01]
      rw [spBlock_torus_eq]
      have h := weyl_pair_conj_unit hE (spS (F := F)) (single_mem_sp_roots 1) t c
      rw [sp_pairing_s_long] at h
      refine h.trans ?_
      congr 1
      simp [zpow_neg]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        spBlock_lower, diagConj2_tv10]
      rw [spBlock_torus_eq]
      have h := weyl_pair_conj_unit hE (spS (F := F)) (neg_single_mem_sp_roots 1) t c
      rw [sp_pairing_s_neg_long] at h
      refine h.trans ?_
      congr 1
      simp [mul_comm]
  exact DFunLike.congr_fun h A

theorem sp_torus1_conj (t : Fˣ) (A : SL(2, F)) :
    spBlock F 1 (torusHom F t) * spBlock F 0 A * (spBlock F 1 (torusHom F t))⁻¹ =
      spBlock F 0 (diagConj2 t⁻¹ 1 A) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h : (MulAut.conj (spBlock F 1 (torusHom F t))).toMonoidHom.comp (spBlock F 0) =
      (spBlock F 0).comp (diagConj2 t⁻¹ 1).toMonoidHom := by
    refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        spBlock_upper, diagConj2_tv01]
      rw [spBlock_torus_eq]
      have h := weyl_pair_conj_unit hE (spL (F := F)) (single_mem_sp_roots 0) t c
      rw [sp_pairing_l_short] at h
      refine h.trans ?_
      congr 1
      simp [zpow_neg]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        spBlock_lower, diagConj2_tv10]
      rw [spBlock_torus_eq]
      have h := weyl_pair_conj_unit hE (spL (F := F)) (neg_single_mem_sp_roots 0) t c
      rw [sp_pairing_l_neg_short] at h
      refine h.trans ?_
      congr 1
      simp [mul_comm]
  exact DFunLike.congr_fun h A

end Conj

section Regular

variable {F : Type} [Field F]

theorem mem_diagTorus2_of_diagConj2_eq {a : Fˣ} (ha : a ≠ 1) {A : SL(2, F)}
    (h : diagConj2 a 1 A = A) : A ∈ diagTorus2 F := by
  have h01 := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have h10 := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp only [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two] at h01 h10
  simp at h01 h10
  have ha' : (a : F) ≠ 1 := fun h' => ha (Units.ext (by simpa using h'))
  refine mem_diagTorus2_of_offDiag A ?_ ?_
  · have : ((a : F) - 1) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha')
  · have h2 : ((a : F)⁻¹ - 1) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination h10
    refine (mul_eq_zero.1 h2).resolve_left ?_
    intro h3
    apply ha'
    have : (a : F)⁻¹ = 1 := sub_eq_zero.1 h3
    simpa using congrArg (fun z : F => z⁻¹) this

theorem spTorus_comm (s t : Fˣ) :
    Commute (spBlock F 0 (torusHom F s)) (spBlock F 1 (torusHom F t)) := by
  have h := sp_torus0_conj s (torusHom F t)
  rw [diagConj2_torusHom] at h
  exact (commute_iff_eq _ _).2 (by
    calc spBlock F 0 (torusHom F s) * spBlock F 1 (torusHom F t) =
        spBlock F 0 (torusHom F s) * spBlock F 1 (torusHom F t) *
          (spBlock F 0 (torusHom F s))⁻¹ * spBlock F 0 (torusHom F s) := by group
      _ = _ := by rw [h])

theorem mem_diagTorus2_of_commute_sp_long {s : Fˣ} (hs : s ^ 2 ≠ 1) {A : SL(2, F)}
    (h : Commute (spBlock F 0 (torusHom F s)) (spBlock F 1 A)) : A ∈ diagTorus2 F := by
  have h1 := sp_torus0_conj s A
  rw [h.eq, mul_inv_cancel_right] at h1
  refine mem_diagTorus2_of_diagConj2_eq (a := s⁻¹ ^ 2) ?_ (spBlock_injective 1 h1).symm
  intro h2
  apply hs
  rw [inv_pow, inv_eq_one] at h2
  exact h2

theorem mem_diagTorus2_of_commute_sp_short {t : Fˣ} (ht : t ≠ 1) {A : SL(2, F)}
    (h : Commute (spBlock F 1 (torusHom F t)) (spBlock F 0 A)) : A ∈ diagTorus2 F := by
  have h1 := sp_torus1_conj t A
  rw [h.eq, mul_inv_cancel_right] at h1
  refine mem_diagTorus2_of_diagConj2_eq (a := t⁻¹) ?_ (spBlock_injective 0 h1).symm
  intro h2
  exact ht (inv_eq_one.1 h2)

end Regular

end CFSG.ClassicalInvolution.WeakCT
