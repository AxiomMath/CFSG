module

public import CFSG.CGT.T75P.Chain

public section

namespace CFSG.CGT.T75P

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

@[expose] def ut (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1]

theorem ut_mul (a b c d e f a' b' c' d' e' f' : ZMod 2) :
    ut a b c d e f * ut a' b' c' d' e' f' =
      ut (a + a') (b + b' + a * d') (c + c' + a * e' + b * f') (d + d') (e + e' + d * f')
        (f + f') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ut, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem ut_det (a b c d e f : ZMod 2) : (ut a b c d e f).det = 1 := by
  simp [ut, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

@[expose] def utSL (a b c d e f : ZMod 2) : SL(4, ZMod 2) := ⟨ut a b c d e f, ut_det a b c d e f⟩

theorem utSL_mul (a b c d e f a' b' c' d' e' f' : ZMod 2) :
    utSL a b c d e f * utSL a' b' c' d' e' f' =
      utSL (a + a') (b + b' + a * d') (c + c' + a * e' + b * f') (d + d') (e + e' + d * f')
        (f + f') :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact ut_mul ..)

theorem utSL_one : utSL 0 0 0 0 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utSL, ut]

theorem utSL_inv (a b c d e f : ZMod 2) :
    (utSL a b c d e f)⁻¹ = utSL (-a) (a * d - b) (-c + a * e + b * f - a * d * f) (-d)
      (d * f - e) (-f) := by
  apply inv_eq_of_mul_eq_one_right
  have key : ∀ a b c d e f : ZMod 2, utSL a b c d e f * utSL (-a) (a * d - b)
      (-c + a * e + b * f - a * d * f) (-d) (d * f - e) (-f) = 1 := by decide +kernel
  exact key a b c d e f

@[expose] def U4 : Subgroup SL(4, ZMod 2) where
  carrier := {M | ∃ a b c d e f, M = utSL a b c d e f}
  one_mem' := ⟨0, 0, 0, 0, 0, 0, utSL_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, e, f, rfl⟩ ⟨a', b', c', d', e', f', rfl⟩
    exact ⟨_, _, _, _, _, _, utSL_mul ..⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, d, e, f, rfl⟩
    exact ⟨_, _, _, _, _, _, utSL_inv ..⟩

theorem card_U4 : Nat.card U4 = 64 := by
  have hbij : Function.Bijective
      (fun x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 =>
        (⟨utSL x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2,
          ⟨_, _, _, _, _, _, rfl⟩⟩ : U4)) := by
    constructor
    · rintro ⟨a, b, c, d, e, f⟩ ⟨a', b', c', d', e', f'⟩ h
      have h' := congrArg (fun y : U4 => ((y : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
      simp only [utSL, ut] at h'
      have h01 := congrFun (congrFun h' 0) 1
      have h02 := congrFun (congrFun h' 0) 2
      have h03 := congrFun (congrFun h' 0) 3
      have h12 := congrFun (congrFun h' 1) 2
      have h13 := congrFun (congrFun h' 1) 3
      have h23 := congrFun (congrFun h' 2) 3
      simp at h01 h02 h03 h12 h13 h23
      simp [h01, h02, h03, h12, h13, h23]
    · rintro ⟨_, a, b, c, d, e, f, rfl⟩
      exact ⟨(a, b, c, d, e, f), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

@[expose] def gA : SL(4, ZMod 2) := utSL 1 0 0 0 0 0
@[expose] def gB : SL(4, ZMod 2) := utSL 0 0 0 1 0 0
@[expose] def gC : SL(4, ZMod 2) := utSL 0 0 0 0 0 1

theorem hE13 : utSL 0 1 0 0 0 0 = (gA * gB) ^ 2 := by decide +kernel
theorem hE24 : utSL 0 0 0 0 1 0 = (gB * gC) ^ 2 := by decide +kernel
theorem hE14 : utSL 0 0 1 0 0 0 =
    utSL 0 1 0 0 0 0 * gC * (utSL 0 1 0 0 0 0)⁻¹ * gC⁻¹ := by decide +kernel

theorem hfac : ∀ a b c d e f : ZMod 2, utSL a b c d e f = gA ^ a.val * gB ^ d.val * gC ^ f.val *
    (utSL 0 1 0 0 0 0) ^ (b + a * d).val * (utSL 0 0 0 0 1 0) ^ (e + d * f).val *
      (utSL 0 0 1 0 0 0) ^ (c + a * e).val := by decide +kernel

theorem closure_gen_eq : Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) = U4 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, 0, 0, 0, rfl⟩
    · exact ⟨0, 0, 0, 1, 0, 0, rfl⟩
    · exact ⟨0, 0, 0, 0, 0, 1, rfl⟩
  · rintro _ ⟨a, b, c, d, e, f, rfl⟩
    have hA : gA ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) :=
      Subgroup.subset_closure (by simp)
    have hB : gB ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) :=
      Subgroup.subset_closure (by simp)
    have hC : gC ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) :=
      Subgroup.subset_closure (by simp)
    have h13 : utSL 0 1 0 0 0 0 ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) := by
      rw [hE13]; exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hA hB) 2
    have h24 : utSL 0 0 0 0 1 0 ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) := by
      rw [hE24]; exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hB hC) 2
    have h14 : utSL 0 0 1 0 0 0 ∈ Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2)) := by
      rw [hE14]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h13 hC)
        (Subgroup.inv_mem _ h13)) (Subgroup.inv_mem _ hC)
    rw [hfac]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hA _) (Subgroup.pow_mem _ hB _))
      (Subgroup.pow_mem _ hC _)) (Subgroup.pow_mem _ h13 _)) (Subgroup.pow_mem _ h24 _))
      (Subgroup.pow_mem _ h14 _)

theorem card_closure_gen : Nat.card (Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2))) = 64 := by
  rw [closure_gen_eq]
  exact card_U4

theorem card_SL_four_two : Nat.card SL(4, GaloisField 2 1) = 20160 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero]
  decide

@[expose] noncomputable def castF : ZMod 2 →+* GaloisField 2 1 := ZMod.castHom (dvd_refl 2) _

@[expose] noncomputable def toF : SL(4, ZMod 2) →* SL(4, GaloisField 2 1) :=
  Matrix.SpecialLinearGroup.map castF

theorem toF_coe (g : SL(4, ZMod 2)) :
    ((toF g : SL(4, GaloisField 2 1)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) =
      castF.mapMatrix (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) := rfl

theorem toF_injective : Function.Injective toF := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun m : SL(4, GaloisField 2 1) =>
    (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 1))) h
  simp only [toF_coe] at h'
  exact Matrix.map_injective castF.injective h'

theorem toF_gA_apply (v : Fin 4 → GaloisField 2 1) :
    ((toF gA : SL(4, GaloisField 2 1)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) *ᵥ v =
      v + v 1 • Pi.single 0 1 := by
  rw [toF_coe]
  funext i
  fin_cases i <;> simp [gA, utSL, ut, castF, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem toF_gB_apply (v : Fin 4 → GaloisField 2 1) :
    ((toF gB : SL(4, GaloisField 2 1)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) *ᵥ v =
      v + v 2 • Pi.single 1 1 := by
  rw [toF_coe]
  funext i
  fin_cases i <;> simp [gB, utSL, ut, castF, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem toF_gC_apply (v : Fin 4 → GaloisField 2 1) :
    ((toF gC : SL(4, GaloisField 2 1)) : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) *ᵥ v =
      v + v 3 • Pi.single 2 1 := by
  rw [toF_coe]
  funext i
  fin_cases i <;> simp [gC, utSL, ut, castF, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem toF_gA_ne_one : toF gA ≠ 1 := fun h => by
  have h' := congrArg (fun m : SL(4, GaloisField 2 1) =>
    (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) 0 1) h
  simp only [toF_coe, Matrix.SpecialLinearGroup.coe_one] at h'
  simp [gA, utSL, ut, castF] at h'

theorem toF_gB_ne_one : toF gB ≠ 1 := fun h => by
  have h' := congrArg (fun m : SL(4, GaloisField 2 1) =>
    (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) 1 2) h
  simp only [toF_coe, Matrix.SpecialLinearGroup.coe_one] at h'
  simp [gB, utSL, ut, castF] at h'

theorem toF_gC_ne_one : toF gC ≠ 1 := fun h => by
  have h' := congrArg (fun m : SL(4, GaloisField 2 1) =>
    (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)) 2 3) h
  simp only [toF_coe, Matrix.SpecialLinearGroup.coe_one] at h'
  simp [gC, utSL, ut, castF] at h'

noncomputable def chain4 : TransvChain 4 3 where
  E := fun i => if i = 0 then toF gA else if i = 1 then toF gB else toF gC
  axis := fun i => if i = 0 then 1 else if i = 1 then 2 else 3
  axis_inj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  isTrans := by
    intro i
    fin_cases i
    · exact isTransvection_of_apply (toF gA) (LinearMap.proj 1) (Pi.single 0 1) (by simp)
        toF_gA_apply toF_gA_ne_one
    · exact isTransvection_of_apply (toF gB) (LinearMap.proj 2) (Pi.single 1 1) (by simp)
        toF_gB_apply toF_gB_ne_one
    · exact isTransvection_of_apply (toF gC) (LinearMap.proj 3) (Pi.single 2 1) (by simp)
        toF_gC_apply toF_gC_ne_one
  fixed_of := by
    intro i v hv
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ite_true] at hv ⊢
      rw [toF_gA_apply, hv]
      simp
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true] at hv ⊢
      rw [toF_gB_apply, hv]
      simp
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ite_false] at hv ⊢
      rw [toF_gC_apply, hv]
      simp
  odd_index := by
    have hrange : Set.range (fun i : Fin 3 =>
        if i = 0 then toF gA else if i = 1 then toF gB else toF gC) =
        toF '' ({gA, gB, gC} : Set SL(4, ZMod 2)) := by
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨gA, Or.inl rfl, by simp⟩
        · exact ⟨gB, Or.inr (Or.inl rfl), by simp⟩
        · exact ⟨gC, Or.inr (Or.inr rfl), by simp⟩
      · rintro ⟨y, rfl | rfl | rfl, rfl⟩
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩
    rw [hrange, ← MonoidHom.map_closure]
    have h64 : Nat.card ((Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2))).map toF) = 64 := by
      rw [Subgroup.card_map_of_injective toF_injective]
      exact card_closure_gen
    have h := Subgroup.index_mul_card ((Subgroup.closure ({gA, gB, gC} :
      Set SL(4, ZMod 2))).map toF)
    rw [h64, card_SL_four_two] at h
    have : ((Subgroup.closure ({gA, gB, gC} : Set SL(4, ZMod 2))).map toF).index = 315 := by
      omega
    rw [this]
    decide

end CFSG.CGT.T75P
