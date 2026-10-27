module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Sl2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Sub
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

noncomputable abbrev blk0 : Sl28 →* Sp8 := longBlock GF8 2 0

noncomputable abbrev blk1 : Sl28 →* Sp8 := longBlock GF8 2 1

theorem blk_commute (x y : Sl28) : Commute (blk0 x) (blk1 y) :=
  commute_longRootSp2 (K := GF8) (n := 2) (by decide) ⟨x, rfl⟩ ⟨y, rfl⟩

@[expose] noncomputable def swp : Sp8 := spOf sc.m sympl_s

theorem swp_mat : mat 2 GF8 swp = decode sc.m := rfl

theorem swp_sq : swp * swp = 1 := by
  apply mat_injective
  rw [map_mul, swp_mat, map_one]
  decide +kernel

theorem swp_inv : swp⁻¹ = swp := inv_eq_of_mul_eq_one_right swp_sq

theorem gf8_ofNat_zero : GF8.ofNat' 0 = 0 := rfl

theorem gf8_ofNat_one : GF8.ofNat' 1 = 1 := rfl

theorem swp_conj_blk0 (x : Sl28) : swp * blk0 x * swp⁻¹ = blk1 x := by
  rw [swp_inv]
  apply mat_injective
  rw [map_mul, map_mul, swp_mat, mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, decode, sc, ix]
  all_goals (simp only [gf8_ofNat_zero, gf8_ofNat_one]; ring)

theorem swp_conj_blk1 (x : Sl28) : swp * blk1 x * swp⁻¹ = blk0 x := by
  have h := swp_conj_blk0 x
  calc swp * blk1 x * swp⁻¹ = swp * (swp * blk0 x * swp⁻¹) * swp⁻¹ := by rw [h]
    _ = (swp * swp) * blk0 x * (swp⁻¹ * swp⁻¹) := by group
    _ = blk0 x := by rw [swp_inv, swp_sq]; group

theorem swp_blk0 (x : Sl28) : swp * blk0 x = blk1 x * swp := by
  rw [← swp_conj_blk0 x]; group

theorem swp_blk1 (x : Sl28) : swp * blk1 x = blk0 x * swp := by
  rw [← swp_conj_blk1 x]; group

theorem blk_mul (x y x' y' : Sl28) :
    (blk0 x * blk1 y) * (blk0 x' * blk1 y') = blk0 (x * x') * blk1 (y * y') := by
  have := (blk_commute x' y).symm.eq
  calc (blk0 x * blk1 y) * (blk0 x' * blk1 y') = blk0 x * (blk1 y * blk0 x') * blk1 y' := by
        group
    _ = blk0 x * (blk0 x' * blk1 y) * blk1 y' := by rw [this]
    _ = _ := by rw [map_mul, map_mul]; group

theorem swp_blk (x y : Sl28) : swp * (blk0 x * blk1 y) = (blk0 y * blk1 x) * swp := by
  calc swp * (blk0 x * blk1 y) = (swp * blk0 x) * blk1 y := by group
    _ = blk1 x * (swp * blk1 y) := by rw [swp_blk0]; group
    _ = blk1 x * (blk0 y * swp) := by rw [swp_blk1]
    _ = (blk0 y * blk1 x) * swp := by
      rw [← mul_assoc, (blk_commute y x).symm.eq, mul_assoc]

theorem blk_inv (x y : Sl28) : (blk0 x * blk1 y)⁻¹ = blk0 x⁻¹ * blk1 y⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [blk_mul]
  simp

theorem stdBlock_blk0 (x y : Sl28) :
    stdBlock 0 (mat 2 GF8 (blk0 x * blk1 y)) = (x : Matrix (Fin 2) (Fin 2) GF8) := by
  rw [map_mul, mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [stdBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat]

theorem stdBlock_blk1 (x y : Sl28) :
    stdBlock 1 (mat 2 GF8 (blk0 x * blk1 y)) = (y : Matrix (Fin 2) (Fin 2) GF8) := by
  rw [map_mul, mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [stdBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat]

theorem blk_inj {x y x' y' : Sl28} (h : blk0 x * blk1 y = blk0 x' * blk1 y') :
    x = x' ∧ y = y' := by
  constructor
  · apply Subtype.ext
    rw [← stdBlock_blk0 x y, ← stdBlock_blk0 x' y', h]
  · apply Subtype.ext
    rw [← stdBlock_blk1 x y, ← stdBlock_blk1 x' y', h]

@[expose] noncomputable def blkHom : Sl28 × Sl28 →* Sp8 :=
  MonoidHom.mk' (fun p => blk0 p.1 * blk1 p.2) (fun p q => (blk_mul p.1 p.2 q.1 q.2).symm)

theorem blkHom_apply (x y : Sl28) : blkHom (x, y) = blk0 x * blk1 y := rfl

theorem blkHom_injective : Function.Injective blkHom := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  obtain ⟨h1, h2⟩ := blk_inj h
  exact Prod.ext h1 h2

theorem swp_ne_blk (a b : Sl28) : swp ≠ blk0 a * blk1 b := by
  intro h
  have := congrFun (congrFun (congrArg (mat 2 GF8) h) (Sum.inl 0)) (Sum.inl 1)
  rw [swp_mat, map_mul, mat_longBlock, mat_longBlock] at this
  revert this
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, decode, sc, ix]
  decide

@[expose] def wrp (X : Subgroup Sl28) : Subgroup Sp8 where
  carrier := {g | ∃ x ∈ X, ∃ y ∈ X, g = blk0 x * blk1 y ∨ g = blk0 x * blk1 y * swp}
  one_mem' := ⟨1, X.one_mem, 1, X.one_mem, Or.inl (by simp)⟩
  mul_mem' := by
    rintro g g' ⟨x, hx, y, hy, rfl | rfl⟩ ⟨x', hx', y', hy', rfl | rfl⟩
    · exact ⟨x * x', X.mul_mem hx hx', y * y', X.mul_mem hy hy', Or.inl (blk_mul ..)⟩
    · refine ⟨x * x', X.mul_mem hx hx', y * y', X.mul_mem hy hy', Or.inr ?_⟩
      rw [← mul_assoc, blk_mul]
    · refine ⟨x * y', X.mul_mem hx hy', y * x', X.mul_mem hy hx', Or.inr ?_⟩
      calc blk0 x * blk1 y * swp * (blk0 x' * blk1 y')
          = blk0 x * blk1 y * (swp * (blk0 x' * blk1 y')) := by group
        _ = blk0 x * blk1 y * ((blk0 y' * blk1 x') * swp) := by rw [swp_blk]
        _ = _ := by rw [← mul_assoc, blk_mul]
    · refine ⟨x * y', X.mul_mem hx hy', y * x', X.mul_mem hy hx', Or.inl ?_⟩
      calc blk0 x * blk1 y * swp * (blk0 x' * blk1 y' * swp)
          = blk0 x * blk1 y * (swp * (blk0 x' * blk1 y')) * swp := by group
        _ = blk0 x * blk1 y * ((blk0 y' * blk1 x') * swp) * swp := by rw [swp_blk]
        _ = (blk0 x * blk1 y * (blk0 y' * blk1 x')) * (swp * swp) := by group
        _ = _ := by rw [swp_sq, mul_one, blk_mul]
  inv_mem' := by
    rintro g ⟨x, hx, y, hy, rfl | rfl⟩
    · exact ⟨x⁻¹, X.inv_mem hx, y⁻¹, X.inv_mem hy, Or.inl (blk_inv x y)⟩
    · refine ⟨y⁻¹, X.inv_mem hy, x⁻¹, X.inv_mem hx, Or.inr ?_⟩
      rw [mul_inv_rev, swp_inv, blk_inv]
      exact swp_blk _ _

theorem blk_mem_wrp {X : Subgroup Sl28} {x y : Sl28} (hx : x ∈ X) (hy : y ∈ X) :
    blk0 x * blk1 y ∈ wrp X := ⟨x, hx, y, hy, Or.inl rfl⟩

theorem swp_mem_wrp (X : Subgroup Sl28) : swp ∈ wrp X :=
  ⟨1, X.one_mem, 1, X.one_mem, Or.inr (by simp)⟩

theorem card_wrp (X : Subgroup Sl28) : Nat.card (wrp X) = 2 * Nat.card X ^ 2 := by
  let f : (X × X) ⊕ (X × X) → wrp X := Sum.elim
    (fun p => ⟨blk0 p.1 * blk1 p.2, p.1, p.1.2, p.2, p.2.2, Or.inl rfl⟩)
    (fun p => ⟨blk0 p.1 * blk1 p.2 * swp, p.1, p.1.2, p.2, p.2.2, Or.inr rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (p | p) (q | q) h
      · have h' := congrArg (fun g : wrp X => (g : Sp8)) h
        simp only [f, Sum.elim_inl] at h'
        obtain ⟨h1, h2⟩ := blk_inj h'
        exact congrArg Sum.inl (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
      · exfalso
        have h' := congrArg (fun g : wrp X => (g : Sp8)) h
        simp only [f, Sum.elim_inl, Sum.elim_inr] at h'
        have : swp = blk0 ((q.1 : Sl28)⁻¹ * p.1) * blk1 ((q.2 : Sl28)⁻¹ * p.2) := by
          calc swp = (blk0 q.1 * blk1 q.2)⁻¹ * (blk0 q.1 * blk1 q.2 * swp) := by group
            _ = (blk0 q.1 * blk1 q.2)⁻¹ * (blk0 p.1 * blk1 p.2) := by rw [← h']
            _ = _ := by rw [blk_inv, blk_mul]
        exact swp_ne_blk _ _ this
      · exfalso
        have h' := congrArg (fun g : wrp X => (g : Sp8)) h
        simp only [f, Sum.elim_inl, Sum.elim_inr] at h'
        have : swp = blk0 ((p.1 : Sl28)⁻¹ * q.1) * blk1 ((p.2 : Sl28)⁻¹ * q.2) := by
          calc swp = (blk0 p.1 * blk1 p.2)⁻¹ * (blk0 p.1 * blk1 p.2 * swp) := by group
            _ = (blk0 p.1 * blk1 p.2)⁻¹ * (blk0 q.1 * blk1 q.2) := by rw [h']
            _ = _ := by rw [blk_inv, blk_mul]
        exact swp_ne_blk _ _ this
      · have h' := congrArg (fun g : wrp X => (g : Sp8)) h
        simp only [f, Sum.elim_inr] at h'
        obtain ⟨h1, h2⟩ := blk_inj (mul_right_cancel h')
        exact congrArg Sum.inr (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    · rintro ⟨g, x, hx, y, hy, rfl | rfl⟩
      · exact ⟨Sum.inl (⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
      · exact ⟨Sum.inr (⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, Nat.card_prod]
  ring

theorem mat_blk0_slZ : mat 2 GF8 (blk0 slZ) = blockMat (Sum.inl 0) (Sum.inr 0) (mk28 1 1 1 0) := by
  rw [mat_longBlock]
  congr 1
  exact slZ_val

theorem block_eqs {g : Sp8} (h : g * blk0 slZ = blk0 slZ * g) :
    mat 2 GF8 g (Sum.inl 1) (Sum.inl 0) = 0 ∧ mat 2 GF8 g (Sum.inl 1) (Sum.inr 0) = 0 ∧
    mat 2 GF8 g (Sum.inr 1) (Sum.inl 0) = 0 ∧ mat 2 GF8 g (Sum.inr 1) (Sum.inr 0) = 0 ∧
    mat 2 GF8 g (Sum.inl 0) (Sum.inl 1) = 0 ∧ mat 2 GF8 g (Sum.inl 0) (Sum.inr 1) = 0 ∧
    mat 2 GF8 g (Sum.inr 0) (Sum.inl 1) = 0 ∧ mat 2 GF8 g (Sum.inr 0) (Sum.inr 1) = 0 := by
  have hM : mat 2 GF8 g * mat 2 GF8 (blk0 slZ) = mat 2 GF8 (blk0 slZ) * mat 2 GF8 g := by
    rw [← map_mul, ← map_mul, h]
  rw [mat_blk0_slZ] at hM
  have eq1 := congrFun (congrFun hM (Sum.inl 1)) (Sum.inr 0)
  have eq2 := congrFun (congrFun hM (Sum.inl 1)) (Sum.inl 0)
  have eq3 := congrFun (congrFun hM (Sum.inr 1)) (Sum.inr 0)
  have eq4 := congrFun (congrFun hM (Sum.inr 1)) (Sum.inl 0)
  have eq5 := congrFun (congrFun hM (Sum.inr 0)) (Sum.inl 1)
  have eq6 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 1)
  have eq7 := congrFun (congrFun hM (Sum.inr 0)) (Sum.inr 1)
  have eq8 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inr 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, mk28,
    gf8_ofNat_zero, gf8_ofNat_one] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  exact ⟨eq1.trans eq2, eq2, eq3.trans eq4, eq4, eq5.symm.trans eq6, eq7.symm.trans eq8, eq6, eq8⟩

theorem block_of_comm {g : Sp8} (h : g * blk0 slZ = blk0 slZ * g) :
    ∃ x y : Sl28, x ∈ slT ∧ g = blk0 x * blk1 y := by
  obtain ⟨h10, h12, h30, h32, h01, h03, h21, h23⟩ := block_eqs h
  have hdx : (stdBlock 0 (mat 2 GF8 g)).det = 1 := by
    refine det_stdBlock_eq_one g 0 fun c hc => ?_
    rcases c with i | i
    · fin_cases i
      · exact absurd (inl_mem_coords 0) hc
      · exact h10
    · fin_cases i
      · exact absurd (inr_mem_coords 0) hc
      · exact h30
  have hdy : (stdBlock 1 (mat 2 GF8 g)).det = 1 := by
    refine det_stdBlock_eq_one g 1 fun c hc => ?_
    rcases c with i | i
    · fin_cases i
      · exact h01
      · exact absurd (inl_mem_coords 1) hc
    · fin_cases i
      · exact h21
      · exact absurd (inr_mem_coords 1) hc
  refine ⟨mkSL _ hdx, mkSL _ hdy, ?_, ?_⟩
  · have hM : mat 2 GF8 g * mat 2 GF8 (blk0 slZ) = mat 2 GF8 (blk0 slZ) * mat 2 GF8 g := by
      rw [← map_mul, ← map_mul, h]
    rw [mat_blk0_slZ] at hM
    have f00 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inl 0)
    have f01 := congrFun (congrFun hM (Sum.inl 0)) (Sum.inr 0)
    have f10 := congrFun (congrFun hM (Sum.inr 0)) (Sum.inl 0)
    have f11 := congrFun (congrFun hM (Sum.inr 0)) (Sum.inr 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, mk28,
      gf8_ofNat_zero, gf8_ofNat_one, h01, h03, h21, h23] at f00 f01 f10 f11
    apply cent_z
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slZ_val]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [stdBlock, coe_mkSL, Matrix.mul_apply, Fin.sum_univ_two, mk28, gf8_ofNat_zero,
        gf8_ofNat_one]
    · exact f00
    · exact f01
    · exact f10
    · exact f11
  · apply mat_injective
    rw [map_mul, mat_longBlock, mat_longBlock]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, blockMat, stdBlock,
        coe_mkSL, h10, h12, h30, h32, h01, h03, h21, h23]

end CFSG.AGLEmbedding.KFactProofs.Sp48
