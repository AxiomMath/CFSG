module

public import CFSG.ClassicalInvolution.Q3.Q3ZBRigid
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
public import CFSG.ClassicalInvolution.Q3.Q3ZBLayer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups
open Matrix

@[expose] noncomputable def tHub : StatedSp 2 F3 := longBlock F3 2 0 uSL

@[expose] noncomputable def DHub : Subgroup (StatedSp 2 F3) := Subgroup.centralizer {tHub}

theorem mem_DHub {g : StatedSp 2 F3} : g ∈ DHub ↔ g * tHub = tHub * g := by
  rw [DHub, Subgroup.mem_centralizer_singleton_iff]

theorem entries_of_mem_DHub {g : StatedSp 2 F3} (hg : g ∈ DHub) :
    mat 2 F3 g (Sum.inl 1) (Sum.inl 0) = 0 ∧ mat 2 F3 g (Sum.inr 0) (Sum.inl 0) = 0 ∧
      mat 2 F3 g (Sum.inr 1) (Sum.inl 0) = 0 ∧ mat 2 F3 g (Sum.inr 0) (Sum.inl 1) = 0 ∧
      mat 2 F3 g (Sum.inr 0) (Sum.inr 1) = 0 ∧
      mat 2 F3 g (Sum.inr 0) (Sum.inr 0) = mat 2 F3 g (Sum.inl 0) (Sum.inl 0) := by
  have e1 := congrArg (mat 2 F3) (mem_DHub.1 hg)
  rw [map_mul, map_mul, tHub, mat_longBlock] at e1
  have z1 := congrFun (congrFun e1 (Sum.inl 1)) (Sum.inr 0)
  have z2 := congrFun (congrFun e1 (Sum.inr 0)) (Sum.inr 0)
  have z3 := congrFun (congrFun e1 (Sum.inr 1)) (Sum.inr 0)
  have z4 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inl 1)
  have z5 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inr 1)
  have q1 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    CFSG.LieType.Steinberg.Sp.blockMat, uSL] at z1 z2 z3 z4 z5 q1
  exact ⟨z1, z2, z3, z4, z5, by linear_combination -q1⟩

theorem det_blk_of_mem_DHub {g : StatedSp 2 F3} (hg : g ∈ DHub) :
    mat 2 F3 g (Sum.inl 1) (Sum.inl 1) * mat 2 F3 g (Sum.inr 1) (Sum.inr 1) -
      mat 2 F3 g (Sum.inl 1) (Sum.inr 1) * mat 2 F3 g (Sum.inr 1) (Sum.inl 1) = 1 := by
  obtain ⟨-, -, -, z4, z5, -⟩ := entries_of_mem_DHub hg
  have s := form_mulVec g bE1 bF1
  simp [form_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply, sgn, par] at s
  rw [z4, z5] at s
  linear_combination s

@[expose] noncomputable def blkMat (g : StatedSp 2 F3) : Matrix (Fin 2) (Fin 2) F3 :=
  !![mat 2 F3 g (Sum.inl 1) (Sum.inl 1), mat 2 F3 g (Sum.inl 1) (Sum.inr 1);
    mat 2 F3 g (Sum.inr 1) (Sum.inl 1), mat 2 F3 g (Sum.inr 1) (Sum.inr 1)]

theorem blkMat_mul {g h : StatedSp 2 F3} (hg : g ∈ DHub) (hh : h ∈ DHub) :
    blkMat (g * h) = blkMat g * blkMat h := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := entries_of_mem_DHub hg
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := entries_of_mem_DHub hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, g1, g3, h4, h5]

theorem blkMat_one : blkMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

@[expose] noncomputable def blkSL : ↥DHub →* SL(2, F3) where
  toFun g := ⟨blkMat g.1, by
    rw [Matrix.det_fin_two]
    simpa [blkMat] using det_blk_of_mem_DHub g.2⟩
  map_one' := Subtype.ext blkMat_one
  map_mul' g h := Subtype.ext (blkMat_mul g.2 h.2)

theorem blkSL_coe (g : ↥DHub) : ((blkSL g : SL(2, F3)) : Matrix (Fin 2) (Fin 2) F3) = blkMat g.1 :=
  rfl

@[expose] noncomputable def epsHom : ↥DHub →* F3 where
  toFun g := mat 2 F3 g.1 (Sum.inl 0) (Sum.inl 0)
  map_one' := by simp
  map_mul' g h := by
    obtain ⟨h1, h2, h3, -, -, -⟩ := entries_of_mem_DHub h.2
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, h3]

theorem epsHom_sq (g : ↥DHub) : epsHom g * epsHom g = 1 := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := entries_of_mem_DHub g.2
  have s := form_mulVec g.1 bE0 bF0
  simp [form_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply, sgn, par] at s
  simp only [g1, g2, g3, g6, zero_mul, add_zero, neg_zero] at s
  exact s

@[expose] noncomputable def QexpHom : ↥DHub →* SL(2, F3) × F3ˣ :=
  blkSL.prod (MonoidHom.toHomUnits epsHom)

@[expose] noncomputable def Qexp : Subgroup (StatedSp 2 F3) := QexpHom.ker.map DHub.subtype

theorem mem_Qexp {g : StatedSp 2 F3} :
    g ∈ Qexp ↔ ∃ h : g ∈ DHub, blkSL ⟨g, h⟩ = 1 ∧ epsHom ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := (MonoidHom.mem_ker).1 hx
    simp only [QexpHom, MonoidHom.prod_apply, Prod.mk_eq_one] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    simpa [MonoidHom.toHomUnits, Units.ext_iff] using h2
  · rintro ⟨h, h1, h2⟩
    refine ⟨⟨g, h⟩, ?_, rfl⟩
    refine (MonoidHom.mem_ker).2 ?_
    simp only [QexpHom, MonoidHom.prod_apply, Prod.mk_eq_one]
    exact ⟨h1, by simpa [MonoidHom.toHomUnits, Units.ext_iff] using h2⟩

theorem Qexp_le_DHub : Qexp ≤ DHub := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem conj_mem_Qexp {d q : StatedSp 2 F3} (hd : d ∈ DHub) (hq : q ∈ Qexp) :
    d * q * d⁻¹ ∈ Qexp := by
  obtain ⟨x, hx, hxq⟩ := hq
  have hn := (QexpHom.normal_ker).conj_mem x hx ⟨d, hd⟩
  refine ⟨_, hn, ?_⟩
  rw [← hxq]
  simp


theorem lb1_mem_DHub (y : SL(2, F3)) : longBlock F3 2 1 y ∈ DHub := by
  rw [mem_DHub, tHub]
  exact (commute_longBlock_longBlock (by decide : (1 : Fin 2) ≠ 0) y uSL).eq

theorem blkSL_lb1 (y : SL(2, F3)) : blkSL ⟨longBlock F3 2 1 y, lb1_mem_DHub y⟩ = y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkSL_coe, blkMat, mat_longBlock, CFSG.LieType.Steinberg.Sp.blockMat]

theorem epsHom_lb1 (y : SL(2, F3)) : epsHom ⟨longBlock F3 2 1 y, lb1_mem_DHub y⟩ = 1 := by
  simp [epsHom, mat_longBlock, CFSG.LieType.Steinberg.Sp.blockMat]

theorem longInv0_mem_DHub : longInv F3 2 0 ∈ DHub := by
  rw [mem_DHub, tHub]
  exact longInv_comm_lb 0 uSL

theorem blkSL_longInv0 : blkSL ⟨longInv F3 2 0, longInv0_mem_DHub⟩ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkSL_coe, blkMat, longInv, mat_longBlock, CFSG.LieType.Steinberg.Sp.blockMat]

theorem epsHom_longInv0 : epsHom ⟨longInv F3 2 0, longInv0_mem_DHub⟩ = -1 := by
  simp [epsHom, longInv, mat_longBlock, CFSG.LieType.Steinberg.Sp.blockMat]


theorem neg_one_mem_center_sl2F3 : (-1 : SL(2, F3)) ∈ Subgroup.center SL(2, F3) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg, neg_mul, mul_one, one_mul]

theorem orderOf_neg_one_sl2F3 : orderOf (-1 : SL(2, F3)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, neg_mul_neg, mul_one]
  · intro h
    have h0 := congrArg (fun g : SL(2, F3) => (g : Matrix (Fin 2) (Fin 2) F3) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h0
    exact one_ne_neg_one_f3 h0.symm

theorem not_odd_orderOf_neg_one_sl2F3 : ¬ Odd (orderOf (-1 : SL(2, F3))) := by
  rw [orderOf_neg_one_sl2F3]
  decide

theorem mem_Qexp_of_hom (x : ↥DHub) (h1 : blkSL x = 1) (h2 : epsHom x = 1) :
    (x : StatedSp 2 F3) ∈ Qexp :=
  mem_Qexp.2 ⟨x.2, h1, h2⟩

theorem le_Qexp_of_odd {S : Subgroup (StatedSp 2 F3)} (hS : S ≤ DHub)
    (hn : ∀ d ∈ DHub, ∀ s ∈ S, d * s * d⁻¹ ∈ S) (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    S ≤ Qexp := by
  set S' : Subgroup ↥DHub := S.subgroupOf DHub with hS'
  have hS'n : S'.Normal := by
    refine ⟨fun s hs d => ?_⟩
    rw [hS', Subgroup.mem_subgroupOf] at hs ⊢
    exact hn d.1 d.2 s.1 hs
  have hsurj : Function.Surjective blkSL := fun y =>
    ⟨⟨longBlock F3 2 1 y, lb1_mem_DHub y⟩, blkSL_lb1 y⟩
  have hT : (S'.map blkSL).Normal := hS'n.map blkSL hsurj
  have hoddS' : ∀ s' ∈ S', Odd (orderOf s') := by
    intro s' hs'
    rw [hS', Subgroup.mem_subgroupOf] at hs'
    rw [← Subgroup.orderOf_coe]
    exact hodd _ hs'
  have hoddT : ∀ t ∈ S'.map blkSL, Odd (orderOf t) := by
    rintro _ ⟨s', hs', rfl⟩
    exact (hoddS' s' hs').of_dvd_nat (orderOf_map_dvd blkSL s')
  have hbot : S'.map blkSL = ⊥ := by
    rcases Q3T6.normal_cases_of_equiv_sl2_of_card_three card_F3 (MulEquiv.refl SL(2, F3)) _ hT with
      h | h | h | h
    · exact h
    · exact absurd (hoddT _ (h ▸ neg_one_mem_center_sl2F3)) not_odd_orderOf_neg_one_sl2F3
    · have hc : Nat.card (commutator SL(2, F3)) = 8 :=
        Q3T6.natCard_commutator_of_equiv_sl2_of_card_three card_F3 (MulEquiv.refl SL(2, F3))
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := commutator SL(2, F3)) 2
        (by rw [hc]; norm_num)
      have := hoddT (x : SL(2, F3)) (by rw [h]; exact x.2)
      rw [Subgroup.orderOf_coe, hx] at this
      exact absurd this (by decide)
    · exact absurd (hoddT _ (h ▸ Subgroup.mem_top _)) not_odd_orderOf_neg_one_sl2F3
  intro s hs
  have hsD : s ∈ DHub := hS hs
  have hsS' : (⟨s, hsD⟩ : ↥DHub) ∈ S' := by
    rw [hS', Subgroup.mem_subgroupOf]
    exact hs
  refine mem_Qexp_of_hom ⟨s, hsD⟩ ?_ ?_
  · have hm : blkSL ⟨s, hsD⟩ ∈ S'.map blkSL := ⟨_, hsS', rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hm
  · obtain ⟨k, hk⟩ := hodd s hs
    have h1 : epsHom ⟨s, hsD⟩ ^ orderOf s = 1 := by
      rw [← map_pow]
      have : (⟨s, hsD⟩ : ↥DHub) ^ orderOf s = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have hsq : epsHom ⟨s, hsD⟩ ^ 2 = 1 := by rw [sq]; exact epsHom_sq ⟨s, hsD⟩
    rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul] at h1
    exact h1

theorem DHub_decomp {g : StatedSp 2 F3} (hg : g ∈ DHub) : ∃ q ∈ Qexp, ∃ y : SL(2, F3),
    g = q * longBlock F3 2 1 y ∨ g = q * longBlock F3 2 1 y * longInv F3 2 0 := by
  set G0 : ↥DHub := ⟨g, hg⟩ with hG0
  set H : ↥DHub := ⟨longBlock F3 2 1 (blkSL G0), lb1_mem_DHub _⟩ with hH
  set Z : ↥DHub := ⟨longInv F3 2 0, longInv0_mem_DHub⟩ with hZ
  have hHb : blkSL H = blkSL G0 := blkSL_lb1 _
  have hHe : epsHom H = 1 := epsHom_lb1 _
  have hZb : blkSL Z = 1 := blkSL_longInv0
  have hZe : epsHom Z = -1 := epsHom_longInv0
  rcases mul_self_eq_one_iff.1 (epsHom_sq G0) with he | he
  · refine ⟨((G0 * H⁻¹ : ↥DHub) : StatedSp 2 F3), mem_Qexp_of_hom _ ?_ ?_, blkSL G0, Or.inl ?_⟩
    · rw [map_mul, map_inv, hHb, mul_inv_cancel]
    · rw [map_mul, map_inv, hHe, he, inv_one, one_mul]
    · simp [hG0, hH]
  · refine ⟨((G0 * (H * Z)⁻¹ : ↥DHub) : StatedSp 2 F3), mem_Qexp_of_hom _ ?_ ?_, blkSL G0,
      Or.inr ?_⟩
    · rw [map_mul, map_inv, map_mul, hHb, hZb, mul_one, mul_inv_cancel]
    · rw [map_mul, map_inv, map_mul, hHe, hZe, he]
      simp
    · simp only [hG0, hH, hZ, Subgroup.coe_mul, Subgroup.coe_inv]
      group

end CFSG.ClassicalInvolution.Q3.Q3ZB
