module

public import CFSG.GH74.GLS.Stage2.Final.ModelSpConj
public import CFSG.GH74.GLS.Stage2.Final.ModelE
public import CFSG.GH74.GLS.Stage2.Final.ModelLUFam

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS.Stage2.Final.ModelSp
  CFSG.GH74.GLS CFSG.GH74.GLS.SP.Local

variable {F : Type} [Field F]

theorem J0_mem_H2_sp (F : Type) [Field F] : J0 F ∈ (ModelData.sp F).H2 :=
  ((ModelData.sp F).mem_H2 _).2 ⟨mem_U2_sp.2 det_J0, det_J0⟩

theorem swap_of_comm {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {t y : G}
    (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) (hy : ∀ x ∈ K₁, y * x * y⁻¹ = x) :
    K₁.map (MulAut.conj (t * y)).toMonoidHom = K₂ := by
  rw [← hK]
  ext z
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    have := hy x hx
    calc t * x * t⁻¹ = t * (y * x * y⁻¹) * t⁻¹ := by rw [this]
      _ = t * y * x * (t * y)⁻¹ := by group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    have := hy x hx
    calc t * y * x * (t * y)⁻¹ = t * (y * x * y⁻¹) * t⁻¹ := by group
      _ = t * x * t⁻¹ := by rw [this]

theorem yP_comm_iota1 (M : ModelData F) (x : PG M) (hx : x ∈ K1 M) : yP M * x * (yP M)⁻¹ = x := by
  obtain ⟨a, rfl⟩ := hx
  have h : yP M = iota1 M ⟨-1, M.neg_one_mem_H2⟩ := (iota1_negOne M).symm
  rw [h, ← map_inv, ← map_mul, ← map_mul]
  have : (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) * a * (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2)⁻¹ = a := by
    apply Subtype.ext
    show (-1 : GL (Fin 2) F) * (a : GL (Fin 2) F) * (-1 : GL (Fin 2) F)⁻¹ = a
    simp
  rw [this]

theorem yP_mem_C0 (M : ModelData F) : yP M ∈ C0 M := K1_le_C0 M ⟨⟨-1, M.neg_one_mem_H2⟩, iota1_negOne M⟩

theorem spSyl_PG [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    ∃ S : Sylow 2 (PG (ModelData.sp F)),
      SPSyl (PG (ModelData.sp F)) (yP _) S (K1 _) (K2 _) (tP _ * yP _) := by
  have hG := goodModel_sp h2 h5
  have hZ : ZsTwo (ModelData.sp F) := zsTwo_sp
  have hJ := J0_mem_H2_sp F
  have hCodd : Odd (Cg (ModelData.sp F)).index := by rw [index_C]; exact hG.odd_index
  have hEn := layer_normal_Cg (ModelData.sp F) h2 hG.qs
  have hx2 : xJ (ModelData.sp F) hJ * xJ (ModelData.sp F) hJ = 1 := xJ_sq hG hJ
  have hW : IsPGroup 2 ↥(zpowers (xJ (ModelData.sp F) hJ) ⊔ zpowers (tP (ModelData.sp F))) :=
    ModelSylowQ.isPGroup_sup_zpowers (xJ_comm_tP _ hJ) ⟨1, by rw [pow_one, sq]; exact hx2⟩
      ⟨1, by rw [pow_one, sq]; exact tP_sq _⟩
  have hWC : zpowers (xJ (ModelData.sp F) hJ) ⊔ zpowers (tP (ModelData.sp F)) ≤
      Cg (ModelData.sp F) :=
    sup_le (Subgroup.zpowers_le.2 (E_le_Cg _ (xJ_mem_E _ hJ)))
      (Subgroup.zpowers_le.2 (tP_mem_Cg _))
  have hU : Nat.card ↥(ModelData.sp F).U2 = Nat.card ↥(ModelData.sp F).H2 * 1 := card_U2_sp
  have hidx := index_E_Cg_eq (ModelData.sp F) (card_Cg_eq hG hZ hU)
  obtain ⟨S, hSC, haS, hWS, hcard, -⟩ := exists_sylow_le_quot2 (Cg (ModelData.sp F))
    (K1 (ModelData.sp F) ⊔ K2 (ModelData.sp F)) hCodd (E_le_Cg _) hEn (o := 1) odd_one hidx
    (a := tP (ModelData.sp F)) hW (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hWC
    (tP_not_mem_E _ h2)
  refine ⟨S, ?_⟩
  have hzcen : CenterIs (S : Subgroup (PG (ModelData.sp F))) (yP _) :=
    sylow_center_of_le_Cg hG S hSC
  have hyS : yP (ModelData.sp F) ∈ (S : Subgroup (PG (ModelData.sp F))) :=
    ((hzcen _).2 (Subgroup.mem_zpowers _)).1
  have hcomm : tP (ModelData.sp F) * yP _ = yP _ * tP (ModelData.sp F) :=
    Subgroup.mem_centralizer_singleton_iff.1 (tP_mem_Cg _)
  have ht2 : (tP (ModelData.sp F) * yP _) * (tP (ModelData.sp F) * yP _) = 1 := by
    calc (tP (ModelData.sp F) * yP _) * (tP (ModelData.sp F) * yP _)
        = tP (ModelData.sp F) * (yP _ * tP (ModelData.sp F)) * yP _ := by group
      _ = tP (ModelData.sp F) * (tP (ModelData.sp F) * yP _) * yP _ := by rw [← hcomm]
      _ = (tP (ModelData.sp F) * tP (ModelData.sp F)) * (yP _ * yP _) := by group
      _ = 1 := by rw [tP_sq, yP_sq, one_mul]
  have ht1 : tP (ModelData.sp F) * yP _ ≠ 1 := by
    intro h
    apply tP_not_mem_C0 (ModelData.sp F) h2
    have : tP (ModelData.sp F) = (yP (ModelData.sp F))⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (C0 _).inv_mem (yP_mem_C0 _)
  have hwc : IsConj (yP (ModelData.sp F)) (tP (ModelData.sp F)) := by
    obtain ⟨k, hk, hkc⟩ := w_conj_sp h2
    exact isConj_yP_of_ConjMod (ModelData.sp F).swapGL_mem_K4 (ConjMod.of_conj hk hkc)
  have hq : Odd (Nat.card F) := odd_card_of_two_ne_zero h2
  have ht_mem : tP (ModelData.sp F) * yP (ModelData.sp F) ∈
      (S : Subgroup (PG (ModelData.sp F))) :=
    (S : Subgroup (PG (ModelData.sp F))).mul_mem haS hyS
  refine ⟨orderOf_yP _ h2, (centerIs_iff _ _).2 hzcen, ht_mem,
    orderOf_eq_prime (by rw [sq]; exact ht2) ht1, ?_, not_isConj_y_wy hZ h2, ?_, ?_, ?_, hcard⟩
  · exact swap_of_comm (tP_swap _) (yP_comm_iota1 _)
  · have : tP (ModelData.sp F) * yP _ * yP _ = tP (ModelData.sp F) := by
      rw [mul_assoc, yP_sq, mul_one]
    rw [this]; exact hwc
  · intro x hx y hy hx2 hy2 hxz hyz
    exact K_one_class_E hG hq (hasSL2Model_H2_sp F) hx hy hx2 hy2 hxz hyz
  · refine ⟨xJ (ModelData.sp F) hJ, ⟨hWS (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)),
      xJ_mem_E _ hJ⟩, orderOf_eq_prime (by rw [sq]; exact hx2) (xJ_ne_one hG hJ),
      xJ_ne_y hG hJ, (xJ_conj_of_jj hJ (jj_conj_sp h2)).symm⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.GLS.SP.Local

theorem spModelLeaf : SPModelLeaf := by
  intro Gs _ _ F _ _ h4 hodd he S' z' hz'
  obtain ⟨e⟩ := he
  have h2 : (2 : F) ≠ 0 := ModelBlock.two_ne_zero_of_odd_card hodd
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨S₀, hS⟩ := spSyl_PG h2 h5
  have hG := goodModel_sp h2 h5
  have hdata : SPModelData (PG (ModelData.sp F)) (Nat.card F) (yP _) S₀ (K1 _) (K2 _)
      (tP _ * yP _) := ⟨luComps_PG hG _ (hasSL2Model_H2_sp F), hS⟩
  exact spModelData_transfer (e.trans (ModelSp.spEquiv F)) ((centerIs_iff _ _).1 hS.z_cen) h2 S' z'
    hz' hdata

end CFSG.GH74.GLS.Stage2.Final
