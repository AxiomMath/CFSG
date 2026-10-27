module

public import CFSG.GH74.GLS.Stage2.Final.ModelMinus
public import CFSG.GH74.GLS.Stage2.Final.ModelCard
public import CFSG.GH74.GLS.Stage2.Final.ModelLUSyl

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

theorem H2_sq_one [Finite F] {M : ModelData F} (hG : GoodModel M) {a : ↥M.H2} (h : a * a = 1) :
    a = 1 ∨ a = ⟨-1, M.neg_one_mem_H2⟩ := by
  have h' : (a : GL (Fin 2) F) * (a : GL (Fin 2) F) = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  by_cases h1 : (a : GL (Fin 2) F) = 1
  · left; exact Subtype.ext h1
  by_cases h2 : (a : GL (Fin 2) F) = -1
  · right; exact Subtype.ext h2
  exfalso
  obtain ⟨-, hd⟩ := refl_trace_det h' h1 h2
  have h3 := ((M.mem_H2 _).1 a.2).2
  rw [hd] at h3
  apply hG.two_ne_zero
  linear_combination -h3

theorem iota1_negOne' (M : ModelData F) : iota1 M ⟨-1, M.neg_one_mem_H2⟩ = yP M := iota1_negOne M

theorem iota2_negOne' (M : ModelData F) : iota2 M ⟨-1, M.neg_one_mem_H2⟩ = yP M := iota2_negOne M

theorem inv_E_classify [Finite F] {M : ModelData F} (hG : GoodModel M) {x : PG M}
    (hx : x ∈ K1 M ⊔ K2 M) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxy : x ≠ yP M) :
    ∃ a b : ↥M.H2, a * a = ⟨-1, M.neg_one_mem_H2⟩ ∧ b * b = ⟨-1, M.neg_one_mem_H2⟩ ∧
      x = iota1 M a * iota2 M b := by
  obtain ⟨a, b, rfl⟩ := (mem_E_iff M).1 hx
  have hker : iotaE M (a * a, b * b) = 1 := by
    have : iotaE M (a * a, b * b) = (iota1 M a * iota2 M b) * (iota1 M a * iota2 M b) := by
      rw [iotaE_apply, map_mul, map_mul]
      calc iota1 M a * iota1 M a * (iota2 M b * iota2 M b)
          = iota1 M a * (iota1 M a * iota2 M b) * iota2 M b := by group
        _ = iota1 M a * (iota2 M b * iota1 M a) * iota2 M b := by rw [iota_comm]
        _ = (iota1 M a * iota2 M b) * (iota1 M a * iota2 M b) := by group
    rw [this]; exact hx2
  have hmem : (a * a, b * b) ∈ (iotaE M).ker := hker
  rw [ker_iotaE hG] at hmem
  rcases mem_zpowers_of_sq_one (negNeg_sq M) hmem with h | h
  · exfalso
    have ha : a * a = 1 := congrArg Prod.fst h
    have hb : b * b = 1 := congrArg Prod.snd h
    rcases H2_sq_one hG ha with rfl | rfl <;> rcases H2_sq_one hG hb with rfl | rfl
    · apply hx1; simp
    · apply hxy; rw [map_one, one_mul, iota2_negOne']
    · apply hxy; rw [map_one, mul_one, iota1_negOne']
    · apply hx1; rw [iota1_negOne', iota2_negOne', yP_sq]
  · exact ⟨a, b, congrArg Prod.fst h, congrArg Prod.snd h, rfl⟩

theorem K_one_class_E [Finite F] {M : ModelData F} (hG : GoodModel M) {q : ℕ} (hq : Odd q)
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) {x y : PG M} (hx : x ∈ K1 M ⊔ K2 M)
    (hy : y ∈ K1 M ⊔ K2 M) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxz : x ≠ yP M)
    (hyz : y ≠ yP M) : ∃ k ∈ K1 M ⊔ K2 M, k * x * k⁻¹ = y := by
  have hxs : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hys : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; omega
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
  obtain ⟨a, b, ha, hb, rfl⟩ := inv_E_classify hG hx hxs hx1 hxz
  obtain ⟨a', b', ha', hb', rfl⟩ := inv_E_classify hG hy hys hy1 hyz
  obtain ⟨k₁, hk₁⟩ := ord4_conj_H2 hG hq hSL ha ha'
  obtain ⟨k₂, hk₂⟩ := ord4_conj_H2 hG hq hSL hb hb'
  refine ⟨iotaE M (k₁, k₂), ?_, ?_⟩
  · rw [← range_iotaE]; exact ⟨_, rfl⟩
  · have e1 : iota1 M a * iota2 M b = iotaE M (a, b) := rfl
    have e2 : iota1 M a' * iota2 M b' = iotaE M (a', b') := rfl
    rw [e1, e2, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext hk₁ hk₂

theorem J0_not_scalar (c : Fˣ) : J0 F ≠ sc2 c := by
  intro h
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_J0, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this

@[expose] noncomputable def xJ (M : ModelData F) (hJ : J0 F ∈ M.H2) : PG M :=
  iota1 M ⟨J0 F, hJ⟩ * iota2 M ⟨J0 F, hJ⟩

theorem xJ_eq_iotaE (M : ModelData F) (hJ : J0 F ∈ M.H2) :
    xJ M hJ = iotaE M (⟨J0 F, hJ⟩, ⟨J0 F, hJ⟩) := rfl

theorem xJ_mem_E (M : ModelData F) (hJ : J0 F ∈ M.H2) : xJ M hJ ∈ K1 M ⊔ K2 M :=
  (mem_E_iff M).2 ⟨_, _, rfl⟩

theorem iotaE_negNeg [Finite F] {M : ModelData F} (hG : GoodModel M) : iotaE M (negNeg M) = 1 := by
  have : negNeg M ∈ (iotaE M).ker := by rw [ker_iotaE hG]; exact Subgroup.mem_zpowers _
  exact this

theorem xJ_sq [Finite F] {M : ModelData F} (hG : GoodModel M) (hJ : J0 F ∈ M.H2) :
    xJ M hJ * xJ M hJ = 1 := by
  rw [xJ_eq_iotaE, ← map_mul]
  have : ((⟨J0 F, hJ⟩ : ↥M.H2), (⟨J0 F, hJ⟩ : ↥M.H2)) * (⟨J0 F, hJ⟩, ⟨J0 F, hJ⟩) = negNeg M :=
    Prod.ext (Subtype.ext J0_mul_self) (Subtype.ext J0_mul_self)
  rw [this]
  exact iotaE_negNeg hG

theorem xJ_ne_one [Finite F] {M : ModelData F} (hG : GoodModel M) (hJ : J0 F ∈ M.H2) :
    xJ M hJ ≠ 1 := by
  intro h
  have hmem : ((⟨J0 F, hJ⟩ : ↥M.H2), (⟨J0 F, hJ⟩ : ↥M.H2)) ∈ (iotaE M).ker := h
  rw [ker_iotaE hG] at hmem
  rcases mem_zpowers_of_sq_one (negNeg_sq M) hmem with h1 | h1
  · have := congrArg (fun p : ↥M.H2 × ↥M.H2 => (p.1 : GL (Fin 2) F)) h1
    exact J0_not_scalar (F := F) 1 (by simpa [sc2_one] using this)
  · have := congrArg (fun p : ↥M.H2 × ↥M.H2 => (p.1 : GL (Fin 2) F)) h1
    simp only [negNeg] at this
    exact J0_not_scalar (F := F) (-1) (by rw [sc2_neg_one]; exact this)

theorem xJ_ne_y [Finite F] {M : ModelData F} (hG : GoodModel M) (hJ : J0 F ∈ M.H2) :
    xJ M hJ ≠ yP M := by
  intro h
  have hy : yP M = iotaE M (⟨-1, M.neg_one_mem_H2⟩, 1) := by
    rw [iotaE_apply, map_one, mul_one, iota1_negOne']
  rw [hy, xJ_eq_iotaE] at h
  have hmem : (((⟨J0 F, hJ⟩ : ↥M.H2), (⟨J0 F, hJ⟩ : ↥M.H2))⁻¹ *
      (⟨-1, M.neg_one_mem_H2⟩, 1)) ∈ (iotaE M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [ker_iotaE hG] at hmem
  rcases mem_zpowers_of_sq_one (negNeg_sq M) hmem with h1 | h1
  · have := congrArg (fun p : ↥M.H2 × ↥M.H2 => (p.2 : GL (Fin 2) F)) h1
    simp only [Prod.snd_mul, Prod.snd_inv, mul_one] at this
    have h' : (J0 F)⁻¹ = 1 := by simpa using this
    apply J0_not_scalar (F := F) 1
    rw [sc2_one, ← inv_inv (J0 F), h', inv_one]
  · have := congrArg (fun p : ↥M.H2 × ↥M.H2 => (p.2 : GL (Fin 2) F)) h1
    simp only [Prod.snd_mul, Prod.snd_inv, mul_one, negNeg] at this
    have h' : (J0 F)⁻¹ = -1 := by simpa using this
    apply J0_not_scalar (F := F) (-1)
    rw [sc2_neg_one, ← inv_inv (J0 F), h']
    simp

theorem tP_conj_xJ (M : ModelData F) (hJ : J0 F ∈ M.H2) : tP M * xJ M hJ * (tP M)⁻¹ = xJ M hJ := by
  have e : tP M * (iota1 M ⟨J0 F, hJ⟩ * iota2 M ⟨J0 F, hJ⟩) * (tP M)⁻¹ =
      (tP M * iota1 M ⟨J0 F, hJ⟩ * (tP M)⁻¹) * (tP M * iota2 M ⟨J0 F, hJ⟩ * (tP M)⁻¹) := by group
  show tP M * (iota1 M ⟨J0 F, hJ⟩ * iota2 M ⟨J0 F, hJ⟩) * (tP M)⁻¹ = _
  rw [e, tP_conj_iota1, tP_conj_iota2]
  exact (iota_comm M _ _).symm

theorem xJ_comm_tP (M : ModelData F) (hJ : J0 F ∈ M.H2) : xJ M hJ * tP M = tP M * xJ M hJ := by
  have h := tP_conj_xJ M hJ
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem wy_sq (F : Type) [Field F] : (swapGL F * yGL F) * (swapGL F * yGL F) = xGL F := by
  have h := swapGL_mul_yGL_mul_inv (F := F)
  rw [swapGL_inv] at h
  calc (swapGL F * yGL F) * (swapGL F * yGL F) = (swapGL F * yGL F * swapGL F) * yGL F := by group
    _ = xyGL F * yGL F := by rw [h]
    _ = xGL F := by rw [xyGL, yGL, xGL, diagGL_mul]; simp

theorem tP_mul_yP (M : ModelData F) :
    tP M * yP M = mkP M ⟨swapGL F * yGL F, M.K4.mul_mem M.swapGL_mem_K4 M.yGL_mem_K4⟩ := rfl

theorem xJ_conj_of_jj {M : ModelData F} (hJ : J0 F ∈ M.H2)
    (hjj : ∃ k ∈ M.K4, k * diagGL (J0 F) (J0 F) * k⁻¹ = swapGL F * yGL F) :
    IsConj (xJ M hJ) (tP M * yP M) := by
  obtain ⟨k, hk, hkc⟩ := hjj
  have hxy := diagGL_mem_K4_of_H2 M ⟨J0 F, hJ⟩ ⟨J0 F, hJ⟩
  have hx : xJ M hJ = mkP M ⟨diagGL (J0 F) (J0 F), hxy⟩ := iota_mul_eq_mkP_diag M _ _ hxy
  rw [hx, tP_mul_yP, isConj_iff]
  refine ⟨mkP M ⟨k, hk⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hkc

theorem hasSqLift_y (M : ModelData F) : HasSqLift M (yP M) 1 := ⟨M.yK, rfl, M.yK_mul_self⟩

theorem hasSqLift_wy (M : ModelData F) : HasSqLift M (tP M * yP M) M.xK :=
  ⟨M.wK * M.yK, by rw [map_mul]; rfl, Subtype.ext (wy_sq F)⟩

theorem not_isConj_y_wy {M : ModelData F} (hZ : ZsTwo M) (h2 : (2 : F) ≠ 0) :
    ¬ IsConj (yP M) (tP M * yP M) := by
  intro h
  have h1 : HasSqLift M (tP M * yP M) 1 :=
    (hasSqLift_y M).conj (Subgroup.one_mem _) h
  have h3 := HasSqLift.unique hZ h1 (hasSqLift_wy M)
  have h4 : (1 : ↥M.K4) = M.xK := h3
  have h5 := M.orderOf_xK h2
  rw [← h4, orderOf_one] at h5
  omega

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
