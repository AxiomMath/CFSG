module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Lb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  DiagL CSL Subgroup

namespace L4M

variable {F : Type} [Field F]

theorem proj_neg_one : proj 4 F (-1) = 1 := by
  rw [proj_eq_one_iff, mem_scalars]
  refine ⟨-1, by norm_num, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Units.val_neg,
    Units.val_one,
    map_neg, map_one]

theorem proj_eq_of_neg {A B : SpecialLinearGroup (Fin 4) F}
    (h : (A : Matrix (Fin 4) (Fin 4) F) = -(B : Matrix (Fin 4) (Fin 4) F)) :
    proj 4 F A = proj 4 F B := by
  have : A = -1 * B := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_mul, Matrix.one_mul, h])
  rw [this, map_mul, proj_neg_one, one_mul]

theorem commute_proj_of_neg {A B : SpecialLinearGroup (Fin 4) F}
    (h : (A : Matrix (Fin 4) (Fin 4) F) * B = -((B : Matrix (Fin 4) (Fin 4) F) * A)) :
    Commute (proj 4 F A) (proj 4 F B) := by
  show proj 4 F A * proj 4 F B = proj 4 F B * proj 4 F A
  rw [← map_mul, ← map_mul]
  exact proj_eq_of_neg (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h])

theorem commute_proj_of_eq {A B : SpecialLinearGroup (Fin 4) F}
    (h : (A : Matrix (Fin 4) (Fin 4) F) * B = (B : Matrix (Fin 4) (Fin 4) F) * A) :
    Commute (proj 4 F A) (proj 4 F B) := by
  show proj 4 F A * proj 4 F B = proj 4 F B * proj 4 F A
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h])

theorem proj_ne_one_of_apply {A : SpecialLinearGroup (Fin 4) F}
    (h : (A : Matrix (Fin 4) (Fin 4) F) 0 0 = 0) : proj 4 F A ≠ 1 := by
  intro h1
  rw [proj_eq_one_iff, mem_scalars] at h1
  obtain ⟨c, -, hc⟩ := h1
  have := congrFun (congrFun hc 0) 0
  rw [h, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact c.ne_zero this.symm

variable {x y : F} (hxy : x ^ 2 + y ^ 2 = -1)

@[expose] def sA : SpecialLinearGroup (Fin 4) F := ⟨aM x y, det_aM hxy⟩

@[expose] def sT : SpecialLinearGroup (Fin 4) F := ⟨tM x y, det_tM hxy⟩

@[expose] def sW : SpecialLinearGroup (Fin 4) F := ⟨wK, det_wK⟩

@[expose] def sK : SpecialLinearGroup (Fin 4) F := ⟨kpM, det_kpM⟩

theorem coe_sT_inv : (((sT hxy)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    tiM x y :=
  coe_inv_eq' (tM_mul_tiM hxy)

theorem coe_sW_inv : (((sW : SpecialLinearGroup (Fin 4) F)⁻¹ : SpecialLinearGroup (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = -wK :=
  coe_inv_eq' (by
    change wK * -wK = 1
    rw [Matrix.mul_neg, wK_mul_wK, neg_neg])

theorem coe_conj_sA : (((sT hxy)⁻¹ * sA hxy * sT hxy : SpecialLinearGroup (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = apM x y := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sT_inv]
  exact tiM_aM_tM hxy

theorem coe_conj_sW : (((sT hxy)⁻¹ * sW * sT hxy : SpecialLinearGroup (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = wpM x y := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sT_inv]
  exact tiM_wK_tM

theorem coe_sA_pow (j : ℕ) : ((sA hxy ^ j : SpecialLinearGroup (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = bd (zM x y ^ j) (zM (-x) y ^ j) := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact bd_pow _ _ j

include hxy in
theorem zM_neg_pow {j : ℕ} {P : Matrix (Fin 2) (Fin 2) F} (hP : zM x y ^ j = P)
    (hPP : P * -P = 1) : zM (-x) y ^ j = -P := by
  calc zM (-x) y ^ j = zM (-x) y ^ j * (P * -P) := by rw [hPP, Matrix.mul_one]
    _ = (zM (-x) y * zM x y) ^ j * -P := by
        rw [(show Commute (zM (-x) y) (zM x y) from zM_comm (-x) y x y).mul_pow, hP,
          Matrix.mul_assoc]
    _ = -P := by rw [zM_neg_mul_zM hxy, one_pow, Matrix.one_mul]

theorem coe_sA_half {m : ℕ} (hZ : zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap) :
    ((sA hxy ^ 2 ^ (m - 1) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = kpM ∨
      ((sA hxy ^ 2 ^ (m - 1) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        -kpM := by
  rw [coe_sA_pow]
  rcases hZ with h | h
  · left
    rw [h, zM_neg_pow hxy h (by rw [Matrix.mul_neg, kap_mul_kap, neg_neg]), kpM]
  · right
    rw [h, zM_neg_pow hxy h (by rw [neg_neg, Matrix.neg_mul, kap_mul_kap, neg_neg]), kpM,
      ← bd_neg]

theorem proj_sA_half {m : ℕ} (hZ : zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap) :
    proj 4 F (sA hxy) ^ 2 ^ (m - 1) = proj 4 F sK := by
  rw [← map_pow]
  rcases coe_sA_half hxy hZ with h | h
  · exact congrArg (proj 4 F) (Subtype.ext h)
  · exact proj_eq_of_neg h

theorem proj_sK_mul : proj 4 F (sK : SpecialLinearGroup (Fin 4) F) * proj 4 F sK = 1 := by
  rw [← map_mul, ← proj_neg_one]
  congr 1
  exact Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact kpM_mul_kpM)

theorem proj_sK_ne_one : proj 4 F (sK : SpecialLinearGroup (Fin 4) F) ≠ 1 :=
  proj_ne_one_of_apply kpM_apply_zero_zero

theorem proj_sA_pow {m : ℕ} (hm : 1 ≤ m)
    (hZ : zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap) :
    proj 4 F (sA hxy) ^ 2 ^ m = 1 := by
  have e : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e, pow_mul, proj_sA_half hxy hZ, sq, proj_sK_mul]

theorem orderOf_proj_sA {m : ℕ} (hm : 1 ≤ m)
    (hZ : zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap) :
    orderOf (proj 4 F (sA hxy)) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : m = m - 1 + 1 := by omega
  have h := orderOf_eq_prime_pow (p := 2) (x := proj 4 F (sA hxy)) (n := m - 1)
    (by rw [proj_sA_half hxy hZ]; exact proj_sK_ne_one)
    (by rw [← e]; exact proj_sA_pow hxy hm hZ)
  rwa [← e] at h

theorem proj_sW_mul : proj 4 F (sW : SpecialLinearGroup (Fin 4) F) * proj 4 F sW = 1 := by
  rw [← map_mul, ← proj_neg_one]
  congr 1
  exact Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact wK_mul_wK)

theorem proj_sW_conj : proj 4 F (sW : SpecialLinearGroup (Fin 4) F) * proj 4 F (sA hxy) *
    (proj 4 F sW)⁻¹ = (proj 4 F (sA hxy))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  have : (sW : SpecialLinearGroup (Fin 4) F) * sA hxy * sW⁻¹ * sA hxy = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,
      coe_sW_inv, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_neg, Matrix.neg_mul]
    change -(wK * aM x y * wK * aM x y) = 1
    rw [wK_aM_wK_aM hxy, neg_neg])
  rw [this, map_one]

theorem proj_sW_mul_pow_ne_one (i : ℕ) :
    proj 4 F (sW : SpecialLinearGroup (Fin 4) F) * proj 4 F (sA hxy) ^ i ≠ 1 := by
  rw [← map_pow, ← map_mul]
  apply proj_ne_one_of_apply
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sA_pow]
  exact wK_mul_bd_apply _ _

theorem sW_mem_SK (h2 : (2 : F) ≠ 0) :
    (sW : SpecialLinearGroup (Fin 4) F) ∈ SK F neg_one_ne_zero' := by
  have hl1 : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have : (sW : SpecialLinearGroup (Fin 4) F) = slUK (-1) 1 0 * slLK (-1) (-1) 0 * slUK (-1) 1 0 :=
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact wK_eq (-1))
  rw [this]
  exact mul_mem (mul_mem (slUK_mem_SK _ hl1 1 0) (slLK_mem_SK _ hl1 (-1) 0))
    (slUK_mem_SK _ hl1 1 0)

theorem sA_mem_SK (h2 : (2 : F) ≠ 0) : sA hxy ∈ SK F neg_one_ne_zero' := by
  have hl1 : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have : sA hxy = slUK (-1) x y * slLK (-1) x (-y) * slUK (-1) x y * sW⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul]
      exact aM_wK hxy)
  rw [this]
  exact mul_mem (mul_mem (mul_mem (slUK_mem_SK _ hl1 x y) (slLK_mem_SK _ hl1 x (-y)))
    (slUK_mem_SK _ hl1 x y)) (inv_mem (sW_mem_SK h2))

theorem JK_le_cent : JK F neg_one_ne_zero' ≤
    centralizer ({proj 4 F kSL} : Set (projectiveSL 4 F)) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact (mem_CK_iff neg_one_ne_zero').1 (mem_CK_of_mem_SK neg_one_ne_zero' hs)

theorem gamma_mem : proj 4 F sK * ((proj 4 F (sT hxy))⁻¹ * proj 4 F (sA hxy) * proj 4 F (sT hxy)) ∈
    centralizer (JK F neg_one_ne_zero' : Set (projectiveSL 4 F)) := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  have hU : ((sK * ((sT hxy)⁻¹ * sA hxy * sT hxy) : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = eK (-1) (-y) x := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_conj_sA hxy]
    exact kpM_apM
  have hCA := conj_mem_CA_of_eK neg_one_ne_zero' hU
  rw [mem_centralizer_iff]
  intro s hs
  have := hCA s hs
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem sup_le_map_CK [Finite F] (h4 : (4 : F) ≠ 0) :
    JK F neg_one_ne_zero' ⊔ centralizer (JK F neg_one_ne_zero' : Set (projectiveSL 4 F)) ≤
      (CK F neg_one_ne_zero').map (proj 4 F) := by
  refine sup_le (Subgroup.map_mono (fun s hs => mem_CK_of_mem_SK neg_one_ne_zero' hs)) ?_
  intro g hg
  have hCA : MulAut.conj g ∈ CA F neg_one_ne_zero' := by
    intro s hs
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.mp hg s hs).symm
  obtain ⟨U, hU, a, b, hUe⟩ := exists_lift_eK h4 hCA
  refine ⟨U, (mem_CK_iff neg_one_ne_zero').2 ?_, hU⟩
  rw [hUe]
  exact (eK_comm_of_comm (X := kZero (-1)) (-1) a b rfl).symm

theorem conj_sW_not_mem [Finite F] (h2 : (2 : F) ≠ 0) :
    (proj 4 F (sT hxy))⁻¹ * proj 4 F sW * proj 4 F (sT hxy) ∉
      JK F neg_one_ne_zero' ⊔ centralizer (JK F neg_one_ne_zero' : Set (projectiveSL 4 F)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  intro h
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨c, hc, hce⟩ := sup_le_map_CK h4 h
  rw [proj_eq_proj_iff] at hce
  obtain ⟨d, -, hd⟩ := mem_scalars.1 hce
  have hVc : (((sT hxy)⁻¹ * sW * sT hxy : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = (d : F) • (c : Matrix (Fin 4) (Fin 4) F) := by
    rw [← mul_inv_cancel_left c ((sT hxy)⁻¹ * sW * sT hxy), Matrix.SpecialLinearGroup.coe_mul, hd,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hck := (mem_CK_iff neg_one_ne_zero').1 hc
  have hVk : (((sT hxy)⁻¹ * sW * sT hxy : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) * kZero (-1) =
      kZero (-1) * (((sT hxy)⁻¹ * sW * sT hxy : SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) := by
    rw [hVc, Matrix.smul_mul, hck, Matrix.mul_smul]
  rw [coe_conj_sW hxy, kZero_wpM] at hVk
  have h02 := congrFun (congrFun hVk 0) 2
  have h03 := congrFun (congrFun hVk 0) 3
  rw [Matrix.neg_apply, (wpM_kZero_apply x y).1] at h02
  rw [Matrix.neg_apply, (wpM_kZero_apply x y).2] at h03
  have hy : y = 0 := by
    have : (2 : F) * y = 0 := by linear_combination -h02
    exact (mul_eq_zero.1 this).resolve_left h2
  have hx : x = 0 := by
    have : (2 : F) * x = 0 := by linear_combination -h03
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [hx, hy] at hxy
  norm_num at hxy

theorem iota_eq : proj 4 F kSL =
    (proj 4 F (sT hxy))⁻¹ * proj 4 F sK * proj 4 F (sT hxy) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sT_inv]
  exact (tiM_kpM_tM hxy).symm

theorem sT_sq : proj 4 F (sT hxy) * proj 4 F (sT hxy) = proj 4 F kSL * proj 4 F sK := by
  rw [← map_mul, ← map_mul]
  apply proj_eq_of_neg
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact tM_mul_tM hxy

theorem not_conj (hneg : ¬ IsSquare (-1 : F)) (g : projectiveSL 4 F) :
    g * proj 4 F kSL * g⁻¹ ≠ proj 4 F kSL * proj 4 F sK := by
  intro h
  obtain ⟨G, rfl⟩ := proj_surjective 4 F g
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  set X : SpecialLinearGroup (Fin 4) F := G * kSL * G⁻¹ with hX
  have hY : ((kSL * sK : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (X : Matrix (Fin 4) (Fin 4) F) * scalar (Fin 4) (c : F) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hX2 : (X : Matrix (Fin 4) (Fin 4) F) * X = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hX,
      show G * kSL * G⁻¹ * (G * kSL * G⁻¹) = G * (kSL * kSL) * G⁻¹ by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    change (G : Matrix (Fin 4) (Fin 4) F) * (kZero (-1) * kZero (-1)) * _ = _
    rw [kZero_mul_kZero, neg_one_smul, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hY2 : ((kSL * sK : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((kSL * sK : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact kZero_kpM_sq
  have hcomm : Commute (scalar (Fin 4) (c : F)) (X : Matrix (Fin 4) (Fin 4) F) :=
    Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
  have key : (1 : Matrix (Fin 4) (Fin 4) F) = -(scalar (Fin 4) ((c : F) * c)) := by
    rw [← hY2, hY, hcomm.mul_mul_mul_comm, hX2, Matrix.neg_mul, Matrix.one_mul, map_mul]
  have h00 := congrFun (congrFun key 0) 0
  rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  exact hneg ⟨c, by linear_combination -h00⟩

end L4M

end CFSG.ComponentClassification.GSThmB.P29
