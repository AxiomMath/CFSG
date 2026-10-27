module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Uc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Ld

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut UnitaryConj HBlocks StabU DiagU CSU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank Subgroup DihedralGroup

namespace U4M

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def JU (Y : unitarySU p f K 4) :
    Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
  (⁅(Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap (unitarySU p f K 4).subtype,
    (Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap (unitarySU p f K 4).subtype⁆ :
      Subgroup (unitarySU p f K 4)).map (thU p f K)

theorem JU_le_cent (Y : unitarySU p f K 4) :
    JU Y ≤ centralizer ({thU p f K Y} : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
  rintro _ ⟨g, hg, rfl⟩
  have hgC : g ∈ (Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap (unitarySU p f K 4).subtype :=
    (Subgroup.commutator_le.2 fun a ha b hb =>
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hg
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff] at hgC
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hgC

variable (h : UnitaryFieldData p f K)

theorem wpH_X1_apply (z w l : K) : (wpH z w * X1 l : Matrix (Fin 4) (Fin 4) K) 0 3 = l * w := by
  simp [X1, wpH, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem nonempty_modelU (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {Y : unitarySU p f K 4} {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l = l)
    (hYP : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = P * X1 l)
    {z w : K} (hzw : z * w = 1) (hbz : h.bar z = -z) (hbw : h.bar w = -w) {m : ℕ} (hm : 2 ≤ m)
    (hzl : z ^ 2 ^ (m - 1) = l ∨ z ^ 2 ^ (m - 1) = -l) (hJp : ⁅JU Y, JU Y⁆ = JU Y)
    (hJc : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card (JU Y))
    (hJZ : JU Y ⊓ centralizer (JU Y : Set (StatedProj (StatedSU 4 (p ^ f) K))) = ⊥)
    (hL1 : 2 ^ (2 * m + 3) ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)))
    (hL2 : ¬ 2 ^ (2 * m + 4) ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)))
    (hJ2 : ¬ 2 ^ (m + 2) ∣ Nat.card (JU Y)) :
    Nonempty (Model (⊤ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) (thU p f K Y) (JU Y) m) := by
  classical
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hzw
    exact zero_ne_one hzw
  have hY : cP P Y = X1 l := by
    rw [cP, Matrix.mul_assoc, hYP, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hα := isCU_conj h Y
  have hfix : ∀ x ∈ JU Y, MulAut.conj (thU p f K Y) x = x := by
    intro x hx
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_singleton_iff.mp (JU_le_cent Y hx)).symm
  obtain ⟨hJU, hJL, -⟩ := eq_of_perfect_diag h hp2 P hP hl0 hα hYP hfix hJp hJc
  have hm1 : 1 ≤ m := by omega
  set a := thU p f K (mA h P hP hzw hbz hbw) with ha_def
  set b := thU p f K (mW h P hP) with hb_def
  set t := thU p f K (mT h P hP hzw hbz hbw) with ht_def
  have ha : a ^ 2 ^ m = 1 := thU_mA_pow h P hP hzw hbz hbw hl hbl hm hzl
  have hb : b * b = 1 := thU_mW_mul h P hP
  have hba : b * a * b⁻¹ = a⁻¹ := thU_mW_conj h P hP hzw hbz hbw
  have h1m : 1 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm1)
  have hval1 : (1 : ZMod (2 ^ m)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1m]
  have hz : dihHom a b ha hb hba (r (cc m)) = thU p f K (mK h P hP hl hbl) := by
    rw [dihHom_r, val_cc hm, thU_mA_half h P hP hzw hbz hbw hl hbl hm hzl]
  have hr1 : dihHom a b ha hb hba (r 1) = a := by rw [dihHom_r, hval1, pow_one]
  have hs0 : dihHom a b ha hb hba (sr 0) = b := by rw [dihHom_sr, ZMod.val_zero, pow_zero, mul_one]
  have hconj : ∀ X : unitarySU p f K 4, t⁻¹ * thU p f K X * t =
      thU p f K ((mT h P hP hzw hbz hbw)⁻¹ * X * mT h P hP hzw hbz hbw) := fun X => by
    rw [ht_def, map_mul, map_mul, map_inv]
  have hc1 : t⁻¹ * a * t = thU p f K ((mT h P hP hzw hbz hbw)⁻¹ * mA h P hP hzw hbz hbw *
      mT h P hP hzw hbz hbw) := by rw [ha_def, hconj]
  have hc2 : t⁻¹ * b * t =
      thU p f K ((mT h P hP hzw hbz hbw)⁻¹ * mW h P hP * mT h P hP hzw hbz hbw) := by
    rw [hb_def, hconj]
  have hbJ : b ∈ JU Y := by
    have e : mW h P hP = uU h P hP 1 * uL h P hP (-1) * uU h P hP 1 := by
      apply eq_of_cP_eq P
      rw [cP_mW, cP_mul, cP_mul, uU, uL, cP_hypSU, cP_hypSU, Wm_eq_U h]
    rw [hb_def, e, map_mul, map_mul]
    exact mul_mem (mul_mem (hJU 1) (hJL (-1))) (hJU 1)
  have haJ : a ∈ JU Y := by
    have e : mA h P hP hzw hbz hbw =
        uU h P hP z * uL h P hP (-w) * uU h P hP z * (mW h P hP)⁻¹ := by
      apply eq_of_cP_eq P
      rw [cP_mA, cP_mul, cP_mul, cP_mul, cP_mW_inv, uU, uL, cP_hypSU, cP_hypSU,
        ← aH_Wm h hzw hbz hbw, Matrix.mul_neg, Matrix.mul_assoc, Wm_mul_Wm, Matrix.mul_neg,
        Matrix.mul_one, neg_neg]
    rw [ha_def, e, map_mul, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (mul_mem (hJU z) (hJL (-w))) (hJU z)) (inv_mem hbJ)
  refine ⟨{
    ρ := dihHom a b ha hb hba
    t₀ := t
    two_le := hm
    inj := dihHom_injective ha hb hba (orderOf_thU_mA h P hP hzw hbz hbw hl hbl hp2 hm hzl)
      (thU_mW_mul_pow_ne_one h P hP hzw hbz hbw)
    le_J := ?_
    J_le_L := le_top
    t₀_mem := mem_top _
    J_le := JU_le_cent Y
    normJ := fun c hc y => normalizes_of_comm h hp2 hα rfl (by
      rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp hc.1).symm]) y
    inf_cent := hJZ
    comm := ?_
    gamma := ?_
    sr_not := ?_
    iota := ?_
    sq := ?_
    not_conj := ?_
    dvd_L := by rw [Subgroup.card_top]; exact hL1
    not_dvd_L := by rw [Subgroup.card_top]; exact hL2
    not_dvd_J := hJ2 }⟩
  · intro x
    cases x with
    | r i =>
      rw [dihHom_r]
      exact pow_mem haJ _
    | sr i =>
      rw [dihHom_sr]
      exact mul_mem hbJ (pow_mem haJ _)
  · refine dihHom_conj_comm ha hb hba ?_ ?_ ?_ ?_
    · rw [hc1, ha_def]
      exact commute_thU_of_cP P (by rw [cP_conj_mA, cP_mA]; exact apH_aH)
    · rw [hc1, hb_def]
      refine commute_thU_of_cP_neg P ?_
      rw [cP_conj_mA, cP_mW, Wm_apH, neg_neg]
    · rw [hc2, ha_def]
      refine commute_thU_of_cP_neg P ?_
      rw [cP_conj_mW, cP_mA, aH_wpH, neg_neg]
    · rw [hc2, hb_def]
      refine commute_thU_of_cP_neg P ?_
      rw [cP_conj_mW, cP_mW, Wm_wpH, neg_neg]
  · rw [hz, hr1, hc1, ← map_mul]
    have hU : cP P (mK h P hP hl hbl * ((mT h P hP hzw hbz hbw)⁻¹ * mA h P hP hzw hbz hbw *
        mT h P hP hzw hbz hbw)) = blk (l * z) 0 0 (l * w) := by
      rw [cP_mul, cP_mK, cP_conj_mA, kH_apH]
    have hCA := conj_mem_CAU_of_blk h hp2 P hl0 hYP rfl hU
    rw [mem_centralizer_iff]
    intro x hx
    have := hCA x hx
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · rw [hs0, hc2]
    intro hmem
    set C := (Subgroup.centralizer {(Y : GL (Fin 4) K)}).comap (unitarySU p f K 4).subtype
      with hCdef
    have hle : JU Y ⊔ centralizer (JU Y : Set (StatedProj (StatedSU 4 (p ^ f) K))) ≤
        C.map (thU p f K) := by
      refine sup_le (Subgroup.map_mono (Subgroup.commutator_le.2 fun a ha b hb =>
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) ?_
      intro g hg
      obtain ⟨G, rfl⟩ := thU_surjective g
      have hCAU : MulAut.conj (thU p f K G) ∈ CAU (JU Y) := by
        intro x hx
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
        exact (mem_centralizer_iff.mp hg x hx).symm
      obtain ⟨x, y, hxy, -⟩ := blk_of_mem_AU h hp2 P hP hJU hJL (isCU_conj h G) hCAU
      refine ⟨G, (mem_C_iff P hYP G).2 ?_, rfl⟩
      have hcG : cP P G = blk x 0 0 y := by
        rw [← hxy, Units.val_mul, Units.val_mul]
        rfl
      rw [hcG, blk_eq_dg, X1_eq_dg, dg_mul_dg, dg_mul_dg]
      congr 1 <;> ring
    obtain ⟨c, hc, hce⟩ := hle hmem
    obtain ⟨d, hd⟩ := cP_of_thU_eq P hce.symm
    have hcomm := (mem_C_iff P hYP c).1 hc
    rw [hd, cP_conj_mW, Matrix.smul_mul, Matrix.mul_smul] at hcomm
    have e1 := congrFun (congrFun hcomm 0) 3
    rw [Matrix.smul_apply, Matrix.smul_apply, wpH_X1_apply, X1_wpH_apply, smul_eq_mul,
      smul_eq_mul] at e1
    have e2 : (2 : K) * ((d : K) * (l * w)) = 0 := by linear_combination e1
    exact mul_ne_zero (two_ne_zero_of_odd h hp2) (mul_ne_zero d.ne_zero (mul_ne_zero hl0 hw0)) e2
  · rw [hz, ht_def]
    exact iota_eqU h P hP hzw hbz hbw hl hbl hY
  · rw [hz, ht_def]
    exact mT_sqU h P hP hzw hbz hbw hl hbl hY
  · intro g _
    rw [hz]
    exact not_conjU h P hP hl hbl hp2 hq hY g

end U4M

end CFSG.ComponentClassification.GSThmB.P29
