module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmQuot
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremA.S8

variable {w : ℕ}

theorem card_F4' : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [card_F4]
  norm_num

theorem five_dvd_card_statedSU (hw : 4 ≤ w) : 5 ∣ Nat.card (StatedSU w 2 F4) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F4 :=
    ⟨Nat.prime_two, le_rfl, by rw [card_F4]; norm_num⟩
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq h (n := w) (by omega)
  have hdiv : (5 : ℤ) ∣ ∏ i ∈ Finset.Icc 2 w, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (show 4 ∈ Finset.Icc 2 w by
      simp only [Finset.mem_Icc]; omega))
    norm_num
  have hZ : (5 : ℤ) ∣ (Nat.card (StatedSU w (2 ^ 1) F4) : ℤ) := by
    rw [hc]
    exact dvd_mul_of_dvd_right hdiv _
  rw [pow_one] at hZ
  exact_mod_cast hZ




abbrev PGU (w : ℕ) : Type := StatedProj (unitSub w)

noncomputable def mkY (w : ℕ) : ↥(unitSub w) →* PGU w := QuotientGroup.mk' _

theorem mkY_surjective (w : ℕ) : Function.Surjective (mkY w) := QuotientGroup.mk'_surjective _

noncomputable def detU (w : ℕ) : ↥(unitSub w) →* F4ˣ :=
  (Matrix.GeneralLinearGroup.det : GL (Fin w) F4 →* Units F4).comp (unitSub w).subtype

noncomputable def SUg (w : ℕ) : Subgroup ↥(unitSub w) := (detU w).ker

theorem mem_SUg_iff (g : ↥(unitSub w)) :
    g ∈ SUg w ↔ (g : GL (Fin w) F4) ∈ StatedSU w 2 F4 := by
  rw [mem_statedSU_iff]
  unfold SUg detU
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← Units.val_eq_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  constructor
  · intro h
    exact ⟨h, g.2⟩
  · intro h
    exact h.1

theorem statedSU_le_unitSub (w : ℕ) : StatedSU w 2 F4 ≤ unitSub w := by
  intro A hA
  exact ((mem_statedSU_iff A).1 hA).2

instance SUg_normal (w : ℕ) : (SUg w).Normal := by
  unfold SUg
  infer_instance

noncomputable def Ysu (w : ℕ) : Subgroup (PGU w) := (SUg w).map (mkY w)

instance Ysu_normal (w : ℕ) : (Ysu w).Normal :=
  Subgroup.Normal.map inferInstance _ (mkY_surjective w)

theorem five_element_statedSU (hw : 4 ≤ w) :
    ∃ g : GL (Fin w) F4, g ∈ StatedSU w 2 F4 ∧ orderOf g = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(StatedSU w 2 F4)) 5
    (five_dvd_card_statedSU hw)
  refine ⟨(x : GL (Fin w) F4), x.2, ?_⟩
  rw [Subgroup.orderOf_coe, hx]

theorem five_power_mem_Ysu (y : PGU w) (k : ℕ) (hy : y ^ (5 ^ k) = 1) : y ∈ Ysu w := by
  obtain ⟨g, rfl⟩ := mkY_surjective w y
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pow_zero, pow_one] at hy
    rw [hy]
    exact Subgroup.one_mem _
  have hm2 : 2 ≤ 5 ^ k := by
    have : 5 ^ 1 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hcop : Nat.Coprime 3 (5 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hφ : 0 < Nat.totient (5 ^ k) := Nat.totient_pos.2 (by omega)
  have he1 : 3 ^ Nat.totient (5 ^ k) % 5 ^ k = 1 := by
    have h := Nat.ModEq.pow_totient hcop
    unfold Nat.ModEq at h
    rw [h, Nat.mod_eq_of_lt (by omega : 1 < 5 ^ k)]
  have h3e : 3 ∣ 3 ^ Nat.totient (5 ^ k) := dvd_pow_self 3 hφ.ne'
  have hye : (mkY w g) ^ (3 ^ Nat.totient (5 ^ k)) = mkY w g := by
    rw [pow_eq_pow_mod _ hy, he1, pow_one]
  have hdet : ((((g ^ (3 ^ Nat.totient (5 ^ k)) : ↥(unitSub w)) : GL (Fin w) F4) :
      Matrix (Fin w) (Fin w) F4)).det = 1 := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow]
    obtain ⟨t, ht⟩ := h3e
    have h3 := det_pow_three_of_unitary (B := ((g : GL (Fin w) F4) : Matrix (Fin w) (Fin w) F4))
      g.2
    rw [ht, pow_mul, h3, one_pow]
  have hmem : g ^ (3 ^ Nat.totient (5 ^ k)) ∈ SUg w := by
    rw [mem_SUg_iff, mem_statedSU_iff]
    exact ⟨hdet, (g ^ (3 ^ Nat.totient (5 ^ k))).2⟩
  exact ⟨g ^ (3 ^ Nat.totient (5 ^ k)), hmem, by rw [map_pow, hye]⟩

theorem mem_statedScalars_iff (g : GL (Fin w) F4) :
    g ∈ StatedScalars (Fin w) F4 ↔ ∃ c : F4ˣ, (g : Matrix (Fin w) (Fin w) F4) = (c : F4) • 1 := by
  unfold StatedScalars
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, Matrix.diagonal_apply]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext ?_⟩
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, hc, Matrix.one_apply, Matrix.diagonal_apply]

theorem scalar_cube_eq_one (g : GL (Fin w) F4) (hg : g ∈ StatedScalars (Fin w) F4) :
    g ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := (mem_statedScalars_iff g).1 hg
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hc, smul_pow, one_pow, Units.val_one]
  rw [pow_three_of_ne_zero c.ne_zero, one_smul]

noncomputable def iSU (w : ℕ) : ↥(StatedSU w 2 F4) →* ↥(unitSub w) :=
  Subgroup.inclusion (statedSU_le_unitSub w)

noncomputable def FSU (w : ℕ) : ↥(StatedSU w 2 F4) →* PGU w := (mkY w).comp (iSU w)

theorem mkY_eq_one_iff (x : ↥(unitSub w)) :
    mkY w x = 1 ↔ (x : GL (Fin w) F4) ∈ StatedScalars (Fin w) F4 := by
  unfold mkY
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem range_FSU (w : ℕ) : (FSU w).range = Ysu w := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(iSU w g : ↥(unitSub w)), (mem_SUg_iff _).2 g.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, ((mem_SUg_iff x).1 hx)⟩, rfl⟩

theorem ker_FSU (w : ℕ) : (FSU w).ker = (StatedScalars (Fin w) F4).subgroupOf (StatedSU w 2 F4) := by
  ext g
  rw [MonoidHom.mem_ker, FSU, MonoidHom.comp_apply, mkY_eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem Ysu_simple (hw : 12 ≤ w) : IsSimpleGroup ↥(Ysu w) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 card_F4' w
    (by omega)
    (by intro h; simp only [Prod.mk.injEq] at h; omega)
  rw [pow_one] at hS
  let e1 : ↥(StatedSU w 2 F4) ⧸ (FSU w).rangeRestrict.ker ≃* ↥(FSU w).range :=
    QuotientGroup.quotientKerEquivOfSurjective (FSU w).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hker : (FSU w).rangeRestrict.ker = (StatedScalars (Fin w) F4).subgroupOf (StatedSU w 2 F4) := by
    rw [MonoidHom.ker_rangeRestrict, ker_FSU]
  let e2 : StatedProj (StatedSU w 2 F4) ≃* ↥(FSU w).range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e1
  let e3 : ↥(FSU w).range ≃* ↥(Ysu w) := MulEquiv.subgroupCongr (range_FSU w)
  exact MulEquiv.isSimpleGroup (e2.trans e3).symm

theorem oPrimeRes_PGU (hw : 12 ≤ w) : oPrimeRes 5 (PGU w) = Ysu w := by
  apply le_antisymm
  · unfold oPrimeRes
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨k, hk⟩
    exact five_power_mem_Ysu y k hk
  · intro y hy
    haveI := Ysu_simple hw
    let H : Subgroup ↥(Ysu w) := (oPrimeRes 5 (PGU w)).subgroupOf (Ysu w)
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := ↥(Ysu w)) H) with h | h
    · exfalso
      obtain ⟨g, hg, hg5⟩ := five_element_statedSU (w := w) (by omega)
      have hgu : g ∈ unitSub w := statedSU_le_unitSub w hg
      let gu : ↥(unitSub w) := ⟨g, hgu⟩
      have hgSU : gu ∈ SUg w := (mem_SUg_iff gu).2 hg
      have hmemY : mkY w gu ∈ Ysu w := ⟨gu, hgSU, rfl⟩
      have hz : (⟨mkY w gu, hmemY⟩ : ↥(Ysu w)) ∈ H := by
        rw [Subgroup.mem_subgroupOf]
        apply Subgroup.subset_normalClosure
        refine ⟨1, ?_⟩
        rw [pow_one, ← map_pow]
        have h5 : gu ^ 5 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          rw [← hg5]
          exact pow_orderOf_eq_one g
        rw [h5, map_one]
      rw [h, Subgroup.mem_bot] at hz
      have hz1 : mkY w gu = 1 := congrArg Subtype.val hz
      have hgs : (gu : GL (Fin w) F4) ∈ StatedScalars (Fin w) F4 := (mkY_eq_one_iff gu).1 hz1
      have h3 : g ^ 3 = 1 := scalar_cube_eq_one g hgs
      have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      rw [hg5] at hdvd
      norm_num at hdvd
    · have hmem : (⟨y, hy⟩ : ↥(Ysu w)) ∈ H := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem

theorem isSimpleGroup_oPrimeRes_PGU (hw : 12 ≤ w) : IsSimpleGroup ↥(oPrimeRes 5 (PGU w)) := by
  rw [oPrimeRes_PGU hw]
  exact Ysu_simple hw

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
