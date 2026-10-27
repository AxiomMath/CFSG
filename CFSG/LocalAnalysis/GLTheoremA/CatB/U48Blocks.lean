module

public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Layer
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Aux
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

noncomputable section

@[expose] def yStd (t : μ3) : SU4 := torusSU4 fun _ => t

theorem coe_yStd (t : μ3) :
    (((yStd t : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun k => if k = 3 then (1 : K) else ((t : Kˣ) : K) := by
  rw [yStd, coe_torusSU4]
  congr 1
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.torusSnoc_last]
    have h3 : ((t : Kˣ)) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp t.2
    simp [Fin.prod_const, h3]
  · rw [CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.torusSnoc_castSucc]
    have : (Fin.castSucc i : Fin 4) ≠ 3 := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]

theorem yStd_pow_three (t : μ3) : yStd t ^ 3 = 1 := by
  rw [yStd, ← map_pow]
  have : (fun _ : Fin 3 => t) ^ 3 = 1 := funext fun i => by
    have h3 : ((t : Kˣ)) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp t.2
    exact Subtype.ext h3
  rw [this, map_one]

theorem mem_centralizer_yStd {t : μ3} (ht : (t : Kˣ) ≠ 1) (g : SU4) :
    g ∈ Subgroup.centralizer ({yStd t} : Set SU4) ↔
      ∀ i : Fin 4, i ≠ 3 → (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i 3 = 0 ∧
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 i = 0) := by
  have ht' : ((t : Kˣ) : K) ≠ 1 := fun h => ht (Units.ext h)
  have hsub : ((t : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr ht'
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i hi
    have h' := congrArg (fun z : SU4 => ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_yStd] at h'
    have e1 := congrFun (congrFun h' i) 3
    have e2 := congrFun (congrFun h' 3) i
    simp only [mul_diagonal, diagonal_mul, if_pos rfl, if_neg hi, ite_true] at e1 e2
    constructor
    · have : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i 3) * (1 - ((t : Kˣ) : K)) = 0 := by
        linear_combination e1
      rcases mul_eq_zero.mp this with h0 | h0
      · exact h0
      · exact absurd (by linear_combination -h0) hsub
    · have : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 i) * (1 - ((t : Kˣ) : K)) = 0 := by
        linear_combination -e2
      rcases mul_eq_zero.mp this with h0 | h0
      · exact h0
      · exact absurd (by linear_combination -h0) hsub
  · intro h
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_yStd]
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases hi : i = 3 <;> by_cases hj : j = 3
    · subst hi; subst hj; simp
    · subst hi
      have := (h j hj).2
      simp [hj, this]
    · subst hj
      have := (h i hi).1
      simp [hi, this]
    · simp [hi, hj]
      ring

abbrev ent (g : SU4) (i j : Fin 4) : K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j

abbrev Cstd (t : μ3) : Subgroup SU4 := Subgroup.centralizer ({yStd t} : Set SU4)

section Rho

variable {t : μ3} (ht : (t : Kˣ) ≠ 1)

include ht in
theorem ent_mul_33 (g h : ↥(Cstd t)) : ent (g * h).1 3 3 = ent g.1 3 3 * ent h.1 3 3 := by
  have hg := (mem_centralizer_yStd ht g.1).1 g.2
  change ((((g.1 * h.1 : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3) = _
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four]
  rw [(hg 0 (by decide)).2, (hg 1 (by decide)).2, (hg 2 (by decide)).2]
  simp [ent]

include ht in
theorem ent_33_ne_zero (g : ↥(Cstd t)) : ent g.1 3 3 ≠ 0 := by
  intro h0
  have h1 : ent (g * g⁻¹).1 3 3 = 1 := by rw [mul_inv_cancel]; simp [ent]
  rw [ent_mul_33 ht, h0, zero_mul] at h1
  exact zero_ne_one h1

@[expose] def rho : ↥(Cstd t) →* Kˣ where
  toFun g := Units.mk0 (ent g.1 3 3) (ent_33_ne_zero ht g)
  map_one' := by
    apply Units.ext
    simp [ent]
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    exact ent_mul_33 ht g h

include ht in
theorem rho_apply (g : ↥(Cstd t)) : ((rho ht g : Kˣ) : K) = ent g.1 3 3 := rfl

include ht in
theorem rho_pow_nine (g : ↥(Cstd t)) : rho ht g ^ 9 = 1 := by
  have hg := (mem_centralizer_yStd ht g.1).1 g.2
  have hU := g.1.2.2
  have e := congrFun (congrFun hU 3) 3
  simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_four,
    Matrix.one_apply_eq] at e
  rw [(hg 0 (by decide)).1, (hg 1 (by decide)).1, (hg 2 (by decide)).1] at e
  simp only [map_zero, zero_mul, zero_add] at e
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, rho_apply]
  have h8 : CFSG.LieType.BorelTits.unitaryInvolution K 2 3 (ent g.1 3 3) = ent g.1 3 3 ^ 8 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  change CFSG.LieType.BorelTits.unitaryInvolution K 2 3 (ent g.1 3 3) * ent g.1 3 3 = 1 at e
  rw [h8] at e
  calc ent g.1 3 3 ^ 9 = ent g.1 3 3 ^ 8 * ent g.1 3 3 := by ring
    _ = 1 := e

open CFSG.ClassicalInvolution.Phan (blockEmb blockEmb_injective mem_range_blockEmb_iff
  coe_coe_blockEmb blockMat_apply_of_not_mem_left blockMat_apply_of_not_mem_right)

abbrev Jblk : Subgroup SU4 := (blockEmb K 2 3 4 3 0 (by norm_num)).range

theorem mem_Jblk_iff (g : SU4) :
    g ∈ Jblk ↔ g • (Pi.single 3 1 : Fin 4 → K) = Pi.single 3 1 := by
  rw [mem_range_blockEmb_iff]
  constructor
  · intro h
    exact h 3 (by simp)
  · intro h l hl
    have : l = 3 := by
      by_contra hne
      apply hl
      have : l.val ≠ 3 := fun h3 => hne (Fin.ext h3)
      have := l.isLt
      omega
    rw [this]; exact h

section Rho2

include ht in
theorem map_ker_rho : (rho ht).ker.map (Cstd t).subtype = Jblk := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxg := (mem_centralizer_yStd ht x.1).1 x.2
    have hx1 : ent x.1 3 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) (MonoidHom.mem_ker.1 hx)
      simpa [rho_apply] using this
    rw [Subgroup.coe_subtype, mem_Jblk_iff]
    funext a
    rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one]
    show ent x.1 a 3 = (Pi.single 3 1 : Fin 4 → K) a
    by_cases ha : a = 3
    · subst ha; simp [hx1]
    · simp [Pi.single_apply, ha, (hxg a ha).1]
  · intro hg
    obtain ⟨A, rfl⟩ := hg
    have hshape : ∀ i : Fin 4, i ≠ 3 →
        ent (blockEmb K 2 3 4 3 0 (by norm_num) A) i 3 = 0 ∧
          ent (blockEmb K 2 3 4 3 0 (by norm_num) A) 3 i = 0 := by
      intro i hi
      constructor
      · show ((((blockEmb K 2 3 4 3 0 (by norm_num) A : SU4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) i 3 = 0
        rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_right _ _ (by simp)]
        simp [Matrix.one_apply, hi]
      · show ((((blockEmb K 2 3 4 3 0 (by norm_num) A : SU4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) 3 i = 0
        rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ (by simp)]
        simp [Matrix.one_apply, hi.symm]
    have hmem : blockEmb K 2 3 4 3 0 (by norm_num) A ∈ Cstd t :=
      (mem_centralizer_yStd ht _).2 hshape
    refine ⟨⟨_, hmem⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    apply Units.ext
    rw [rho_apply]
    show ((((blockEmb K 2 3 4 3 0 (by norm_num) A : SU4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) 3 3 = ((1 : Kˣ) : K)
    rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ (by simp)]
    simp

@[expose] def kerEquiv : ↥(rho ht).ker ≃* CFSG.ClassicalInvolution.Phan.Su K 2 3 3 :=
  ((Subgroup.equivMapOfInjective (rho ht).ker (Cstd t).subtype (Cstd t).subtype_injective).trans
    (MulEquiv.subgroupCongr (map_ker_rho ht))).trans
    (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := 2) (f := 3)
      (by norm_num : 0 + 3 ≤ 4))).symm

include ht in
theorem isQuasisimple_ker : CFSG.Open.IsQuasisimple ↥(rho ht).ker := by
  have h := CFSG.GH74.L5U5.isQuasisimple_su (K := K) (p := 2) (f := 3) card_K (d := 3) le_rfl
    (by decide)
  have h2 := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (kerEquiv ht).symm h
  exact ⟨Group.isPerfect_def.1 h2.1, h2.2.1⟩

include ht in
theorem center_ker_cube (z : ↥(rho ht).ker) (hz : z ∈ Subgroup.center ↥(rho ht).ker) :
    z ^ 3 = 1 := by
  let eSt : CFSG.ClassicalInvolution.Phan.Su K 2 3 3 ≃* StatedSU 3 (2 ^ 3) K :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := 3) card_K 3)
  let e := (kerEquiv ht).trans eSt
  have hZ : e z ∈ Subgroup.center (StatedSU 3 (2 ^ 3) K) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, hz v]
  have hcen := (isQuasisimple_statedSU_of_card (p := 2) (f := 3) card_K (n := 3) le_rfl
    (by decide)).2
  rw [hcen] at hZ
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hZ
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU (e z).2
  have hc3 : c ^ 3 = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
        Kˣ) = c ^ Fintype.card (Fin 3) := Matrix.GeneralLinearGroup.det_scalar _
    apply Units.ext
    have h2 := congrArg (fun u : Kˣ => (u : K))
      (show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 from by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Units.val_one]
        exact hdet)
    simp only [h1, Fintype.card_fin, Units.val_one] at h2
    simpa using h2
  have hz3 : e (z ^ 3) = 1 := by
    rw [map_pow]
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one]
    rfl
  exact e.injective (by rw [hz3, map_one])

end Rho2

section Order

@[expose] def sStd (t : μ3) : SU4 :=
  torusSU4 fun i => if i = 0 then t else if i = 1 then t⁻¹ else 1

theorem sStd_pow_three (t : μ3) : sStd t ^ 3 = 1 := pow_three_Dstd _ ⟨_, rfl⟩

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)

theorem ent_torus_castSucc (a : Fin 3 → μ3) (i : Fin 3) :
    ent (torusSU4 a) i.castSucc i.castSucc = (((a i : μ3) : Kˣ) : K) := by
  simp only [ent, coe_torusSU4, diagonal_apply_eq]
  rw [torusSnoc_castSucc]

theorem ent_torus_last (a : Fin 3 → μ3) :
    ent (torusSU4 a) 3 3 = ((((∏ i, ((a i : μ3) : Kˣ))⁻¹ : Kˣ)) : K) := by
  simp only [ent, coe_torusSU4, diagonal_apply_eq]
  exact congrArg (fun u : Kˣ => (u : K)) (torusSnoc_last 3 _)

theorem sStd_ne_one {t : μ3} (ht : (t : Kˣ) ≠ 1) : sStd t ≠ 1 := by
  intro h
  have h0 := congrArg (fun z : SU4 => ent z (Fin.castSucc 0) (Fin.castSucc 0)) h
  simp only [sStd, ent_torus_castSucc] at h0
  apply ht
  apply Units.ext
  simpa [ent] using h0

theorem orderOf_sStd {t : μ3} (ht : (t : Kˣ) ≠ 1) : orderOf (sStd t) = 3 :=
  orderOf_eq_prime (sStd_pow_three t) (sStd_ne_one ht)

theorem sStd_mem_Jblk (t : μ3) : sStd t ∈ Jblk := by
  rw [mem_Jblk_iff]
  funext a
  rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one]
  show ent (sStd t) a 3 = (Pi.single 3 1 : Fin 4 → K) a
  have hlast : ent (sStd t) 3 3 = 1 := by
    rw [sStd, ent_torus_last]
    have : ∏ i : Fin 3, ((((fun i : Fin 3 => if i = 0 then t else if i = 1 then t⁻¹ else 1) i :
        μ3) : Kˣ)) = 1 := by
      simp [Fin.prod_univ_three]
    rw [this]; simp
  by_cases ha : a = 3
  · subst ha; simp [hlast]
  · have : ent (sStd t) a 3 = 0 := by
      simp only [sStd, ent, coe_torusSU4, diagonal_apply_ne _ ha]
    simp [Pi.single_apply, ha, this]

end Order

section Data

include ht in
theorem exists_order_three_ker : ∃ s : ↥(rho ht).ker, orderOf s = 3 := by
  have hs : sStd t ∈ (rho ht).ker.map (Cstd t).subtype := by
    rw [map_ker_rho ht]; exact sStd_mem_Jblk t
  obtain ⟨s, hs1, hs2⟩ := hs
  refine ⟨⟨s, hs1⟩, ?_⟩
  have h1 : orderOf (⟨s, hs1⟩ : ↥(rho ht).ker) = orderOf s :=
    (Subgroup.orderOf_coe (⟨s, hs1⟩ : ↥(rho ht).ker)).symm
  have h2 : orderOf s = orderOf ((s : ↥(Cstd t)) : SU4) := (Subgroup.orderOf_coe s).symm
  have h3 : ((s : ↥(Cstd t)) : SU4) = sStd t := hs2
  rw [h1, h2, h3]
  exact orderOf_sStd ht

include ht in
theorem pPrimeCore_Cstd : GLAPPrimeCore 3 ↥(Cstd t) = ⊥ :=
  pPrimeCore_eq_bot_of_ker (rho ht) (rho_pow_nine ht) (isQuasisimple_ker ht)
    (center_ker_cube ht) (exists_order_three_ker ht)

include ht in
theorem perfect_le_ker (T : Subgroup ↥(Cstd t)) (hT : ⁅T, T⁆ = T) : T ≤ (rho ht).ker :=
  le_ker_of_perfect (rho ht) T hT

end Data

end Rho

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
