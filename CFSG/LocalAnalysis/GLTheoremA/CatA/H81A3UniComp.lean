module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinComp
public import CFSG.ClassicalInvolution.Balance.StrongPowSuDiag
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.GroupTheory.PLayer.CentralQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.UniA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Elements

variable {d : Fin 4 → K} {hn : ∀ i, h.bar (d i) * d i = 1} {hd : ∏ i, d i = 1}

theorem diagU_pow_eq_one {p : ℕ} (hdp : ∀ i, d i ^ p = 1) : diagU h d hn hd ^ p = 1 := by
  apply toSLU_injective h
  rw [map_pow, toSLU_diagU, map_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL, diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, one_apply_eq, Pi.pow_apply, hdp]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

theorem diagU_mem_blockU {I : Finset (Fin 4)} (hdI : ∀ i, i ∉ I → d i = 1) :
    diagU h d hn hd ∈ blockU h I := by
  rw [mem_blockU_iff]
  intro i j hij
  rw [coe_diagU]
  by_cases hij' : i = j
  · subst hij'
    rw [diagonal_apply_eq, if_pos rfl]
    exact hdI i (by tauto)
  · rw [diagonal_apply_ne _ hij', if_neg hij']

variable (h) in
@[expose] noncomputable def swapU {i j : Fin 4} (hij : i ≠ j) : ↥(SG h) :=
  ⟨(unitSignedSwapMatrix_mem h hij).choose, (unitSignedSwapMatrix_mem h hij).choose_spec.2⟩

theorem coe_swapU {i j : Fin 4} (hij : i ≠ j) :
    (((swapU h hij : ↥(SG h)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      unitSignedSwapMatrix i j :=
  (unitSignedSwapMatrix_mem h hij).choose_spec.1

theorem swapU_apply {i j : Fin 4} (hij : i ≠ j) (a b : Fin 4) :
    (((swapU h hij : ↥(SG h)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := by
  rw [coe_swapU, CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.unitSignedSwapMatrix_apply'']

theorem swapU_mem_blockU {I : Finset (Fin 4)} {i j : Fin 4} (hij : i ≠ j) (hi : i ∈ I)
    (hj : j ∈ I) : swapU h hij ∈ blockU h I := by
  rw [mem_blockU_iff]
  intro r s hrs
  rw [swapU_apply]
  by_cases hr : r = i ∨ r = j
  · have hrI : r ∈ I := by rcases hr with rfl | rfl <;> assumption
    have hsI : s ∉ I := by
      rcases hrs with hr' | hs'
      · exact absurd hrI hr'
      · exact hs'
    have hsw : Equiv.swap i j r ∈ I := by
      rcases hr with rfl | rfl
      · simpa using hj
      · simpa using hi
    have hne : Equiv.swap i j r ≠ s := fun he => hsI (he ▸ hsw)
    have hrs' : r ≠ s := fun he => hsI (he ▸ hrI)
    simp [hne, hrs']
  · push Not at hr
    rw [Equiv.swap_apply_of_ne_of_ne hr.1 hr.2]
    simp [hr.1]

theorem diagU_mul_swapU_ne {a b : Fin 4} (hab : a ≠ b) (hdab : d a ≠ d b) :
    diagU h d hn hd * swapU h hab ≠ swapU h hab * diagU h d hn hd := by
  intro he
  have h1 := congrArg (fun x : ↥(SG h) => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) a b) he
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagU, diagonal_mul, mul_diagonal,
    swapU_apply, Equiv.swap_apply_left, if_pos rfl, ↓reduceIte] at h1
  apply hdab
  linear_combination -h1

theorem projU_diagU_mul_swapU_ne {a b : Fin 4} (hab : a ≠ b) (hdab : d a ≠ d b) :
    projU h (diagU h d hn hd) * projU h (swapU h hab) ≠
      projU h (swapU h hab) * projU h (diagU h d hn hd) := by
  intro he
  rw [← map_mul, ← map_mul] at he
  set x := diagU h d hn hd with hx
  set w := swapU h hab with hw
  have hmem : (w * x)⁻¹ * (x * w) ∈ (projU h).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [ker_projU] at hmem
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hmem
  have heq : x * w = (w * x) * ((w * x)⁻¹ * (x * w)) := by group
  have hent : ∀ k l, ((x * w : ↥(SG h)) : GL (Fin 4) K).val k l =
      ((w * x : ↥(SG h)) : GL (Fin 4) K).val k l * (c : K) := by
    intro k l
    conv_lhs => rw [heq]
    rw [Subgroup.coe_mul, Units.val_mul, hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      mul_diagonal]
  have key : ∀ a b : Fin 4, ∃ r : Fin 4, r ≠ a ∧ r ≠ b := by decide
  obtain ⟨r, hra, hrb⟩ := key a b
  have hdr : d r ≠ 0 := by
    intro h0
    have : ∏ i, d i = 0 := Finset.prod_eq_zero (Finset.mem_univ r) h0
    rw [hd] at this
    exact one_ne_zero this
  have h1 := hent r r
  have h2 := hent a b
  simp only [Subgroup.coe_mul, Units.val_mul, hx, hw, coe_diagU, diagonal_mul, mul_diagonal,
    swapU_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hra hrb, if_pos rfl,
    if_neg hra, ↓reduceIte] at h1 h2
  have hc1 : (c : K) = 1 := by
    have h3 : d r * (c : K) = d r * 1 := by linear_combination -h1
    exact mul_left_cancel₀ hdr h3
  rw [hc1] at h2
  apply hdab
  linear_combination -h2

end Elements

theorem centralizer_projU_diagU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : Fin 4 → K}
    {hn : ∀ i, h.bar (d i) * d i = 1} {hd : ∏ i, d i = 1} (hdp : ∀ i, d i ^ p = 1) :
    Subgroup.centralizer ({projU h (diagU h d hn hd)} : Set (PS h)) =
      (Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h))).map (projU h) :=
  CFSG.StandardType.TableBUE.centralizer_map_eq_of_noTorsion (projU h)
    (QuotientGroup.mk'_surjective _) ker_projU_le_center (projU_noTorsion hp hp2)
    (diagU_pow_eq_one hdp)

theorem eq_one_of_mem_blockU_of_projU_eq_one {g : ↥(SG h)} (hg : g ∈ blockU h blockJ)
    (h1 : projU h g = 1) : g = 1 := by
  have hk : g ∈ (projU h).ker := h1
  rw [ker_projU] at hk
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hk
  have h00 := corner_of_mem_coordBlockSL hg
  rw [coe_toSLU, hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h00
  apply Subtype.ext
  rw [hc, show c = 1 from Units.ext h00, map_one]
  rfl

noncomputable def mapProjUEquiv (L : Subgroup ↥(SG h)) (hL : L ≤ blockU h blockJ) :
    ↥L ≃* ↥(L.map (projU h)) :=
  MulEquiv.ofBijective ((projU h).subgroupMap L)
    ⟨fun a b hab => by
      have h1 : projU h ((a : ↥(SG h))⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hab
      have h2 := eq_one_of_mem_blockU_of_projU_eq_one (hL (mul_mem (inv_mem a.2) b.2)) h1
      exact Subtype.ext (inv_mul_eq_one.1 h2),
     (projU h).subgroupMap_surjective L⟩

theorem blockU_mono {I J : Finset (Fin 4)} (hIJ : I ⊆ J) : blockU h I ≤ blockU h J :=
  fun _ hg => coordBlockSL_mono hIJ hg

variable (h) in
noncomputable abbrev JU : Subgroup (PS h) := (blockU h blockJ).map (projU h)

theorem conj_mem_blockU_of_mem_centralizer {d : Fin 4 → K} {hn : ∀ i, h.bar (d i) * d i = 1}
    {hd : ∏ i, d i = 1} {I : Finset (Fin 4)} (hdist : ∀ i j, (i ∈ I ↔ j ∉ I) → d i ≠ d j)
    {m g : ↥(SG h)} (hm : m ∈ Subgroup.centralizer ({diagU h d hn hd} : Set ↥(SG h)))
    (hg : g ∈ blockU h I) : m * g * m⁻¹ ∈ blockU h I := by
  change toSLU h (m * g * m⁻¹) ∈ coordBlockSL K I
  rw [map_mul, map_mul, map_inv]
  refine conj_mem_coordBlockSL ?_ hg
  have hm' := toSLU_mem_cent hm
  rw [mem_centralizer_diagSL_iff] at hm'
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
  · simp [hi, hj]
  · rw [if_pos hi, if_neg hj, hm' i j (hdist i j ⟨fun _ => hj, fun _ => hi⟩)]
  · rw [if_neg hi, if_pos hj, hm' i j (hdist i j ⟨fun h' => absurd h' hi, fun h' => absurd hj h'⟩)]
  · simp [hi, hj]

section Root

variable {p : ℕ} {μ : K} (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
  (hpq : p ∣ ℓ ^ f + 1)

include hpq in
theorem norm_of_pow {d : Fin 4 → K} (hdp : ∀ i, d i ^ p = 1) : ∀ i, h.bar (d i) * d i = 1 :=
  fun i => bar_mul_self_of_pow_eq_one hpq (hdp i)

variable (h) in
noncomputable abbrev yU : ↥(SG h) :=
  diagU h (yd μ) (norm_of_pow hpq (yd_pow hp hp2 hμ)) (prod_yd (ne_zero_of_root hp hp2 hμ))

variable (h) in
noncomputable abbrev zU : ↥(SG h) :=
  diagU h (zd μ) (norm_of_pow hpq (zd_pow hp hp2 hμ)) (prod_zd (ne_zero_of_root hp hp2 hμ))

include hp hp2 hμ hpq

theorem yd_const_blockJ : ∀ i ∈ blockJ, ∀ j ∈ blockJ, yd μ i = yd μ j :=
  fun i hi j hj => yd_const hp hp2 hμ i j (mem_blockJ.1 hi) (mem_blockJ.1 hj)

omit hp hp2 hμ hpq in
theorem zd_const_blockI : ∀ i ∈ blockI, ∀ j ∈ blockI, zd μ i = zd μ j := by
  intro i hi j hj
  fin_cases i <;> fin_cases j <;> simp_all [blockI, zd]

omit hp hp2 hμ hpq in
theorem t2d_eq_one_of_not_mem_blockI : ∀ i, i ∉ blockI → t2d μ i = 1 := by
  intro i hi
  fin_cases i <;> simp_all [blockI, t2d]

omit hpq in
theorem zd_ne_of_mem_blockI_iff : ∀ i j, (i ∈ blockI ↔ j ∉ blockI) → zd μ i ≠ zd μ j := by
  have h1 := inv_ne_one hp hp2 hμ
  have h2 := ne_one_of_root hp hp2 hμ
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [zd, blockI, eq_comm]

theorem centralizer_projU_yU :
    Subgroup.centralizer ({projU h (yU h hp hp2 hμ hpq)} : Set (PS h)) =
      (Subgroup.centralizer ({yU h hp hp2 hμ hpq} : Set ↥(SG h))).map (projU h) :=
  centralizer_projU_diagU hp hp2 (yd_pow hp hp2 hμ)

theorem centralizer_projU_zU :
    Subgroup.centralizer ({projU h (zU h hp hp2 hμ hpq)} : Set (PS h)) =
      (Subgroup.centralizer ({zU h hp hp2 hμ hpq} : Set ↥(SG h))).map (projU h) :=
  centralizer_projU_diagU hp hp2 (zd_pow hp hp2 hμ)

theorem projU_zU_not_mem_zpowers :
    projU h (zU h hp hp2 hμ hpq) ∉ Subgroup.zpowers (projU h (yU h hp hp2 hμ hpq)) := by
  have hab : (1 : Fin 4) ≠ 2 := by decide
  have hwJ : swapU h hab ∈ blockU h blockJ := swapU_mem_blockU hab (by decide) (by decide)
  have hwy : swapU h hab * yU h hp hp2 hμ hpq = yU h hp hp2 hμ hpq * swapU h hab :=
    Subgroup.mem_centralizer_singleton_iff.1
      (blockU_le_centralizer (yd_const_blockJ hp hp2 hμ hpq) hwJ)
  have hyC : projU h (yU h hp hp2 hμ hpq) ∈
      Subgroup.centralizer ({projU h (swapU h hab)} : Set (PS h)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hwy]
  intro hmem
  have hzC := (Subgroup.zpowers_le.2 hyC) hmem
  rw [Subgroup.mem_centralizer_singleton_iff] at hzC
  exact projU_diagU_mul_swapU_ne hab (by simpa [zd] using inv_ne_one hp hp2 hμ) hzC

theorem projU_yU_ne_one : projU h (yU h hp hp2 hμ hpq) ≠ 1 := by
  intro h1
  have hk : yU h hp hp2 hμ hpq ∈ (projU h).ker := h1
  rw [ker_projU] at hk
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hk
  have hm := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
  have h0 := congrFun (congrFun hm 0) 0
  have h1' := congrFun (congrFun hm 1) 1
  simp only [coe_diagU, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_eq] at h0 h1'
  exact yd_zero_ne hp hp2 hμ 1 (by decide) (h0.trans h1'.symm)

section Finite

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
include hK hq

theorem dvd_card_blockU_blockJ :
    p ∣ Nat.card (↥(blockU h blockJ) ⧸ Subgroup.center ↥(blockU h blockJ)) := by
  have hab : (1 : Fin 4) ≠ 2 := by decide
  refine dvd_card_quotient_center_of_not_commute hp
    (x := diagU h (td μ) (norm_of_pow hpq (td_pow hp hp2 hμ)) (prod_td (ne_zero_of_root hp hp2 hμ)))
    (y := swapU h hab) (diagU_mem_blockU fun i hi => ?_)
    (swapU_mem_blockU hab (by decide) (by decide)) (diagU_pow_eq_one (td_pow hp hp2 hμ))
    (diagU_mul_swapU_ne hab (by simpa [td] using (inv_ne_self hp hp2 hμ).symm))
  rw [mem_blockJ, not_not] at hi
  subst hi
  rfl

theorem glaPComponent_cent_yU :
    GLAPComponent p (Subgroup.centralizer ({yU h hp hp2 hμ hpq} : Set ↥(SG h)))
      (blockU h blockJ) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
    (IsSubnormal.step (blockU_le_centralizer (yd_const_blockJ hp hp2 hμ hpq))
      (blockU_normal (yd_zero_ne hp hp2 hμ) (yd_const hp hp2 hμ)) (IsSubnormal.refl _))
    (isQuasisimple_blockU hK hq (by decide)) (dvd_card_blockU_blockJ hp hp2 hμ hpq hK hq)

theorem eq_of_glaPComponent_cent_yU {L : Subgroup ↥(SG h)}
    (hL : GLAPComponent p (Subgroup.centralizer ({yU h hp hp2 hμ hpq} : Set ↥(SG h))) L) :
    L = blockU h blockJ :=
  eq_of_glaPComponent_of_commutator_le (blockU_le_centralizer (yd_const_blockJ hp hp2 hμ hpq))
    (isQuasisimple_blockU hK hq (by decide))
    (commutator_centralizer_le_blockU (yd_zero_ne hp hp2 hμ)) hL

omit hp hp2 hμ hpq hK hq in
private theorem central_kerU (X : Subgroup ↥(SG h)) :
    ∀ y ∈ X ⊓ (projU h).ker, ∀ x ∈ X, x * y = y * x := fun _ hy x _ =>
  (Subgroup.mem_center_iff.1 (ker_projU_le_center hy.2) x)

theorem glaPComponent_centralizer_projU_yU :
    GLAPComponent p (Subgroup.centralizer ({projU h (yU h hp hp2 hμ hpq)} : Set (PS h)))
      (JU h) := by
  rw [centralizer_projU_yU hp hp2 hμ hpq]
  exact (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (projU h)
    (central_kerU _)).1 _ (glaPComponent_cent_yU hp hp2 hμ hpq hK hq)

theorem eq_of_glaPComponent_centralizer_projU_yU {L : Subgroup (PS h)}
    (hL : GLAPComponent p (Subgroup.centralizer ({projU h (yU h hp hp2 hμ hpq)} : Set (PS h)))
      L) : L = JU h := by
  rw [centralizer_projU_yU hp hp2 hμ hpq] at hL
  obtain ⟨L₀, hL₀, rfl⟩ := (CFSG.glaPComponent_map_bijective_of_ker_le_center hp (projU h)
    (central_kerU _)).2 L hL
  rw [eq_of_glaPComponent_cent_yU hp hp2 hμ hpq hK hq hL₀]

theorem isQuasisimple_JU : CFSG.Open.IsQuasisimple ↥(JU h) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapProjUEquiv _ le_rfl).symm (isQuasisimple_blockU hK hq (by decide))

theorem dvd_card_JU : p ∣ Nat.card (↥(JU h) ⧸ Subgroup.center ↥(JU h)) := by
  rw [← natCard_quotient_center_congr (mapProjUEquiv _ le_rfl)]
  exact dvd_card_blockU_blockJ hp hp2 hμ hpq hK hq

theorem glaPLayer_JU_inf_centralizer_ne_bot :
    GLAPLayer p (JU h ⊓ Subgroup.centralizer
      ({projU h (zU h hp hp2 hμ hpq)} : Set (PS h))) ≠ ⊥ := by
  have hIJ : blockI ⊆ blockJ := by decide
  have hK₂J : blockU h blockI ≤ blockU h blockJ := blockU_mono hIJ
  have hzI : ∀ i ∈ blockI, ∀ j ∈ blockI, zd μ i = zd μ j := zd_const_blockI
  set K₂ := (blockU h blockI).map (projU h) with hK₂def
  have hle : K₂ ≤ JU h ⊓ Subgroup.centralizer
      ({projU h (zU h hp hp2 hμ hpq)} : Set (PS h)) := by
    refine le_inf (Subgroup.map_mono hK₂J) ?_
    rw [centralizer_projU_zU hp hp2 hμ hpq]
    exact Subgroup.map_mono (blockU_le_centralizer hzI)
  have hdist : ∀ i j, (i ∈ blockI ↔ j ∉ blockI) → zd μ i ≠ zd μ j :=
    zd_ne_of_mem_blockI_iff hp hp2 hμ
  have hN : (K₂.subgroupOf (JU h ⊓ Subgroup.centralizer
      ({projU h (zU h hp hp2 hμ hpq)} : Set (PS h)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : PS h) ∈ (Subgroup.centralizer
        ({zU h hp hp2 hμ hpq} : Set ↥(SG h))).map (projU h) := by
      rw [← centralizer_projU_zU hp hp2 hμ hpq]
      exact g.2.2
    obtain ⟨m, hm, hmg⟩ := hg
    obtain ⟨k, hk, hkn⟩ := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hmg, ← hkn, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_blockU_of_mem_centralizer hdist hm hk)
  have hqs : CFSG.Open.IsQuasisimple ↥K₂ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv (mapProjUEquiv _ hK₂J).symm
      (isQuasisimple_blockU hK hq (I := blockI) (by decide))
  have hdvd : p ∣ Nat.card (↥K₂ ⧸ Subgroup.center ↥K₂) := by
    rw [← natCard_quotient_center_congr (mapProjUEquiv _ hK₂J)]
    have hab : (2 : Fin 4) ≠ 3 := by decide
    refine dvd_card_quotient_center_of_not_commute hp
      (x := diagU h (t2d μ) (norm_of_pow hpq (t2d_pow hp hp2 hμ))
        (prod_t2d (ne_zero_of_root hp hp2 hμ)))
      (y := swapU h hab) (diagU_mem_blockU t2d_eq_one_of_not_mem_blockI)
      (swapU_mem_blockU hab (by decide) (by decide)) (diagU_pow_eq_one (t2d_pow hp hp2 hμ))
      (diagU_mul_swapU_ne hab (by simpa [t2d] using (inv_ne_self hp hp2 hμ).symm))
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple hp hle hN hqs
    hdvd

end Finite

end Root

end CFSG.LocalAnalysis.GLTheoremA.H81.UniA3
