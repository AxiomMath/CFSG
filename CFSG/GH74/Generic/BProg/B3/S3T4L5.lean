module

public import CFSG.GH74.Generic.BProg.B3.S3T4L5A
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphLin
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspace
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.GH74.Generic.BProg.B2.PuL4GraphLin

namespace S3T4

theorem mem_of_puL5 {N : Type} [Group N] [Finite N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (hP : B2.PuL5 ↥H)
    (h4 : SectionalTwoRankLE N 4) {t : N} (ht : t * t = 1) : t ∈ H := by
  by_contra htH
  have hβ2 : (MulAut.conjNormal t : MulAut ↥H) * MulAut.conjNormal t = 1 := by
    rw [← map_mul, ht, map_one]
  have hβi : (MulAut.conjNormal t : MulAut ↥H) ∉ (MulAut.conj : ↥H →* MulAut ↥H).range :=
    fun hmem => htH (B2.T4.T4OutCore.mem_of_conjNormal_mem_inner hfaith hmem)
  obtain ⟨V, hVfix, hVea, hVcard⟩ := B2.GenLocL5Out.out16_of_puL5 hP _ hβ2 hβi
  set E : Subgroup N := V.map H.subtype with hEdef
  have hEcard : Nat.card ↥E = 16 := by
    rw [hEdef, Subgroup.card_map_of_injective H.subtype_injective, hVcard]
  have hEea : CFSG.IsElementaryAbelian 2 ↥E := CFSG.IsElementaryAbelian.map _
  have hcomm : ∀ x ∈ E, t * x = x * t := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : t * (y : N) * t⁻¹ = y := by
      have := congrArg Subtype.val (hVfix y hy)
      rwa [MulAut.conjNormal_apply] at this
    calc t * (H.subtype y) = t * (y : N) * t⁻¹ * t := by simp
      _ = H.subtype y * t := by rw [h1]; rfl
  set W : Subgroup N := B2.GenLocL5Gen.adjoinInvolution E t ht hcomm with hWdef
  have hWea : CFSG.IsElementaryAbelian 2 ↥W := B2.GenLocL5Gen.isEA_adjoin hEea
  have hEW : E < W := by
    refine lt_of_le_of_ne (fun x hx => B2.GenLocL5Gen.mem_adjoin_of_mem hx) fun hEq => ?_
    have htE : t ∈ E := by rw [hEq]; exact B2.GenLocL5Gen.u_mem_adjoin
    obtain ⟨y, -, hyt⟩ := htE
    exact htH (hyt ▸ y.2)
  have hcardW : 32 ≤ Nat.card ↥W := by
    have h1 := Subgroup.card_lt_of_lt hEW
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEW.le
    rw [hEcard] at h1 hk
    omega
  have hbound := h4.card_le_of_elementary W
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 W).1 hWea)
  omega

open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.UnbalancedCatalog in
theorem exists_summand_of_inner {N : Type} [Group N] [Finite N] {H L : Subgroup N} [H.Normal]
    {t : N} (hs : B2.ShapeInCent H t L) (ht : t ∈ H) {F : Type} [Field F] [Finite F]
    (hF2 : (2 : F) ≠ 0) (e : ↥H ≃* projectiveSL 5 F) :
    ∃ (B : GL (Fin 5) F) (c : Fˣ), rhoOf e t = conjAut 5 F B ∧
      B ^ 2 = GeneralLinearGroup.scalar (Fin 5) (c ^ 2) ∧
      2 ≤ Module.finrank F ((splitMatrixOperator B).eigenspace c.val) ∧
      ((⁅(L.map (rhoOf e)).comap (conjAut 5 F), (L.map (rhoOf e)).comap (conjAut 5 F)⁆ :
        Subgroup (GL (Fin 5) F)) : Set (GL (Fin 5) F)) =
        summandSpecialLinear ((splitMatrixOperator B).eigenspace c.val)
          ((splitMatrixOperator B).eigenspace (-c.val)) := by
  classical
  obtain ⟨g, hg⟩ := LinearFlag.proj_surjective 5 F (e ⟨t, ht⟩)
  set B : GL (Fin 5) F := SpecialLinearGroup.toGL g with hBdef
  have hρ : rhoOf e t = conjAut 5 F B := by
    rw [hBdef, LinearFlag.conjAut_toGL, hg]
    exact rhoOf_mem e ⟨t, ht⟩
  have hX := isComponentOf_map_rho hs e
  rw [hρ] at hX
  obtain ⟨hXh, -, -⟩ := inner_component_lift (by norm_num : 3 ≤ 5) B hX
  set Xh := ⁅(L.map (rhoOf e)).comap (conjAut 5 F), (L.map (rhoOf e)).comap (conjAut 5 F)⁆
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  have h2 : conjAut 5 F (B ^ 2) = 1 := by rw [map_pow, ← hρ, ← map_pow, ht2, map_one]
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h2
  have hB1 : GeneralLinearGroup.det B = 1 := Units.ext (by
    rw [GeneralLinearGroup.val_det_apply, hBdef, SpecialLinearGroup.coe_GL_coe_matrix, g.2,
      Units.val_one])
  have hμ5 : μ ^ 5 = 1 := by
    have := congrArg GeneralLinearGroup.det hμ
    rwa [GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, hB1, one_pow] at this
  have hsq0 : B ^ 2 = GeneralLinearGroup.scalar (Fin 5) ((μ ^ 3) ^ 2) := by
    rw [← hμ, ← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_succ, hμ5, one_mul]
  have hL' : CFSG.IsComponent (Xh.subgroupOf (centralizer {B})) :=
    (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  obtain ⟨c, hsq, hfix⟩ : ∃ c : Fˣ, B ^ 2 = GeneralLinearGroup.scalar (Fin 5) (c ^ 2) ∧
      ∀ x ∈ Xh.subgroupOf (centralizer {B}), ∀ w ∈ (splitMatrixOperator B).eigenspace (-c.val),
        ((x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ w = w := by
    rcases fix_or_fix_of_isComponent hF2 hsq0 hL' with h | h
    · exact ⟨μ ^ 3, hsq0, h⟩
    · refine ⟨-(μ ^ 3), by rw [neg_sq]; exact hsq0, fun x hx w hw => h x hx w ?_⟩
      simpa only [Units.val_neg, neg_neg] using hw
  have hcompl := squareScalar_eigenspaces_isCompl (splitMatrixOperator B) c.val c.ne_zero hF2
    (splitMatrixOperator_square B c hsq)
  have hA : (splitMatrixOperator B).eigenspace c.val ≠ ⊥ := by
    intro hA
    have htop : (splitMatrixOperator B).eigenspace (-c.val) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hA, bot_sup_eq] at this
    have : Nontrivial (Xh.subgroupOf (centralizer {B})) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Xh.subgroupOf (centralizer {B}))
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    refine matrix_eq_of_mulVec_eq fun v => ?_
    rw [hfix x hx v (htop ▸ Submodule.mem_top)]
    simp
  have hmap := map_subtype_eq_summandSpecialLinear hF2 hsq hL' hfix hA
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hXh.1] at hmap
  exact ⟨B, c, hρ, hsq, (splitFst_map_eq hF2 hsq hL' hfix hA).2, hmap⟩

open CFSG.ComponentClassification.UnbalancedCatalog in
theorem false_of_inner_pair_lin {N : Type} [Group N] [Finite N] {H L : Subgroup N} [H.Normal]
    {v w : N} (hsv : B2.ShapeInCent H v L) (hsw : B2.ShapeInCent H w L)
    (hsvw : B2.ShapeInCent H (v * w) L) (hv : v ∈ H) (hw : w ∈ H) {F : Type} [Field F]
    [Finite F] (hF2 : (2 : F) ≠ 0) (e : ↥H ≃* projectiveSL 5 F) : False := by
  obtain ⟨Bv, cv, hρv, hsqv, hAv, hXv⟩ := exists_summand_of_inner hsv hv hF2 e
  obtain ⟨Bw, cw, hρw, hsqw, hAw, hXw⟩ := exists_summand_of_inner hsw hw hF2 e
  have hBB := S3T4.mul_eq_scalar_of_summandSL_eq hF2 hsqv hsqw hAv hAw (hXv.symm.trans hXw)
  have h1 : rhoOf e (v * w) = 1 := by
    rw [map_mul, hρv, hρw, ← map_mul, hBB, LinearFlag.conjAut_scalar]
  have h2 : v * w = 1 := rhoOf_injective hsv.faithful e (h1.trans (map_one _).symm)
  have h3 := hsvw.inv
  rw [h2, orderOf_one] at h3
  omega

end S3T4

end CFSG.GH74.Generic.BProg.B3
