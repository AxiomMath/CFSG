module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg

@[expose] def chainNode (k : Fin 5) : Fin (Tag.rank .E6) := (![0, 2, 3, 4, 5] : Fin 5 → Fin 6) k

set_option maxRecDepth 100000 in
theorem a5Root_castSucc_succ_check :
    ∀ k : Fin 5, a5Root k.castSucc k.succ = Pi.single (chainNode k) 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a5Root_succ_castSucc_check :
    ∀ k : Fin 5, a5Root k.succ k.castSucc = -Pi.single (chainNode k) 1 := by
  decide +kernel

theorem a5Root_castSucc_succ (k : Fin 5) :
    a5Root k.castSucc k.succ = Pi.single (chainNode k) 1 :=
  a5Root_castSucc_succ_check k

theorem a5Root_succ_castSucc (k : Fin 5) :
    a5Root k.succ k.castSucc = -Pi.single (chainNode k) 1 :=
  a5Root_succ_castSucc_check k

theorem chain_exponent (v : Fin (Tag.rank .E6) → ℤ) :
    (∑ j, Tag.cartan .E6 (chainNode 0) j * v j) +
        2 * (∑ j, Tag.cartan .E6 (chainNode 1) j * v j) +
          3 * (∑ j, Tag.cartan .E6 (chainNode 2) j * v j) +
            4 * (∑ j, Tag.cartan .E6 (chainNode 3) j * v j) +
              5 * (∑ j, Tag.cartan .E6 (chainNode 4) j * v j) =
      3 * (2 * v (chainNode 4) - v (highNode .E6)) := by
  change (∑ j : Fin 6, Tag.cartan .E6 (chainNode 0) j * v j) +
        2 * (∑ j : Fin 6, Tag.cartan .E6 (chainNode 1) j * v j) +
          3 * (∑ j : Fin 6, Tag.cartan .E6 (chainNode 2) j * v j) +
            4 * (∑ j : Fin 6, Tag.cartan .E6 (chainNode 3) j * v j) +
              5 * (∑ j : Fin 6, Tag.cartan .E6 (chainNode 4) j * v j) =
      3 * (2 * v (chainNode 4) - v (highNode .E6))
  simp [Fin.sum_univ_six, Tag.cartan, Tag.cartanE, chainNode, highNode]
  ring

theorem zpow_eq_one_of_three_dvd {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) {e : ℤ}
    (he : (3 : ℤ) ∣ e) : u ^ e = 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [zpow_mul, zpow_ofNat, hu, one_zpow]

section Torus


variable {K : Type} [Field K]

theorem torusElt_smul_single (i : Fin (Tag.rank .E6)) (t : Kˣ) (b : Label .E6) (c : K) :
    (torusElt .E6 K i t : Module.End K (RootModule .E6 K)) (c • Finsupp.single b 1) =
      (c * ((t ^ (∑ j, Tag.cartan .E6 i j * Label.latticeWeight b j) : Kˣ) : K)) •
        Finsupp.single b 1 := by
  rw [map_smul, torusElt_single_eq, smul_smul]

theorem torusElt_chain_prod_eq_one {u : Kˣ} (hu : u ^ 3 = 1) :
    torusElt .E6 K (chainNode 0) u * torusElt .E6 K (chainNode 1) (u ^ 2) *
        torusElt .E6 K (chainNode 2) (u ^ 3) * torusElt .E6 K (chainNode 3) (u ^ 4) *
          torusElt .E6 K (chainNode 4) (u ^ 5) = 1 := by
  refine Units.ext (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.end_ext_single
    fun b => ?_)
  simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
  rw [torusElt_single_eq, torusElt_smul_single, torusElt_smul_single, torusElt_smul_single,
    torusElt_smul_single]
  conv_rhs => rw [← one_smul K (Finsupp.single b 1 : RootModule .E6 K)]
  congr 1
  simp only [← Units.val_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  rw [Units.val_eq_one]
  have he := chain_exponent (Label.latticeWeight b)
  refine zpow_eq_one_of_three_dvd hu ⟨2 * Label.latticeWeight b (chainNode 4) -
    Label.latticeWeight b (highNode .E6), ?_⟩
  push_cast
  linear_combination he

end Torus

section Block

variable {K : Type} [Field K]

theorem blockMat_diag (k : Fin 5) (a b : K) :
    SL.blockMat k !![a, 0; 0, b] =
      Matrix.diagonal (fun p : Fin (5 + 1) =>
        if p = k.castSucc then a else if p = k.succ then b else 1) := by
  have hne := SL.castSucc_ne_succ k
  refine SL.ext_blockEquiv k fun p q => ?_
  rw [SL.blockMat_apply]
  rcases p with p | ⟨x, hx⟩ <;> rcases q with q | ⟨y, hy⟩
  · fin_cases p <;> fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, Matrix.diagonal, hne, Ne.symm hne]
  · push Not at hy
    fin_cases p <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, Matrix.diagonal,
        Ne.symm hy.1, Ne.symm hy.2]
  · push Not at hx
    fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, Matrix.diagonal, hx.1, hx.2]
  · push Not at hx
    simp [SL.blockEquiv_inr, Matrix.diagonal, Matrix.one_apply, hx.1, hx.2,
      Matrix.fromBlocks_apply₂₂, Subtype.ext_iff]

theorem coe_blockHom_HSL (k : Fin 5) (t : Kˣ) :
    ((SL.blockHom K k (HSL t) : Matrix.SpecialLinearGroup (Fin (5 + 1)) K) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) K) =
      Matrix.diagonal (fun p : Fin (5 + 1) =>
        if p = k.castSucc then (t : K) else if p = k.succ then ((t⁻¹ : Kˣ) : K) else 1) :=
  blockMat_diag k _ _

theorem blockHom_HSL_prod_eq {u : Kˣ} (hu : u ^ 6 = 1) :
    ((SL.blockHom K (0 : Fin 5) (HSL u) * SL.blockHom K 1 (HSL (u ^ 2)) *
        SL.blockHom K 2 (HSL (u ^ 3)) * SL.blockHom K 3 (HSL (u ^ 4)) *
          SL.blockHom K 4 (HSL (u ^ 5)) : Matrix.SpecialLinearGroup (Fin (5 + 1)) K) :
        Matrix (Fin (5 + 1)) (Fin (5 + 1)) K) = Matrix.scalar (Fin (5 + 1)) (u : K) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockHom_HSL, Matrix.diagonal_mul_diagonal]
  rw [Matrix.scalar_apply]
  congr 1
  funext p
  have hu' : ((u : K)) ^ 6 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h0 : (u : K) ≠ 0 := u.ne_zero
  fin_cases p <;> simp [Fin.ext_iff] <;> field_simp
  exact hu'.symm

end Block

section Kernel


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem coe_slToAdjointE6_blockHom_HSL (k : Fin 5) (t : Kˣ) :
    ((slToAdjointE6 K (SL.blockHom K k (HSL t)) : adjointGroup .E6 K) : ModGL .E6 K) =
      torusElt .E6 K (chainNode k) t := by
  obtain ⟨ρ, hu, hv, hH, -⟩ := exceptional_ordinary_rank_one_central_image .E6 K (chainNode k)
  have hne := SL.castSucc_ne_succ k
  have hext : (adjointGroup .E6 K).subtype.comp ((slToAdjointE6 K).comp (SL.blockHom K k)) =
      ρ := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have hb : SL.blockHom K k (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c) =
          Matrix.SpecialLinearGroup.transvection hne c :=
        Subtype.ext (SL.blockMat_transvection_upper k c)
      change ((slToAdjointE6 K (SL.blockHom K k (uSL c)) : adjointGroup .E6 K) : ModGL .E6 K) =
        ρ (uSL c)
      rw [hu, show uSL c = CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c from rfl, hb,
        coe_slToAdjointE6_transvection, a5Root_castSucc_succ, pinnedX_single]
    · have hb : SL.blockHom K k (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c) =
          Matrix.SpecialLinearGroup.transvection hne.symm c :=
        Subtype.ext (SL.blockMat_transvection_lower k c)
      change ((slToAdjointE6 K (SL.blockHom K k (vSL c)) : adjointGroup .E6 K) : ModGL .E6 K) =
        ρ (vSL c)
      rw [hv, show vSL c = CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c from rfl, hb,
        coe_slToAdjointE6_transvection, a5Root_succ_castSucc, pinnedX_neg_single]
  rw [← hH t, ← hext]
  rfl

theorem center_le_ker_slToAdjointE6 :
    center (Matrix.SpecialLinearGroup (Fin 6) K) ≤ (slToAdjointE6 K).ker := by
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  set u : Kˣ := Units.mk0 r hr0 with hu
  have hu6 : u ^ 6 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr,
    Units.val_one])
  have hu3 : u ^ 3 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    refine charTwo_eq_one_of_mul_self_eq_one ?_
    rw [← pow_add, Units.val_mk0, hr]
  have hz' : z = SL.blockHom K (0 : Fin 5) (HSL u) * SL.blockHom K 1 (HSL (u ^ 2)) *
      SL.blockHom K 2 (HSL (u ^ 3)) * SL.blockHom K 3 (HSL (u ^ 4)) *
        SL.blockHom K 4 (HSL (u ^ 5)) := by
    refine Subtype.ext ?_
    rw [blockHom_HSL_prod_eq hu6, ← hrz, Units.val_mk0]
  rw [MonoidHom.mem_ker, hz']
  refine Subtype.ext ?_
  simp only [map_mul, Subgroup.coe_mul, coe_slToAdjointE6_blockHom_HSL, OneMemClass.coe_one]
  exact torusElt_chain_prod_eq_one hu3

theorem ker_slToAdjointE6 :
    (slToAdjointE6 K).ker = center (Matrix.SpecialLinearGroup (Fin 6) K) := by
  refine le_antisymm ?_ center_le_ker_slToAdjointE6
  have hne : (0 : Fin 6) ≠ 1 := by decide
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num))
    ⟨_, slToAdjointE6_transvection_ne_one hne one_ne_zero⟩

end Kernel

end CFSG.SeitzReduction.E6Pilot
