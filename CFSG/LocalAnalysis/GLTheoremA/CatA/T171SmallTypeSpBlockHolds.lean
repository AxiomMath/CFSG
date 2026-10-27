module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpBlockDim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.LieType.BorelTits.HeldFlagSp
public import CFSG.Walter.Bender1970.S2.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL
  (comSp fixSp ds ds_apply mem_comSp mem_fixSp e_mem_comSp eq_zero_of_mem_comSp_fixed
    isCompl_fixSp_comSp finrank_fixSp)
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped commutatorElement

variable {n : ℕ}

private theorem fixSp_eq_orthogonal_comSp
    (hB : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).IsAlt)
    (hBn : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).Nondegenerate)
    {y : SpV n ≃ₗ[ZMod 2] SpV n}
    (hy : y ∈ linIsometryGroup (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)))
    (hy3 : y ^ 3 = 1) :
    fixSp y = (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).orthogonal (comSp y) := by
  have hle : fixSp y ≤ (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).orthogonal (comSp y) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨u, rfl⟩ := mem_comSp.mp hw
    change (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)) (y u - u) v = 0
    rw [map_sub]
    change (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)) (y u) v -
      (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)) u v = 0
    have hvv : y v = v := mem_fixSp.mp hv
    nth_rewrite 1 [← hvv]
    rw [mem_linIsometryGroup.mp hy u v, sub_self]
  have hdimfix : Module.finrank (ZMod 2) (fixSp y) =
      Module.finrank (ZMod 2) (SpV n) - Module.finrank (ZMod 2) (comSp y) := by
    have := finrank_fixSp hy3
    omega
  have hdimorth : Module.finrank (ZMod 2)
      ((CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).orthogonal (comSp y)) =
      Module.finrank (ZMod 2) (SpV n) - Module.finrank (ZMod 2) (comSp y) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBn]
  exact Submodule.eq_of_le_of_finrank_eq hle (hdimfix.trans hdimorth.symm)

private theorem restrict_comSp_nondegenerate
    (hB : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).IsAlt)
    (hBn : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).Nondegenerate)
    {y : SpV n ≃ₗ[ZMod 2] SpV n}
    (hy : y ∈ linIsometryGroup (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)))
    (hy3 : y ^ 3 = 1) :
    ((CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).restrict (comSp y)).Nondegenerate := by
  have hfix := fixSp_eq_orthogonal_comSp hB hBn hy hy3
  have hcompl : IsCompl (comSp y)
      ((CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).orthogonal (comSp y)) := by
    rw [← hfix]
    exact (isCompl_fixSp_comSp hy3).symm
  exact (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl).mpr
    hcompl

private theorem finrank_comSp_eq_two
    (hB : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).IsAlt)
    (hBn : (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)).Nondegenerate)
    (A : Subgroup (SpV n ≃ₗ[ZMod 2] SpV n)) [Fintype A] [Fintype (SpNonzeroBlock A)]
    (hAe : IsElemAbelian 3 A) (D0 : SpNonzeroBlock A)
    (hD0 : Module.finrank (ZMod 2) (blockSpace A D0.1.1) = 2)
    (y : ↥A) (hyD0 : y ∉ D0.1.1)
    (hyD : ∀ D : SpNonzeroBlock A, D ≠ D0 → y ∈ D.1.1)
    (hy3 : (y : SpV n ≃ₗ[ZMod 2] SpV n) ^ 3 = 1)
    (hyVne : (y : SpV n ≃ₗ[ZMod 2] SpV n) ≠ 1) :
    Module.finrank (ZMod 2) (comSp (y : SpV n ≃ₗ[ZMod 2] SpV n)) = 2 := by
  classical
  have hle2 := finrank_comSp_le_two_of_coordinate A hAe D0 hD0 y hyD0 hyD
  have heven := even_finrank_comSp_of_order_three (y : SpV n ≃ₗ[ZMod 2] SpV n) hy3
  have hpos : 0 < Module.finrank (ZMod 2) (comSp (y : SpV n ≃ₗ[ZMod 2] SpV n)) := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    have hbot : comSp (y : SpV n ≃ₗ[ZMod 2] SpV n) = ⊥ :=
      (Submodule.finrank_eq_zero).mp hzero
    have hds : ds (y : SpV n ≃ₗ[ZMod 2] SpV n) = 0 := by
      rw [comSp] at hbot
      exact LinearMap.range_eq_bot.mp hbot
    have hyone : (y : SpV n ≃ₗ[ZMod 2] SpV n) = 1 := by
      apply LinearEquiv.ext
      intro v
      have h := congrArg (fun f : SpV n →ₗ[ZMod 2] SpV n => f v) hds
      simp [ds] at h
      exact sub_eq_zero.mp h
    exact hyVne hyone
  rcases heven with ⟨k, hk⟩
  omega


private theorem statedSpEquiv_coe (A : StatedSp n (ZMod 2)) :
    ((CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n (ZMod 2) A :
      ↥(linIsometryGroup (CFSG.LargeExtraspecial.DW.spB n (ZMod 2)))) :
      SpV n ≃ₗ[ZMod 2] SpV n) = linHom n A := by
  apply LinearEquiv.ext
  intro v
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply,
    linHom_apply]


theorem spOneBlock_holds : SpOneBlock := by
  intro n hn4 hn5 Bb h
  classical
  let B : LinearMap.BilinForm (ZMod 2) (SpV n) := CFSG.LargeExtraspecial.DW.spB n (ZMod 2)
  let H : Subgroup (SpV n ≃ₗ[ZMod 2] SpV n) := linIsometryGroup B
  let A : Subgroup (SpV n ≃ₗ[ZMod 2] SpV n) := Bb.map (linHom n)
  have hB : B.IsAlt := fun x => CFSG.LargeExtraspecial.DW.spB_self x
  have hBn : B.Nondegenerate := CFSG.LocalAnalysis.GLTheoremA.CatB.spB_nondegenerate n
  haveI : Finite (SpV n ≃ₗ[ZMod 2] SpV n) := CFSG.LargeExtraspecial.O62.finite_linearEquiv
  haveI : Fintype A := Fintype.ofFinite _
  haveI : Fintype (SpNonzeroBlock A) := Fintype.ofFinite _
  have hAe : IsElemAbelian 3 A := h.elem.map (linHom n)
  obtain ⟨D0, hD0, hcardblocks⟩ := exists_plane_block_of_smallModel hn4 hn5 Bb h
  obtain ⟨T, hT2, hTne, hTnorm⟩ := h.twoLocal
  have hle : Nat.card Bb ≤ 3 ^ (n - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.rankFine_statedSp_two n Bb T h.elem hT2 hTne hTnorm
  obtain ⟨E, hEelem, hEcard, hEtwo⟩ := exists_twoLocal_elementaryAbelian n (n - 1) (by omega)
  have hmax := h.max E hEelem hEtwo
  rw [hEcard] at hmax
  have hcardBb : Nat.card Bb = 3 ^ (n - 1) := le_antisymm hle hmax
  have hcardA : Nat.card A = 3 ^ (n - 1) := by
    change Nat.card (Bb.map (linHom n)) = 3 ^ (n - 1)
    rw [Subgroup.card_map_of_injective (linHom_injective n), hcardBb]
  obtain ⟨yA, hyD0, hyD, hy3⟩ := exists_coordinate_element A hAe hcardA D0 hcardblocks
  have hyAne : (yA : SpV n ≃ₗ[ZMod 2] SpV n) ≠ 1 := by
    intro h1
    apply hyD0
    have hy1 : yA = 1 := Subtype.ext h1
    rw [hy1]
    exact D0.1.1.one_mem
  have hyA3 : (yA : SpV n ≃ₗ[ZMod 2] SpV n) ^ 3 = 1 := hy3
  have hplane2 : Module.finrank (ZMod 2) (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) = 2 :=
    finrank_comSp_eq_two hB hBn A hAe D0 hD0 yA hyD0 hyD hyA3 hyAne
  have hyAH : (yA : SpV n ≃ₗ[ZMod 2] SpV n) ∈ H :=
    mem_linIsometryGroup_map Bb yA.2
  have hfix : fixSp (yA : SpV n ≃ₗ[ZMod 2] SpV n) =
      B.orthogonal (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) :=
    fixSp_eq_orthogonal_comSp hB hBn hyAH hyA3
  have hPnd : (B.restrict (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n))).Nondegenerate :=
    restrict_comSp_nondegenerate hB hBn hyAH hyA3
  have hAeH : IsElemAbelian 3 (A.subgroupOf H) := hAe.subgroupOf H
  let yH : ↥H := ⟨(yA : SpV n ≃ₗ[ZMod 2] SpV n), hyAH⟩
  have hyHA : yH ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr yA.2
  have hyH3 : yH ^ 3 = 1 := Subtype.ext (by simpa using hyA3)
  have hyHne : yH ≠ 1 := by
    intro h1
    apply hyAne
    exact congrArg (fun z : ↥H => (z : SpV n ≃ₗ[ZMod 2] SpV n)) h1
  have hK6 : 6 ≤ Module.finrank (ZMod 2) (B.orthogonal
      (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n))) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBn]
    rw [CFSG.LocalAnalysis.GLTheoremA.CatB.finrank_sp, hplane2]
    omega
  have hV2 : Module.finrank (ZMod 2) (SpV n) = 2 * n :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.finrank_sp n
  have hstdH : StdAt (A.subgroupOf H) yH :=
    stdAt_of_oneBlock hB hBn n (A.subgroupOf H) hAeH yH hyHA hyH3
      (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) hPnd rfl hfix hplane2 hK6 hV2
  have hlayerIso : Nonempty
      (↥(pointwiseStab H (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n))) ≃*
        StatedSp (n - 1) (ZMod 2)) :=
    nonempty_mulEquiv_pointwiseStab_statedSp hB hBn n
      (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) hPnd hV2 hplane2
  have hlayerEq : GLALayer (Subgroup.centralizer ({yH} : Set ↥H)) =
      pointwiseStab H (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) :=
    (layer_centralizer_eq_pointwiseStab hB hBn yH hyH3
      (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)) hPnd rfl hfix hplane2 hK6).1
  let e : StatedSp n (ZMod 2) ≃* ↥H :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n (ZMod 2)
  have e_coe : ∀ b : StatedSp n (ZMod 2),
      ((e b : ↥H) : SpV n ≃ₗ[ZMod 2] SpV n) = linHom n b :=
    fun b => statedSpEquiv_coe b
  have hmapA : Bb.map e.toMonoidHom = A.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        change ((e b : ↥H) : SpV n ≃ₗ[ZMod 2] SpV n) ∈ A
        rw [e_coe b]
        exact Subgroup.mem_map_of_mem (linHom n) hb)
    · intro hx
      obtain ⟨b, hb, hbmap⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨b, hb, ?_⟩
      apply Subtype.ext
      change ((e b : ↥H) : SpV n ≃ₗ[ZMod 2] SpV n) = (x : SpV n ≃ₗ[ZMod 2] SpV n)
      rw [e_coe b]
      exact hbmap
  obtain ⟨y0, hy0Bb, hy0map⟩ := Subgroup.mem_map.mp yA.2
  have hy0e : e y0 = yH := by
    apply Subtype.ext
    rw [e_coe y0]
    exact hy0map
  have hy0ne : y0 ≠ 1 := by
    intro h1
    apply hyHne
    rw [← hy0e, h1, map_one]
  have hstdMap : StdAt (Bb.map e.toMonoidHom) (e y0) := by
    rw [hmapA, hy0e]
    exact hstdH
  refine ⟨y0, hy0Bb, hy0ne, (stdAt_map_iff e Bb y0).1 hstdMap, ?_⟩
  have hlayer0 : GLALayer (Subgroup.centralizer ({y0} : Set (StatedSp n (ZMod 2)))) =
      (pointwiseStab H (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n))).map e.symm.toMonoidHom := by
    have hy0' : e.symm yH = y0 := by rw [← hy0e, MulEquiv.symm_apply_apply]
    have h := glaLayer_centralizer_mulEquiv e.symm yH
    rw [hy0', hlayerEq] at h
    exact h
  rw [hlayer0]
  obtain ⟨eD⟩ := hlayerIso
  exact ⟨(Subgroup.equivMapOfInjective
    (pointwiseStab H (comSp (yA : SpV n ≃ₗ[ZMod 2] SpV n)))
    e.symm.toMonoidHom e.symm.injective).symm.trans eD⟩

theorem famSp_holds : FamSp := famSp_of_spOneBlock spOneBlock_holds

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
