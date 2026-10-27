module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec42
public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.LinRadicalsCount
public import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary
public import CFSG.LocalAnalysis.EvenBN.U5.LinRadicalsQuot
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type*} [Group G]

@[expose] def imgSE (S E X : Subgroup G) [(E.subgroupOf S).Normal] :
    Subgroup (↥S ⧸ E.subgroupOf S) :=
  (X.subgroupOf S).map (QuotientGroup.mk' (E.subgroupOf S))

theorem lin_card_image_mul (S E X : Subgroup G) [(E.subgroupOf S).Normal] (hX : X ≤ S) :
    Nat.card (imgSE S E X) * Nat.card (E ⊓ X : Subgroup G) = Nat.card X := by
  set Y : Subgroup S := X.subgroupOf S with hY
  set φ : ↥Y →* ↥S ⧸ E.subgroupOf S := (QuotientGroup.mk' (E.subgroupOf S)).comp Y.subtype with hφ
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = imgSE S E X := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : φ.ker = (E.subgroupOf S).subgroupOf Y := by
    ext y
    simp [hφ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcardY : Nat.card Y = Nat.card X := by
    rw [hY, ← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hX]
  have hcardker : Nat.card φ.ker = Nat.card (E ⊓ X : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x.1 : ↥Y) : ↥S), ?_⟩
        invFun := fun z => ⟨⟨⟨(z : G), hX (Subgroup.mem_inf.1 z.2).2⟩,
          Subgroup.mem_inf.1 z.2 |>.2⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
    · have h2 := x.2
      rw [MonoidHom.mem_ker] at h2
      have h3 : ((x.1 : ↥Y) : ↥S) ∈ E.subgroupOf S :=
        (QuotientGroup.eq_one_iff (N := E.subgroupOf S) ((x.1 : ↥Y) : ↥S)).1 h2
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h3, x.1.2⟩
    · rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := E.subgroupOf S)
        (⟨(z : G), hX (Subgroup.mem_inf.1 z.2).2⟩ : ↥S)).2
        (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 z.2).1)
  rw [hrange, hcardker, hcardY] at h1
  rw [mul_comm]
  exact h1

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin_E_normal_S : (d.E.subgroupOf c.S).Normal := by
  obtain ⟨-, hEchar, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  haveI := hEchar
  infer_instance

theorem lin_S_le_L₁ : c.S ≤ d.L₁ := (k.s10_2 c.S c.S_syl c.P_le_S).2.2.2.2.2.2.1.le

theorem lin_E_le_S : d.E ≤ c.S := by
  obtain ⟨hSeq, -, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  exact hSeq ▸ le_sup_left

theorem lin_F_inf_E : d.F ⊓ d.E = d.W := by
  obtain ⟨hSeq, hEchar, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  obtain ⟨hVc, hW, -, -, -⟩ := k.s9_2 c.S c.S_syl c.P_le_S
  have hES := lin_E_le_S hl k c
  have hDS := lin_D_le_S hl k c
  have hEab := hl.hyp.elemAbMod_V_E hl.gms
  have hE6 := (k.s10_1 c.S c.S_syl c.P_le_S).2.2.2.2.2.1
  apply le_antisymm
  · rintro f₀ ⟨hfF, hfE⟩
    rw [← hW]
    refine ⟨⟨f₀, hES hfE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    have hyS : (y : G) ∈ d.E ⊔ d.D := hSeq ▸ y.2
    have hDE : d.D ≤ normalizer (d.E : Set G) :=
      hDS.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (lin_E_normal_S hl k c))
    obtain ⟨e, he, d', hd', hy⟩ := Common.exists_mul_of_le_normalizer hDE (y : G) hyS
    have hfd : f₀ * d' = d' * f₀ :=
      mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hd') f₀ hfF
    have hcomm : ⁅f₀, e⁆ ∈ d.V := hEab.2 f₀ hfE e he
    have hcomm' : ⁅f₀, e⁆ ∈ CFSG.centerIn c.S := by rw [hVc]; exact hcomm
    have key : f₀ * (y : G) * f₀⁻¹ * (y : G)⁻¹ = ⁅f₀, e⁆ := by
      rw [hy, commutatorElement_def]
      have h1 : d' * f₀⁻¹ = f₀⁻¹ * d' := by
        calc d' * f₀⁻¹ = f₀⁻¹ * (f₀ * d') * f₀⁻¹ := by group
          _ = f₀⁻¹ * (d' * f₀) * f₀⁻¹ := by rw [hfd]
          _ = f₀⁻¹ * d' := by group
      calc f₀ * (e * d') * f₀⁻¹ * (e * d')⁻¹ = f₀ * e * (d' * f₀⁻¹) * d'⁻¹ * e⁻¹ := by group
        _ = f₀ * e * (f₀⁻¹ * d') * d'⁻¹ * e⁻¹ := by rw [h1]
        _ = f₀ * e * f₀⁻¹ * e⁻¹ := by group
    intro g
    have := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcomm').2 (g : G) g.2
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [key]
    exact this
  · intro w hw
    refine ⟨s313a_W_le_F hl.toCaseHyp k c.S_syl c.P_le_S hw, ?_⟩
    rw [hE6]
    exact mem_sup_left (mem_sup_left hw)

theorem lin_L₁_le_normalizer_Bt : d.L₁ ≤ normalizer (c.Bt : Set G) := by
  rw [lin_Bt_eq hl k c]
  exact fun _ hg => Common.mem_normalizer_inf (lin_L₁_le_normalizer_FKt hl k c hg)
    (lin_L₁_le_normalizer_D hl k c hg)

theorem lin_card_Bc_inf_E [(d.E.subgroupOf c.S).Normal] (h41 : c.Sec41)
    (hQ : ∃ Q₁ Q₂ : Subgroup (↥c.S ⧸ d.E.subgroupOf c.S),
      LinearThree.Radicals ⊤ Q₁ Q₂ ((2 ^ f) ^ 2)) :
    Nat.card (c.Bc ⊓ d.E : Subgroup G) = (2 ^ f) ^ 8 := by
  obtain ⟨Q₁, Q₂, hR⟩ := hQ
  obtain ⟨hSeq, -, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  have hf2 := hl.hyp.two_le
  have hπs : Function.Surjective (QuotientGroup.mk' (d.E.subgroupOf c.S)) :=
    QuotientGroup.mk'_surjective _
  have hDS := lin_D_le_S hl k c
  have hES := lin_E_le_S hl k c
  have hBS : c.Bc ≤ c.S := (lin_Bc_le_D hl k c).trans hDS
  have hBtS : c.Bt ≤ c.S := (lin_Bt_le_D hl k c).trans hDS
  have hFS : d.F ≤ c.S := (lin_F_le_D hl k c).trans hDS
  obtain ⟨hBel, hBcard, hBinf, hBsup⟩ := lin_sec42_basic hl k c h41
  have hBtel : IsElemAbelian 2 c.Bt := IsElemAbelian.map hBel (MulAut.conj d.t).toMonoidHom
  have hBel' : IsElemAbelian 2 (imgSE c.S d.E c.Bc) :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf hBel c.S) _
  have hBtel' : IsElemAbelian 2 (imgSE c.S d.E c.Bt) :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf hBtel c.S) _
  have hBn : (imgSE c.S d.E c.Bc).Normal := by
    have : (c.Bc.subgroupOf c.S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).2
        ((lin_S_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bc hl k c))
    exact this.map _ hπs
  have hBtn : (imgSE c.S d.E c.Bt).Normal := by
    have : (c.Bt.subgroupOf c.S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBtS).2
        ((lin_S_le_L₁ hl k c).trans (lin_L₁_le_normalizer_Bt hl k c))
    exact this.map _ hπs
  have hDE : d.D ≤ normalizer (d.E : Set G) :=
    hDS.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (lin_E_normal_S hl k c))
  have hsup : imgSE c.S d.E c.Bc ⊔ imgSE c.S d.E c.Bt = ⊤ := by
    unfold imgSE
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hBS hBtS, hBsup, eq_top_iff]
    intro q _
    obtain ⟨s, rfl⟩ := hπs q
    have hs : (s : G) ∈ d.D ⊔ d.E := by
      rw [sup_comm, ← hSeq]
      exact s.2
    obtain ⟨d', hd', e, he, hsde⟩ := Common.exists_mul_of_le_normalizer' hDE (s : G) hs
    refine ⟨⟨d', hDS hd'⟩, Subgroup.mem_subgroupOf.2 hd', ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : ((⟨d', hDS hd'⟩ : ↥c.S)⁻¹ * s : ↥c.S) ∈ d.E.subgroupOf c.S := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hsde]
      simpa using he
    exact this
  have hcB := lin_card_image_mul c.S d.E c.Bc hBS
  have hcBt := lin_card_image_mul c.S d.E c.Bt hBtS
  have hcF := lin_card_image_mul c.S d.E d.F hFS
  have hEt : d.E.map (MulAut.conj d.t).toMonoidHom = d.E :=
    map_conj_eq_of_mem_normalizer (hl.hyp.t_mem_normalizer_E_caseB hl.gms)
  have hEBt : Nat.card (d.E ⊓ c.Bt : Subgroup G) = Nat.card (d.E ⊓ c.Bc : Subgroup G) := by
    have : d.E ⊓ c.Bt = (d.E ⊓ c.Bc).map (MulAut.conj d.t).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective, hEt]
      rfl
    rw [this, Subgroup.card_map_of_injective (MulAut.conj d.t).injective]
  have hpos : 0 < Nat.card (d.E ⊓ c.Bc : Subgroup G) := Nat.card_pos
  have hcard : Nat.card (imgSE c.S d.E c.Bc) = Nat.card (imgSE c.S d.E c.Bt) := by
    rw [hEBt, lin_card_Bt hl k c, ← hBcard] at hcBt
    exact Nat.eq_of_mul_eq_mul_right hpos (hcB.trans hcBt.symm)
  have hZ : imgSE c.S d.E d.F ≤ imgSE c.S d.E c.Bc ⊓ imgSE c.S d.E c.Bt :=
    le_inf (map_mono (subgroupOf_mono _ (lin_F_le_Bc hl k c)))
      (map_mono (subgroupOf_mono _ (lin_F_le_Bt hl k c)))
  have hEF : d.E ⊓ d.F = d.W := by rw [inf_comm]; exact lin_F_inf_E hl k c
  have hZc : Nat.card (imgSE c.S d.E d.F) = (2 ^ f) ^ 2 := by
    rw [hEF, hl.hyp.card_W hl.gms, lin_card_F hl k c] at hcF
    have h6 : 0 < (2 ^ f) ^ 6 := by positivity
    refine Nat.eq_of_mul_eq_mul_right h6 ?_
    rw [hcF]
    ring
  have hq : 2 ≤ (2 ^ f) ^ 2 := by
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    nlinarith
  have key := LinCase.radicals_card_of_product hq hR hBel' hBtel' hBn hBtn hsup hcard hZ hZc
  rw [key, hBcard] at hcB
  have hp2 : 0 < ((2 ^ f) ^ 2) ^ 2 := by positivity
  rw [inf_comm]
  refine Nat.eq_of_mul_eq_mul_left hp2 ?_
  rw [hcB]
  ring

theorem lin_exists_radicals_quotient [(d.E.subgroupOf c.S).Normal] :
    ∃ Q₁ Q₂ : Subgroup (↥c.S ⧸ d.E.subgroupOf c.S),
      LinearThree.Radicals ⊤ Q₁ Q₂ ((2 ^ f) ^ 2) := by
  have ha := k.s9a c.S c.S_syl c.P_le_S
  obtain ⟨R₁, R₂, hR⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl ha.sylow₂
  exact ⟨_, _, LinCase.radicals_quotient (lin_E_le_S hl k c) inf_le_left ha.S_eq₂.symm
    ha.E_inf₂ hR⟩

theorem lin_sec42_of_hyp (h41 : c.Sec41) : c.Sec42 := by
  haveI := lin_E_normal_S hl k c
  obtain ⟨hBel, hBcard, hBinf, hBsup⟩ := lin_sec42_basic hl k c h41
  exact ⟨hBel.isElementaryAbelian, hBcard, hBinf, hBsup,
    lin_card_Bc_inf_E hl k c h41 (lin_exists_radicals_quotient hl k c)⟩

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
