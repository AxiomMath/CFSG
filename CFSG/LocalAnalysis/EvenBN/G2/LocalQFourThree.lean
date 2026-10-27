module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourTwo
public import CFSG.LocalAnalysis.EvenBN.Common.HeisLikeSL3

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourLight

variable {K : Type} [Field K]

theorem conj_map_leviA2 (h : Setup G L f t) (d : G2Data L K) :
    ∀ x ∈ (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
      (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))),
      QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
          ⟨t, h.t_mem_centralizer_J₁ d⟩ * x *
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
          ⟨t, h.t_mem_centralizer_J₁ d⟩)⁻¹ = x := by
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← mem_centralizer_iff.1 (h.t_mem_centralizer_leviA2 d) _ (mem_subgroupOf.1 hk),
    mul_inv_cancel_right]

end QFourLight

section QFourLayer

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite G] in
theorem sbY_le_leviA2 (d : G2Data L K) (hK4 : Nat.card K = 4) : d.sbY ≤ d.leviA2 := by
  rw [← d.S_inf_centralizer_J₁_four hK4, ← (d.yamada_3_10_J₁_four_G hK4).1]
  exact inf_le_inf_right _ d.inclusions.2.2.2.2.2.2.2.2.2

theorem exists_map_leviA2_not_comm (d : G2Data L K) (hK4 : Nat.card K = 4) :
    ∃ a ∈ (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))),
      ∃ b ∈ (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))), a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (d.J₁ : Set G) with hH
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hsbH : d.sbY ≤ H := (sbY_le_leviA2 d hK4).trans (d.leviA2_le_centralizer_J₁ hK4)
  have hp₁ := d.xb₁_mem_sbY
  have hp₂ := d.x3ab₁_mem_sbY
  refine ⟨π ⟨_, hsbH hp₁⟩, ⟨⟨_, hsbH hp₁⟩, sbY_le_leviA2 d hK4 hp₁, rfl⟩,
    π ⟨_, hsbH hp₂⟩, ⟨⟨_, hsbH hp₂⟩, sbY_le_leviA2 d hK4 hp₂, rfl⟩, fun e => ?_⟩
  apply d.xb₁_mul_x3ab₁_ne
  set c : H := ⟨_, hsbH hp₁⟩ * ⟨_, hsbH hp₂⟩ * (⟨_, hsbH hp₁⟩ : H)⁻¹ * (⟨_, hsbH hp₂⟩ : H)⁻¹
    with hc
  have hcO : c ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.oddCore H), ← QuotientGroup.mk'_apply, ← hπ, hc,
      map_mul, map_mul, map_mul, map_inv, map_inv, e]
    group
  have hc2 : IsPGroup 2 (d.sbY.subgroupOf H) :=
    ((d.isSylowOf_S.isPGroup.to_le (d.S_inf_centralizer_J₁_four hK4 ▸ inf_le_left)).comap_subtype)
  have hcsb : c ∈ d.sbY.subgroupOf H := by
    rw [hc, mem_subgroupOf]
    exact mul_mem (mul_mem (mul_mem hp₁ hp₂) (inv_mem hp₁)) (inv_mem hp₂)
  obtain ⟨k, hk⟩ := hc2 ⟨c, hcsb⟩
  have hc1 : c = 1 := TrialityD4.eq_one_of_mem_oddCore_of_pow_D4 hcO (k := k) (by
    have := congrArg Subtype.val hk
    simpa using this)
  have h1 := congrArg Subtype.val hc1
  simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h1
  calc d.xb₁ * d.x3ab₁ = d.xb₁ * d.x3ab₁ * d.xb₁⁻¹ * d.x3ab₁⁻¹ * (d.x3ab₁ * d.xb₁) := by group
    _ = d.x3ab₁ * d.xb₁ := by rw [h1, one_mul]

theorem map_yamadaB_eq (h : Setup G L f t) (d : G2Data L K) (hK4 : Nat.card K = 4)
    {Kc : Subgroup (centralizer (d.J₁ : Set G) ⧸ CFSG.oddCore (centralizer (d.J₁ : Set G)))}
    (hKc : CFSG.IsComponent Kc) (hZ : center Kc = ⊥)
    (hKle : (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom) :
    ((yamadaB d).subgroupOf (centralizer (d.J₁ : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) =
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom := by
  obtain ⟨-, hsyl, -⟩ := h.yamada_5_10_hr7 d hK4
  have hcomp := fun C hC =>
    Common.isComponent_eq_of_le_sup_of_card_le_two (C := C) hKc hKle hsyl hC
  have hKbs := conj_map_leviA2 h d
  have hB : (yamadaB d).subgroupOf (centralizer (d.J₁ : Set G)) =
      normalClosure (((L ⊓ centralizer (d.J₁ : Set G)).subgroupOf
        (centralizer (d.J₁ : Set G)) : Subgroup _) : Set (centralizer (d.J₁ : Set G))) :=
    comap_map_eq_self_of_injective (centralizer (d.J₁ : Set G)).subtype_injective _
  rw [hB, map_normalClosure _ _ (QuotientGroup.mk'_surjective _), ← coe_map,
    (d.yamada_3_10_J₁_four_G hK4).1]
  exact Common.normalClosure_eq_sup_of_isComponent hKc hZ hcomp hKle hKbs
    (exists_map_leviA2_not_comm d hK4)

theorem qFourSylowPackage_of_cat (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3)
    {V : Subgroup G} (hV : IsSylowOf 2 V (yamadaB d))
    (hXV : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V) : QFourSylowPackage d V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kc, hKc, hKle, hcase⟩ := h.yamada_5_10_layer_of_cat d hK hK4 hcat
  have hZ : center Kc = ⊥ := by
    rcases hcase with ⟨-, -, -, -, hZ, -⟩ | ⟨-, -, hZ, -⟩ <;> exact hZ
  have hB := h.map_yamadaB_eq d hK4 hKc hZ hKle
  have hKH : d.leviA2 ≤ centralizer (d.J₁ : Set G) := d.leviA2_le_centralizer_J₁ hK4
  have hVH : V ≤ centralizer (d.J₁ : Set G) := hV.le.trans (yamadaB_le_centralizer_J₁ d)
  have hcase' : (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = Kc ∧
        LieModel Kc .PSL 3 2 (2 * 2)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom,
          x * y = y * x) ∧
        Kc ⊓ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = ⊥ ∧
        LieModel Kc .PSL 3 2 2 ∧
        LieModel (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom) .PSL 3 2 2 ∧
        (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) ⊓ Kc = ⊥ ∧
        (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) ⊓
          Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = ⊥) := by
    rcases hcase with ⟨heq, -, -, -, -, hlie⟩ | ⟨-, hcomm, -, ⟨e⟩⟩
    · exact Or.inl ⟨heq, hlie⟩
    · right
      set tb := QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
        ⟨t, h.t_mem_centralizer_J₁ d⟩ with htb
      have hKcc : ∀ x ∈ Kc, ∀ y ∈ Kc.map (MulAut.conj tb).toMonoidHom, x * y = y * x :=
        fun x hx y hy => by
          have := commutator_mem_commutator hx hy
          rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
      have hKcinf : Kc ⊓ Kc.map (MulAut.conj tb).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hyc : (⟨y, (Subgroup.mem_inf.1 hy).1⟩ : Kc) ∈ center Kc :=
          mem_center_iff.2 fun x => Subtype.ext (hKcc x x.2 y (Subgroup.mem_inf.1 hy).2)
        rw [hZ, mem_bot] at hyc
        exact mem_bot.2 (congrArg Subtype.val hyc)
      obtain ⟨hcompK, -, -⟩ := h.yamada_5_10_hr7 d hK4
      have hne' := SeitzReduction.ne_bot_of_isQuasisimple hcompK.2.2
      have hKbm := SeitzReduction.LinearPilot.lieModel_quotient_center_map_oddCore hKH
        (d.isQuasisimple_leviA2 hK4) (d.lieModel_leviA2 hK4) hne'
      have hZK : center ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G))))) = ⊥ := by
        rw [← map_center_eq e, hZ, Subgroup.map_bot]
      have hKbl := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot) hKbm
      have hKcl := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hKbl
      have hKcl' := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (Kc.equivMapOfInjective (MulAut.conj tb).toMonoidHom (MulAut.conj tb).injective) hKcl
      have hKbs := conj_map_leviA2 h d
      refine ⟨hKcc, hKcinf, hKcl, hKcl', ?_, ?_⟩
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
        have h1 : x ∈ Kc.map (MulAut.conj tb).toMonoidHom := by
          rw [← hKbs x hxK]
          exact ⟨x, hxc, rfl⟩
        rw [← hKcinf]
        exact Subgroup.mem_inf.2 ⟨hxc, h1⟩
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
        obtain ⟨c, hc, hcx⟩ := hxc
        have h1 : x = c := by
          have e1 := hKbs x hxK
          have e2 : tb * c * tb⁻¹ = x := hcx
          calc x = tb⁻¹ * (tb * x * tb⁻¹) * tb := by group
            _ = tb⁻¹ * x * tb := by rw [e1]
            _ = tb⁻¹ * (tb * c * tb⁻¹) * tb := by rw [e2]
            _ = c := by group
        rw [← hKcinf]
        exact Subgroup.mem_inf.2 ⟨h1 ▸ hc, ⟨c, hc, hcx⟩⟩
  have hV' : IsSylowOf 2 (V.subgroupOf (centralizer (d.J₁ : Set G)))
      ((yamadaB d).subgroupOf (centralizer (d.J₁ : Set G))) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.2 hVH,
      inf_eq_left.2 (yamadaB_le_centralizer_J₁ d)]
    exact hV
  have hpk := Common.sylowPackage_of_isSylowOf_of_map_eq hB (g := 2) (by norm_num) hcase' hV'
  have hpk' := hpk.map (centralizer (d.J₁ : Set G)).subtype
    (centralizer (d.J₁ : Set G)).subtype_injective
  rw [subgroupOf_map_subtype, inf_eq_left.2 hVH, subgroupOf_map_subtype, inf_eq_left.2 hKH]
    at hpk'
  obtain ⟨h1, h2, h3, h4⟩ := hpk'
  have hsbV : d.sbY ≤ V := by
    rw [← yamadaD₁_inf_centralizer_J₁_inf_D d hK4]
    exact inf_le_left.trans hXV
  refine ⟨by rw [h1, hK4]; norm_num, h2, h3, fun a ha b hb hab x hx hxa hxb => ?_⟩
  exact h4 a ⟨sbY_le_leviA2 d hK4 ha, hsbV ha⟩ b ⟨sbY_le_leviA2 d hK4 hb, hsbV hb⟩ hab x hx hxa hxb

theorem yamada_5_10_1_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    yamadaD₁ d t = d.D ⊔ yamadaU₁ d t ∧ yamadaU₁ d t ⊓ centralizer ({t} : Set G) = d.U ∧
      Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 :=
  h.yamada_5_10_1_four_of_package d hK hK4 fun _ hV hXV =>
    h.qFourSylowPackage_of_cat d hK hK4 hcat hV hXV

theorem yamada_5_10_2_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    CFSG.IsElementaryAbelian 2 (yamadaU₁ d t) :=
  h.yamada_5_10_2_four_of_package d hK hK4 fun _ hV hXV =>
    h.qFourSylowPackage_of_cat d hK hK4 hcat hV hXV

theorem yamada_5_10_3_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    yamadaU₁ d t = yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G) ∧
      yamadaU₁ d t ≤ yamadaF₁ d t :=
  h.yamada_5_10_3_four_of_package d hK hK4 fun _ hV hXV =>
    h.qFourSylowPackage_of_cat d hK hK4 hcat hV hXV

theorem yamada_5_10_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3)
    {V : Subgroup G} (hV : IsSylowOf 2 V (yamadaB d))
    (hXV : yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ V) :
    yamadaU₁ d t = V ⊓ centralizer (V : Set G) ∧ ElemModulo (yamadaU₁ d t) V :=
  h.yamada_5_10_4_of_package d hK hK4 (fun _ hV' hXV' =>
    h.qFourSylowPackage_of_cat d hK hK4 hcat hV' hXV') hV hXV

end QFourLayer

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
