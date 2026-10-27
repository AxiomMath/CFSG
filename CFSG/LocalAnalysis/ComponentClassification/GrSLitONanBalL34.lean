module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalZ
public import CFSG.LocalAnalysis.OddStandard.ONanIdL34

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2
  CFSG.ABGLocalTools

abbrev KQO {G : Type} [Group G] (y : G) : Type := KQ y ⧸ pPrimeCore 2 (KQ y)

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3

theorem isPGroup_v1_quot (D : FusCtx G v1 v2 v3 s t) :
    IsPGroup 2 (zpowers (πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩)) :=
  isPGroup_zpowers_of_pow_two (k := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← D.orderOf_v1_quot, pow_orderOf_eq_one])

theorem isPGroup_s2_quot (D : FusCtx G v1 v2 v3 s t) :
    IsPGroup 2 (zpowers (πQ 𝔵 ⟨s ^ 2, D.s2_mem_Cx⟩)) :=
  isPGroup_zpowers_of_pow_two (k := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← D.orderOf_s2_quot, pow_orderOf_eq_one])

theorem lieModel_quot_core
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) :
    CFSG.Blueprint.LieModel (KQO 𝔵) .PSL 3 2 2 := by
  obtain ⟨hO, hodd⟩ := pPrimeCore_two_facts (X := KQ 𝔵)
  obtain ⟨T, hT⟩ := D.exists_sylow_quot f2QuotCheck_cert
  obtain ⟨T', hT'⟩ := exists_sylow_quot_equiv hodd T hT
  have hone' := isConj_mk_of_oneClass hodd (D.oneClass_quot hone)
  obtain ⟨K, hKn, hKL, -, hidx⟩ :=
    ThmC.onan_use_of_full hF ThmC.conclTwoClasses hO T' hT' hone'
  have ha := isPGroup_v1_quot D
  have hb := isPGroup_s2_quot D
  have hK := eq_top_of_not_isConj_order_four_cert hO hKn hKL hidx
    (u := ((πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩ : KQ 𝔵) : KQO 𝔵))
    (v := ((πQ 𝔵 ⟨s ^ 2, D.s2_mem_Cx⟩ : KQ 𝔵) : KQO 𝔵))
    (by rw [orderOf_mk_eq hodd ha, D.orderOf_v1_quot])
    (by rw [orderOf_mk_eq hodd hb, D.orderOf_s2_quot])
    (fun h => D.not_isConj_v1_s2 (isConj_of_isConj_mk hodd ha hb h))
  subst hK
  exact lieModel_PSL_of_mulEquiv Subgroup.topEquiv hKL

theorem card_pPrimeCore_quot (D : FusCtx G v1 v2 v3 s t) :
    Nat.card (pPrimeCore 2 (KQ 𝔵)) = Nat.card (theta 𝔵) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cx := centralizer ({𝔵} : Set G)
  have hcen : zpowers (zIn 𝔵) ≤ center Cx :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
  rw [CFSG.central_p_subgroup_prime_core_quotient _ hcen D.isPGroup_zpowers_zIn_x, theta,
    card_map_of_injective Cx.subtype_injective]
  have hker : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 Cx)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact (pPrimeCore_two_facts (X := Cx)).2
  have hinj : Function.Injective
      ((QuotientGroup.mk' (zpowers (zIn 𝔵))).comp (pPrimeCore 2 Cx).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : Cx) ∈ zpowers (zIn 𝔵) ⊓ pPrimeCore 2 Cx := by
      refine mem_inf.2 ⟨?_, y.2⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      exact hy
    rw [CFSG.RankThree.OddKernel.inf_eq_bot_of_odd D.isPGroup_zpowers_zIn_x
      (pPrimeCore_two_facts (X := Cx)).2, mem_bot] at h1
    exact mem_bot.2 (Subtype.ext h1)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  exact h.symm

theorem card_centralizer_x
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) :
    Nat.card (centralizer ({𝔵} : Set G)) =
      4 * Nat.card CFSG.GH74.KGroups.L34.QP.originalSubgroup * Nat.card (theta 𝔵) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel (lieModel_quot_core D hF hone)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (zIn 𝔵))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 (KQ 𝔵))
  have h4 : Nat.card (zpowers (zIn 𝔵)) = 4 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    show orderOf 𝔵 = 4
    rw [D.x_eq, orderOf_injective D.E.φ D.E.inj, xE_orderOf]
  rw [h1, h4, h2, Nat.card_congr e.toEquiv, card_pPrimeCore_quot D]
  ring

end CFSG.ComponentClassification.GrSLit.ONanBal
