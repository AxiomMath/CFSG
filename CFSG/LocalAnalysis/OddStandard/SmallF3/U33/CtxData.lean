module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxThompson
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxRho
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxSylow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

theorem WreathRel.sq_x₁x₂_ne_one {G : Type*} [Group G] {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) :
    (x₁ * x₂) ^ 2 ≠ 1 := by
  intro hsq
  have hcomm : Commute x₁ x₂ := h.comm
  have hx1x2 : x₁ ^ 2 * x₂ ^ 2 = 1 := by
    rw [← hcomm.mul_pow 2]
    exact hsq
  have hx₂4 : x₂ ^ 4 = 1 := by
    rw [← h.ord_x₂]
    exact pow_orderOf_eq_one x₂
  have hx₂sq_inv : (x₂ ^ 2)⁻¹ = x₂ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₂4]
  have hx1sq : x₁ ^ 2 = x₂ ^ 2 := by
    calc x₁ ^ 2 = x₁ ^ 2 * (x₂ ^ 2 * (x₂ ^ 2)⁻¹) := by group
      _ = (x₁ ^ 2 * x₂ ^ 2) * (x₂ ^ 2)⁻¹ := by group
      _ = 1 * (x₂ ^ 2)⁻¹ := by rw [hx1x2]
      _ = (x₂ ^ 2)⁻¹ := by rw [one_mul]
      _ = x₂ ^ 2 := hx₂sq_inv
  have hmem : x₁ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ := by
    refine ⟨?_, ?_⟩
    · exact npow_mem_zpowers x₁ 2
    · rw [hx1sq]
      exact npow_mem_zpowers x₂ 2
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hmem
  rw [h.ord_x₁] at hdvd
  norm_num at hdvd

theorem WreathRel.sq_x₁x₂_mul_self {G : Type*} [Group G] {x₁ x₂ lam : G}
    (h : WreathRel x₁ x₂ lam) : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
  have hcomm : Commute x₁ x₂ := h.comm
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← h.ord_x₁]
    exact pow_orderOf_eq_one x₁
  have hx₂4 : x₂ ^ 4 = 1 := by
    rw [← h.ord_x₂]
    exact pow_orderOf_eq_one x₂
  rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hcomm.mul_pow 4, hx₁4, hx₂4, mul_one]

theorem wreathGrp_eq_sup {G : Type*} [Group G] (x₁ x₂ lam : G) :
    wreathGrp x₁ x₂ lam = baseGrp x₁ x₂ ⊔ zpowers lam := by
  rw [wreathGrp, baseGrp, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem Ctx0.of_data {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {x₁ x₂ lam rho : G} (hH : Hyp G t L) (hL : Nat.card L = 6048) (hW : WreathRel x₁ x₂ lam)
    (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L) (hlam : lam ∈ L) (hrho : rho ∈ L)
    (hrho3 : orderOf rho = 3) (h1 : rho * x₁ * rho⁻¹ = x₁⁻¹ * x₂)
    (h2 : rho * x₂ * rho⁻¹ = x₁⁻¹) (hlr : lam * rho * lam⁻¹ = rho⁻¹)
    (hcr : ∀ w ∈ baseGrp x₁ x₂, rho * w = w * rho → w = 1)
    (hI : ∀ g ∈ L, g * g = 1 → g ≠ 1 → ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = g)
    (hS : S ≤ invCent t) (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.relIndex (invCent t))
    (hST : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S) :
    Ctx0 t L S x₁ x₂ lam rho := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : wreathGrp x₁ x₂ lam ≤ L := by
    rw [wreathGrp, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hx₁
    · exact hx₂
    · exact hlam
  have hAL : baseGrp x₁ x₂ ≤ L := by
    rw [baseGrp, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hx₁
    · exact hx₂
  have hLle : L ≤ invCent t := by
    intro b hb
    rw [invCent, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hH.mem_centralizer) b hb
  have hPc : ∀ a ∈ twoCore t, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have ha' := ha
    rw [← hH.centralizer_eq] at ha'
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha').1) b hb).symm
  have hLt : ∀ b ∈ L, t * b = b * t := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp hH.mem_centralizer) b hb).symm
  have hPT : twoCore t ⊓ wreathGrp x₁ x₂ lam = ⊥ := by
    have hle : twoCore t ⊓ wreathGrp x₁ x₂ lam ≤ twoCore t ⊓ L :=
      le_inf inf_le_left (le_trans inf_le_right hTL)
    rw [hH.twoCore_inf] at hle
    exact eq_bot_iff.mpr hle
  have hPTc : ∀ a ∈ twoCore t, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a :=
    fun a ha b hb => hPc a ha b (hTL hb)
  have hPAc : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => hPc a ha b (hAL hb)
  have hPrho : ∀ a ∈ twoCore t, rho * a = a * rho :=
    fun a ha => (hPc a ha rho hrho).symm
  have hP2group : IsPGroup 2 (twoCore t) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(invCent t))).map (invCent t).subtype
  have hPab : IsMulCommutative (twoCore t) := by
    haveI := hH.isCyclic
    infer_instance
  have hAab : IsMulCommutative (baseGrp x₁ x₂) := (hW.baseGrp_eq).1
  have hT2group : IsPGroup 2 (wreathGrp x₁ x₂ lam) :=
    IsPGroup.of_card (n := 5) (by rw [hW.card_wreathGrp]; norm_num)
  have hcardT : Nat.card (wreathGrp x₁ x₂ lam) = 2 ^ 5 := by
    rw [hW.card_wreathGrp]
    norm_num
  have hfacL : (Nat.card L).factorization 2 = 5 := by
    rw [hL, show (6048 : ℕ) = 2 ^ 5 * 189 from by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hcard1 : Nat.card (wreathGrp x₁ x₂ lam) = 2 ^ (Nat.card L).factorization 2 := by
    rw [hcardT, hfacL]
  obtain ⟨a, ha⟩ := hP2group.exists_card_eq
  have hcardPL : Nat.card ↥(twoCore t ⊔ L) = Nat.card (twoCore t) * Nat.card L :=
    card_sup_of_commute hPc hH.twoCore_inf
  have hcardPT : Nat.card ↥(twoCore t ⊔ wreathGrp x₁ x₂ lam) =
      Nat.card (twoCore t) * Nat.card (wreathGrp x₁ x₂ lam) :=
    card_sup_of_commute hPTc hPT
  have hfacPL : (Nat.card ↥(twoCore t ⊔ L)).factorization 2 = a + 5 := by
    rw [hcardPL, ha, hL, show (6048 : ℕ) = 2 ^ 5 * 189 from by norm_num, ← mul_assoc,
      ← pow_add, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hcard2 : Nat.card ↥(twoCore t ⊔ wreathGrp x₁ x₂ lam) =
      2 ^ (Nat.card ↥(twoCore t ⊔ L)).factorization 2 := by
    rw [hcardPT, ha, hcardT, ← pow_add, hfacPL]
  have hinf_eq : S ⊓ L = wreathGrp x₁ x₂ lam :=
    inf_eq_of_isPGroup hS2 (le_inf (le_trans le_sup_right hST) hTL) hcard1
  have hinf_PL : S ⊓ (twoCore t ⊔ L) = twoCore t ⊔ wreathGrp x₁ x₂ lam :=
    inf_eq_of_isPGroup hS2 (le_inf hST (sup_le le_sup_left (le_sup_of_le_right hTL))) hcard2
  have habelian_W : IsMulCommutative (ctxW t x₁ x₂) := by
    rw [ctxW]
    exact isMulCommutative_sup_of_commute hPAc hPab hAab
  have hJ0 : CFSG.ambientMaxCardThompson (twoCore t ⊔ wreathGrp x₁ x₂ lam) =
      ctxW t x₁ x₂ := by
    rw [ctxW]
    exact ambientMaxCardThompson_sup_wreathGrp hW hPab hPTc hPT
  have hPT_eq : twoCore t ⊔ wreathGrp x₁ x₂ lam = ctxW t x₁ x₂ ⊔ zpowers lam := by
    rw [wreathGrp_eq_sup x₁ x₂ lam, ctxW, sup_assoc]
  have hrho_norm : rho ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
    rw [ctxW]
    exact rho_mem_normalizer_sup_baseGrp h1 h2 hPrho
  have hcent : ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) = twoCore t := by
    rw [ctxW]
    exact sup_baseGrp_inf_centralizer_rho hPAc hPrho hcr
  have hcomm_rho : ⁅ctxW t x₁ x₂, zpowers rho⁆ = baseGrp x₁ x₂ := by
    rw [ctxW]
    exact commutator_sup_baseGrp_rho hW h1 h2 hPAc hPrho
  have hinvol_PL : ∀ g ∈ twoCore t ⊔ L, g * g = 1 → g ≠ 1 → ∃ h ∈ invCent t,
      h * g * h⁻¹ = t ∨ h * g * h⁻¹ = (x₁ * x₂) ^ 2 ∨
        h * g * h⁻¹ = t * (x₁ * x₂) ^ 2 := by
    intro g hg hg2 hg1
    exact exists_conj_of_involution_sup hI hH.twoCore_inf hPc hH.eq_one_or_eq
      hH.mem_twoCore hLt hg hg2 hg1
  have hzL : (x₁ * x₂) ^ 2 ∈ L := Subgroup.pow_mem L (Subgroup.mul_mem L hx₁ hx₂) 2
  have ht1 : t ≠ 1 := by
    have h2 : orderOf t ≠ 1 := by rw [hH.ord_t]; norm_num
    intro h
    exact h2 (by rw [h, orderOf_one])
  have hLnorm : ∀ h ∈ invCent t, ∀ b ∈ L, h * b * h⁻¹ ∈ L := by
    intro h hh b hb
    have hbH : b ∈ invCent t := hLle hb
    have hmem := hH.normal.conj_mem (⟨b, hbH⟩ : ↥(invCent t))
      (Subgroup.mem_subgroupOf.mpr hb) (⟨h, hh⟩ : ↥(invCent t))
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hinvol_PL_distinct :=
    involution_reps_distinct hH.twoCore_inf hH.mem_twoCore ht1 hzL hW.sq_x₁x₂_ne_one hLnorm
  refine
    { hyp := hH
      le_invCent := hS
      isPGroup := hS2
      relIndex_odd := hSodd
      wreath := hW
      inf_eq := hinf_eq
      inf_PL := hinf_PL
      abelian_W := habelian_W
      J0_eq := hJ0
      PT_eq := hPT_eq
      rho_mem := hrho
      rho_normalizes := hrho_norm
      ord_rho := hrho3
      lam_rho := hlr
      cent_rho := hcent
      comm_rho := hcomm_rho
      invol_L := hI
      invol_PL := hinvol_PL
      invol_PL_distinct := hinvol_PL_distinct }

end CFSG.OddStandard.SmallF3.HarrisU33
