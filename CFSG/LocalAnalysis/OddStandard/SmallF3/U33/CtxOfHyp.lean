module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Frame

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint


theorem exists_ctx0_of_hyp {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (h : Hyp G t L) :
    ∃ (S : Subgroup G) (x₁ x₂ lam rho : G), Ctx0 t L S x₁ x₂ lam rho := by
  obtain ⟨x₁', x₂', lam', rho', _α, hf⟩ := exists_frame_of_psu33 h.lieModel
  have hL : Nat.card L = 6048 := card_K_of_psu33 h.lieModel
  have hx₁ : (x₁' : G) ∈ L := x₁'.2
  have hx₂ : (x₂' : G) ∈ L := x₂'.2
  have hlam : (lam' : G) ∈ L := lam'.2
  have hrho : (rho' : G) ∈ L := rho'.2
  have hW : WreathRel (x₁' : G) (x₂' : G) (lam' : G) :=
    hf.wreath.map' L.subtype L.subtype_injective
  have hrho3 : orderOf (rho' : G) = 3 := by
    rw [Subgroup.orderOf_coe rho']
    exact hf.ord_rho
  have h1 : (rho' : G) * (x₁' : G) * (rho' : G)⁻¹ = (x₁' : G)⁻¹ * (x₂' : G) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv]
      using congrArg (fun k : ↥L => (k : G)) hf.rho_x₁
  have h2 : (rho' : G) * (x₂' : G) * (rho' : G)⁻¹ = (x₁' : G)⁻¹ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv]
      using congrArg (fun k : ↥L => (k : G)) hf.rho_x₂
  have hlr : (lam' : G) * (rho' : G) * (lam' : G)⁻¹ = (rho' : G)⁻¹ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv]
      using congrArg (fun k : ↥L => (k : G)) hf.lam_rho
  have hbase : (baseGrp x₁' x₂').map L.subtype = baseGrp (x₁' : G) (x₂' : G) := by
    rw [show baseGrp x₁' x₂' = Subgroup.closure ({x₁', x₂'} : Set ↥L) from rfl,
      show baseGrp (x₁' : G) (x₂' : G) =
        Subgroup.closure ({(x₁' : G), (x₂' : G)} : Set G) from rfl,
      MonoidHom.map_closure, Set.image_pair]
    rfl
  have hcr : ∀ w ∈ baseGrp (x₁' : G) (x₂' : G),
      (rho' : G) * w = w * (rho' : G) → w = 1 := by
    intro w hw hcomm
    rw [← hbase] at hw
    obtain ⟨w', hw', hw'e⟩ := Subgroup.mem_map.mp hw
    have hcomm' : rho' * w' = w' * rho' := by
      apply L.subtype_injective
      simp only [map_mul, hw'e]
      exact hcomm
    have hw'1 : w' = 1 := hf.cent_rho w' hw' hcomm'
    rw [← hw'e, hw'1]
    rfl
  have hI : ∀ g ∈ L, g * g = 1 → g ≠ 1 →
      ∃ c ∈ L, c * ((x₁' : G) * (x₂' : G)) ^ 2 * c⁻¹ = g := by
    intro g hg hgg hg1
    have hz2 : ((x₁' * x₂') ^ 2 : ↥L) * (x₁' * x₂') ^ 2 = 1 :=
      WreathRel.sq_x₁x₂_mul_self hf.wreath
    have hz1 : ((x₁' * x₂') ^ 2 : ↥L) ≠ 1 :=
      WreathRel.sq_x₁x₂_ne_one hf.wreath
    have hgsq : (⟨g, hg⟩ : ↥L) * ⟨g, hg⟩ = 1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hgg
    have hg1' : (⟨g, hg⟩ : ↥L) ≠ 1 := by
      intro hh
      exact hg1 (by
        have := congrArg (fun k : ↥L => (k : G)) hh
        simpa using this)
    obtain ⟨c, hc⟩ := invol_conj_of_psu33 h.lieModel hz2 hz1 hgsq hg1'
    refine ⟨(c : G), c.2, ?_⟩
    have hcG := congrArg (fun k : ↥L => (k : G)) hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using hcG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP_le_cent : twoCore t ≤ Subgroup.centralizer (L : Set G) := by
    rw [← h.centralizer_eq]
    exact inf_le_left
  have hL_invCent : L ≤ invCent t := by
    intro g hg
    change g ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h.mem_centralizer g hg
  have hP_le_invCent : twoCore t ≤ invCent t := by
    have := Subgroup.map_subtype_le (CFSG.pCore 2 ↥(invCent t))
    simpa only [twoCore, CFSG.Open.pCoreOf] using this
  have hT_le_L : wreathGrp (x₁' : G) (x₂' : G) (lam' : G) ≤ L := by
    rw [show wreathGrp (x₁' : G) (x₂' : G) (lam' : G) =
        Subgroup.closure ({(x₁' : G), (x₂' : G), (lam' : G)} : Set G) from rfl,
      Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · exact hx₁
    · exact hx₂
    · exact hlam
  have hT_le_invCent : wreathGrp (x₁' : G) (x₂' : G) (lam' : G) ≤ invCent t :=
    hT_le_L.trans hL_invCent
  have hPT_le_invCent :
      twoCore t ⊔ wreathGrp (x₁' : G) (x₂' : G) (lam' : G) ≤ invCent t :=
    sup_le hP_le_invCent hT_le_invCent
  have hcommG : ∀ a ∈ twoCore t,
      ∀ b ∈ wreathGrp (x₁' : G) (x₂' : G) (lam' : G), a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hP_le_cent ha)) b (hT_le_L hb)).symm
  have hP2 : IsPGroup 2 (twoCore t) := by
    change IsPGroup 2 ((CFSG.pCore 2 ↥(invCent t)).map (invCent t).subtype)
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(invCent t))).map (invCent t).subtype
  have hT2 : IsPGroup 2 (wreathGrp (x₁' : G) (x₂' : G) (lam' : G)) :=
    IsPGroup.of_card (n := 5) (by rw [hW.card_wreathGrp]; norm_num)
  have hPT2 : IsPGroup 2 ↥(twoCore t ⊔ wreathGrp (x₁' : G) (x₂' : G) (lam' : G)) :=
    isPGroup_sup_of_commute hcommG hP2 hT2
  obtain ⟨S, hS_le, hS2, hSodd, hPTS⟩ :=
    exists_sylow_of_isPGroup (p := 2) (H := invCent t)
      (Q := twoCore t ⊔ wreathGrp (x₁' : G) (x₂' : G) (lam' : G)) hPT_le_invCent hPT2
  exact ⟨S, (x₁' : G), (x₂' : G), (lam' : G), (rho' : G),
    Ctx0.of_data h hL hW hx₁ hx₂ hlam hrho hrho3 h1 h2 hlr hcr hI hS_le hS2 hSodd hPTS⟩

end CFSG.OddStandard.SmallF3.HarrisU33
