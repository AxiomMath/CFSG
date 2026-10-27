module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

private theorem z4i_Q_le_ctxCQ_aux :
    ctxQ t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho :=
  fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hz.Q_comm b hb a ha

theorem z4j_cent_N_t {Ng : Subgroup G} (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    ∀ n ∈ hz.z4iSub Ng, hz.z4iT * n = n * hz.z4iT → n = 1 := by
  intro n hn hcomm
  have hnC : (n : G) ∈ ctxCQ t tau x₁ x₂ rho := hN.le_C hn
  have hnt : t * (n : G) = (n : G) * t := by
    have h := congrArg Subtype.val hcomm
    simpa only [Subgroup.coe_mul, Ctx4Z.z4iT] using h
  have hW : (n : G) ∈ ctxWN t tau x₁ x₂ rho := by
    rw [hz.mem_ctxWN_iff]
    refine ⟨hnC, ?_⟩
    have h1 : (n : G) * t * (n : G)⁻¹ * t⁻¹ = 1 := by rw [← hnt]; group
    rw [h1]
    exact one_mem _
  have hcent : (n : G) ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hnt.symm
  have hbase : (n : G) ∈ baseGrp x₁ x₂ := by
    have h2 : (n : G) ∈ ctxWN t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨hW, hcent⟩
    rwa [hz.ctxWN_inf_centralizer_t] at h2
  have hq : (n : G) ∈ ctxQ t tau x₁ x₂ rho := hz.base_le_Q hbase
  have hbot : (n : G) ∈ (⊥ : Subgroup G) := by
    rw [← hN.inf_Q]
    exact ⟨hn, hq⟩
  exact Subtype.ext (by simpa using hbot)

theorem z4j_K_triv_X {Ng : Subgroup G} (hN : Z4IOdd t tau x₁ x₂ rho Ng)
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1) :
    ∀ k ∈ ⁅centralizer ((hz.z4iSub (ctxYq t tau x₁ x₂ rho) :
          Subgroup ↥(ctxNQ t tau x₁ x₂ rho)) : Set ↥(ctxNQ t tau x₁ x₂ rho)), zpowers hz.z4iRho⁆ ⊔
        (hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng),
      hz.z4iT * k * hz.z4iT⁻¹ * k⁻¹ ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng →
        k ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng := by
  intro k hk hkt
  have hKI_le : ctxKI t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho :=
    Subgroup.relIndex_eq_one.mp hrel
  have hkKI : (k : G) ∈ ctxKI t tau x₁ x₂ rho := by
    rw [ctxKI, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have hle : ⁅centralizer ((hz.z4iSub (ctxYq t tau x₁ x₂ rho) :
              Subgroup ↥(ctxNQ t tau x₁ x₂ rho)) : Set ↥(ctxNQ t tau x₁ x₂ rho)),
              zpowers hz.z4iRho⁆ ⊔
            (hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng) ≤
            (⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho).subgroupOf
              (ctxNQ t tau x₁ x₂ rho) := by
        apply sup_le
        · rw [Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          rw [Subgroup.mem_subgroupOf]
          have h1 : (g₁ : G) ∈ ctxEcY t tau x₁ x₂ rho := by
            refine ⟨g₁.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
            intro a ha
            have ha' : (⟨a, hz.z4i_Q_le_NQ (hz.Y_le_Q ha)⟩ :
                ↥(ctxNQ t tau x₁ x₂ rho)) ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho) := ha
            have hcomm := (Subgroup.mem_centralizer_iff.mp hg₁) _ ha'
            simpa using congrArg Subtype.val hcomm
          have h2 : (g₂ : G) ∈ zpowers rho := by
            have hsub : zpowers hz.z4iRho ≤
                (zpowers rho).subgroupOf (ctxNQ t tau x₁ x₂ rho) := by
              rw [Subgroup.zpowers_le]
              exact Subgroup.mem_zpowers rho
            exact hsub hg₂
          exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator h1 h2)
        · apply sup_le
          · intro g hg
            rw [Subgroup.mem_subgroupOf]
            exact Subgroup.mem_sup_right (z4i_Q_le_ctxCQ_aux hz hg)
          · intro g hg
            rw [Subgroup.mem_subgroupOf]
            exact Subgroup.mem_sup_right (hN.le_C hg)
      exact hle hk
    · refine ⟨k.2, ?_⟩
      have hmem : (hz.z4iT * k * hz.z4iT⁻¹ * k⁻¹ :
          ↥(ctxNQ t tau x₁ x₂ rho)) ∈ hz.z4iSub (ctxCQ t tau x₁ x₂ rho) := by
        rwa [hz.z4i_sup_sub hN] at hkt
      have hmemC : (t * (k : G) * t⁻¹ * (k : G)⁻¹) ∈ ctxCQ t tau x₁ x₂ rho := hmem
      have hconj : (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := by
        have h := inv_mem hmemC
        convert h using 1
        group
      exact hconj
  have hkC : k ∈ hz.z4iSub (ctxCQ t tau x₁ x₂ rho) := hKI_le hkKI
  rwa [← hz.z4i_sup_sub hN] at hkC

theorem z4j_tt_odd :
    ¬ 2 ∣ (closure ({hz.z4iT, hz.z4iTau} : Set ↥(ctxNQ t tau x₁ x₂ rho))).relIndex
      (centralizer ({hz.z4iRho} : Set ↥(ctxNQ t tau x₁ x₂ rho))) := by
  intro h
  apply hz.tt_sylow.2.2
  have hcls : (closure ({t, tau} : Set G)).subgroupOf (ctxNQ t tau x₁ x₂ rho) =
      closure ({hz.z4iT, hz.z4iTau} : Set ↥(ctxNQ t tau x₁ x₂ rho)) := by
    have h0 := z4j_subgroupOf_closure (K := ctxNQ t tau x₁ x₂ rho)
      ({hz.z4iT, hz.z4iTau} : Set ↥(ctxNQ t tau x₁ x₂ rho))
    rwa [show Subtype.val '' ({hz.z4iT, hz.z4iTau} : Set ↥(ctxNQ t tau x₁ x₂ rho)) =
        ({t, tau} : Set G) by rw [Set.image_pair]; rfl] at h0
  have hcen : (ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G)).subgroupOf
        (ctxNQ t tau x₁ x₂ rho) =
      centralizer ({hz.z4iRho} : Set ↥(ctxNQ t tau x₁ x₂ rho)) := by
    rw [Subgroup.inf_subgroupOf_left]
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ centralizer ({rho} : Set G) := hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx'))
    · intro hx
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hx')
  rwa [← Subgroup.relIndex_subgroupOf (H := closure ({t, tau} : Set G))
      (K := ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G))
      (L := ctxNQ t tau x₁ x₂ rho) inf_le_left, hcls, hcen]

theorem z4j_card_U : Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 9 := by
  have hfac : (3 * 2 ^ 9).factorization 2 = 9 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      Nat.factorization_pow_self Nat.prime_two]
  rw [S4B.card_eq_of_isSylowIn hz.U_sylow, hz.card_M, hfac]

theorem z4j_two_pow_ten : 2 ^ 10 ∣ Nat.card ↥(ctxNQ t tau x₁ x₂ rho) := by
  have hU_le : ctxU t tau x₁ x₂ lam ≤ ctxNQ t tau x₁ x₂ rho :=
    hz.U_sylow.1.trans hz.z4i_M_le_NQ
  have hdvd : 2 ∣ (hz.z4iSub (ctxU t tau x₁ x₂ lam)).index := by
    by_contra h
    exact hz.U_not_sylow_L ⟨hU_le, hz.U_sylow.2.1, h⟩
  obtain ⟨m, hm⟩ := hdvd
  have hcard : Nat.card (hz.z4iSub (ctxU t tau x₁ x₂ lam)) = 2 ^ 9 := by
    rw [hz.z4i_card_sub hU_le, z4j_card_U hz]
  have hmul := Subgroup.card_mul_index (H := hz.z4iSub (ctxU t tau x₁ x₂ lam))
  rw [hcard, hm] at hmul
  rw [← hmul]
  exact ⟨m, by ring⟩

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
