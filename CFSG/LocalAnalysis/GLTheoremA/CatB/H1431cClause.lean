module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cTransA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.LocalAnalysis.GLTheoremA (pQuotHom coprime_card_inf_ker_pQuotHom glaPComponent_subgroupOf
  glaPComponent_eq_of_map_eq chev_coe_normalizerMonoidHom)

variable {G : Type} [Group G] [Finite G]

theorem glaPrimeCoreOf_le_self' {L : Subgroup G} : GLAPPrimeCoreOf 3 L ≤ L := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := CFSG.LocalAnalysis.GLTheoremA.I137Tr.mem_glaPPrimeCoreOf_iff.1 hg
  exact h.2

theorem inv_comm_of_comm {f d : G} (hf : f * d = d * f) : f⁻¹ * d = d * f⁻¹ := by
  calc f⁻¹ * d = f⁻¹ * (d * f) * f⁻¹ := by group
    _ = f⁻¹ * (f * d) * f⁻¹ := by rw [hf]
    _ = d * f⁻¹ := by group

theorem conj_comm_of_comm {f d h : G} (hf : f * d = d * f) (hh : h * d = d * h) :
    (f * h * f⁻¹) * d = d * (f * h * f⁻¹) := by
  calc f * h * f⁻¹ * d = f * h * (f⁻¹ * d) := by group
    _ = f * h * (d * f⁻¹) := by rw [inv_comm_of_comm hf]
    _ = f * (h * d) * f⁻¹ := by group
    _ = f * (d * h) * f⁻¹ := by rw [hh]
    _ = (f * d) * h * f⁻¹ := by group
    _ = d * (f * h * f⁻¹) := by rw [hf]; group

theorem normalizer_inf_centralizer {K : Subgroup G} {d e : G} (he : e ∈ Subgroup.normalizer (K : Set G))
    (hed : e * d = d * e) :
    e ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := by
  have hed' : e⁻¹ * d = d * e⁻¹ := inv_comm_of_comm hed
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← Subgroup.mem_normalizer_iff.1 he h]
  constructor
  · rintro ⟨hK, hc⟩
    exact ⟨hK, conj_comm_of_comm hed hc⟩
  · rintro ⟨hK, hc⟩
    refine ⟨hK, ?_⟩
    have h2 := conj_comm_of_comm hed' hc
    have hsimp : e⁻¹ * (e * h * e⁻¹) * e⁻¹⁻¹ = h := by group
    rwa [hsimp] at h2

theorem innerOnMod_imp_inducesInnerMod {K J : Subgroup G} {d e : G}
    (he : e ∈ Subgroup.normalizer (K : Set G)) (hed : e * d = d * e)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({d} : Set G)) J)
    (hinn : InnerOnMod 3 (imgK K J) (barAut 3 K ⟨e, he⟩)) : InducesInnerMod 3 J e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({d} : Set G) with hC
  set τ := barAut 3 K ⟨e, he⟩ with hτ
  have hJC : J ≤ C := hJ.1
  have hJK : J ≤ K := hJC.trans inf_le_left
  have heC : e ∈ Subgroup.normalizer (C : Set G) := normalizer_inf_centralizer he hed
  obtain ⟨lb, hlb, hall⟩ := hinn
  have step1 : ∀ x ∈ imgK K J, τ.symm x ∈ imgK K J := by
    intro x hx
    have h2 : (lb⁻¹ * x * lb)⁻¹ * τ.symm x ∈ imgK K J := glaPrimeCoreOf_le_self' (hall x hx)
    have hl : lb⁻¹ * x * lb ∈ imgK K J :=
      (imgK K J).mul_mem ((imgK K J).mul_mem ((imgK K J).inv_mem hlb) hx) hlb
    have h3 : τ.symm x = (lb⁻¹ * x * lb) * ((lb⁻¹ * x * lb)⁻¹ * τ.symm x) := by group
    rw [h3]
    exact (imgK K J).mul_mem hl h2
  have step2 : (imgK K J).map τ.symm.toMonoidHom = imgK K J := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact step1 x hx
    · exact le_of_eq (Subgroup.card_map_of_injective τ.symm.injective).symm
  have hC' : GLBConj e C = C := mem_normalizer_iff_gLBConj_eq.1 heC
  have hJ' : GLAPComponent 3 C (GLBConj e J) := by
    have h := glaPComponent_gLBConj hJ e
    rw [hC'] at h
    exact h
  have claimA : ((GLBConj e J).subgroupOf K).map (pQuotHom 3 K) = (imgK K J).map τ.symm.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyJ : e * (y : G) * e⁻¹ ∈ J := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hy)
      set w : ↥K := K.normalizerMonoidHom ⟨e, he⟩ y with hw
      have hwJ : (w : G) ∈ J := by
        rw [hw, chev_coe_normalizerMonoidHom]
        exact hyJ
      refine ⟨pQuotHom 3 K w, Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 hwJ, rfl⟩, ?_⟩
      show τ.symm (pQuotHom 3 K w) = pQuotHom 3 K y
      rw [hτ, barAut_symm_pQuotHom]
      congr 1
      apply Subtype.ext
      rw [hw, chev_coe_normalizerMonoidHom, chev_coe_normalizerMonoidHom]
      dsimp only
      group
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
      set y : ↥K := K.normalizerMonoidHom ⟨e⁻¹, Subgroup.inv_mem _ he⟩ u with hy
      have hyJ : (y : G) ∈ GLBConj e J := by
        rw [mem_gLBConj]
        have : e * (y : G) * e⁻¹ = (u : G) := by
          rw [hy, chev_coe_normalizerMonoidHom]
          dsimp only
          group
        rw [this]
        exact Subgroup.mem_subgroupOf.1 hu
      refine ⟨y, Subgroup.mem_subgroupOf.2 hyJ, ?_⟩
      show pQuotHom 3 K y = τ.symm (pQuotHom 3 K u)
      rw [hτ, barAut_symm_pQuotHom]
  have hmap : (J.subgroupOf K).map (pQuotHom 3 K) = ((GLBConj e J).subgroupOf K).map (pQuotHom 3 K) := by
    rw [claimA, step2]
    rfl
  have hJeq : J.subgroupOf K = (GLBConj e J).subgroupOf K := by
    refine glaPComponent_eq_of_map_eq (X := C.subgroupOf K) (J₁ := J.subgroupOf K)
      (J₂ := (GLBConj e J).subgroupOf K) Nat.prime_three (pQuotHom 3 K) ?_ ?_ ?_ hmap
    · exact coprime_card_inf_ker_pQuotHom Nat.prime_three K (C.subgroupOf K)
    · exact glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
    · exact glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ'
  have hJ'K : GLBConj e J ≤ K := by
    intro y hy
    have hyJ : e * y * e⁻¹ ∈ J := mem_gLBConj.1 hy
    exact (Subgroup.mem_normalizer_iff.1 he y).2 (hJK hyJ)
  have hJ_eq : J = GLBConj e J := by
    have h := congrArg (Subgroup.map K.subtype) hJeq
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJK,
      inf_eq_left.2 hJ'K] at h
    exact h
  have hconjJ : ∀ y ∈ J, e⁻¹ * y * e ∈ J := by
    intro y hy
    have h1 : e⁻¹ * y * e ∈ GLBConj e J := by
      rw [mem_gLBConj]
      have : e * (e⁻¹ * y * e) * e⁻¹ = y := by group
      rw [this]
      exact hy
    rw [← hJ_eq] at h1
    exact h1
  obtain ⟨u₀, hu₀, hu₀l⟩ := Subgroup.mem_map.1 hlb
  have hlJ : (u₀ : G) ∈ J := Subgroup.mem_subgroupOf.1 hu₀
  refine ⟨(u₀ : G), hlJ, fun y hy => ?_⟩
  have hyK : y ∈ K := hJK hy
  have hzJ : (((u₀ : G))⁻¹ * y * (u₀ : G))⁻¹ * (e⁻¹ * y * e) ∈ J :=
    J.mul_mem (J.inv_mem (J.mul_mem (J.mul_mem (J.inv_mem hlJ) hy) hlJ)) (hconjJ y hy)
  have hEq : pQuotHom 3 K ⟨(((u₀ : G))⁻¹ * y * (u₀ : G))⁻¹ * (e⁻¹ * y * e), hJK hzJ⟩ =
      (lb⁻¹ * pQuotHom 3 K ⟨y, hyK⟩ * lb)⁻¹ * (barAut 3 K ⟨e, he⟩).symm (pQuotHom 3 K ⟨y, hyK⟩) := by
    have hzK : (⟨(((u₀ : G))⁻¹ * y * (u₀ : G))⁻¹ * (e⁻¹ * y * e), hJK hzJ⟩ : ↥K) =
        (u₀⁻¹ * ⟨y, hyK⟩ * u₀)⁻¹ * K.normalizerMonoidHom ⟨e⁻¹, Subgroup.inv_mem _ he⟩ ⟨y, hyK⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, chev_coe_normalizerMonoidHom, inv_inv,
        Subgroup.coe_mk]
    rw [hzK]
    simp only [map_mul, map_inv]
    rw [hu₀l, ← barAut_symm_pQuotHom he ⟨y, hyK⟩]
  have hcore := hall _ (Subgroup.mem_map.2 ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩)
  apply mem_of_pQuot_mem_core hJK hzJ
  change pQuotHom 3 K ⟨(((u₀ : G))⁻¹ * y * (u₀ : G))⁻¹ * (e⁻¹ * y * e), hJK hzJ⟩ ∈
    GLAPPrimeCoreOf 3 (imgK K J)
  rw [hEq]
  exact hcore

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
