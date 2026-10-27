module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2CentCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.External
open scoped commutatorElement

theorem centralizer_fixD_P
    : Subgroup.centralizer (fixD : Set P) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hqX : (q : Equiv.Perm (Fin 315)) * permX = permX * q :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hq elemX elemX_mem)).symm
  have hqY : (q : Equiv.Perm (Fin 315)) * permY = permY * q :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hq elemY elemY_mem)).symm
  have hcount : countProducts 315 (commAll 315 [toTable permX, toTable permY])
      (levelTables autChain) (idT 315) = 1 := by
    rw [toTable_eq_arrTable rep_permX, toTable_eq_arrTable rep_permY, levelTables_autChain]
    exact centPD_check
  have h1 : (q : Equiv.Perm (Fin 315)) = 1 :=
    eq_one_of_countProducts autChain_valid hcount
      (by rw [autChain_originalSubgroup]; exact q.2) hqX hqY
  exact Subtype.ext h1

theorem tabAutCent_patB
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatB X K t) (Y : Subgroup G) (hYn : Y ≤ Subgroup.normalizer (X : Set G))
    (hYc : Y ≤ Subgroup.centralizer (K : Set G)) :
    (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  obtain ⟨hL32, ⟨e⟩, -, hout⟩ := hpat
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* P :=
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.J2).trans nativeEquivP
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  have hX : Group.IsPerfect ↥X := hXq.1
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hK]
    exact perfectResidualOf_le _
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self (quotProj e') hπ hker ht ht2
  have hα1 := quotAct_ne_one (quotProj e') hπ hker ht hXq hcomm
  have hαout : quotAct (quotProj e') hπ hker ht ∉ inner P := fun h =>
    hout (inducesInner_of_quotAct_mem_inner (quotProj e') hπ hker ht hX ht2 h)
  have hα2' : orderOf (quotAct (quotProj e') hπ hker ht) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα2' hαout
  let ρ : ↥K →* P := (quotProj e').comp (Subgroup.inclusion hKX)
  have hKcenter : Subgroup.center ↥K = ⊥ := by
    have hf := l2pFacts ↥K (Or.inr hL32)
    exact center_eq_bot_of_simple_nonabelian hf.simple hf.nonabelian
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hz : Subgroup.inclusion hKX k ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hk
    have hzk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k'
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hKX k'))
    rw [hKcenter] at hzk
    exact Subgroup.mem_bot.mp hzk
  have hKbcard : Nat.card ρ.range = 168 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    rw [← h]
    exact card_of_psl_three_two hL32
  have hKbF : ρ.range ≤ fixSub (quotAct (quotProj e') hπ hker ht) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixSub]
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e') hπ hker ht _ _ hy
  have hFcard : Nat.card (fixSub (quotAct (quotProj e') hπ hker ht)) = 336 := by
    rw [hg]
    exact card_fixSub_conj_beta g
  have hF' : ⁅fixSub (quotAct (quotProj e') hπ hker ht), fixSub (quotAct (quotProj e') hπ hker ht)⁆ =
      fixD.map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact commutator_fixSub_conj_beta g
  have hKbeq : ρ.range = fixD.map (MulAut.conj g).toMonoidHom := by
    have hidx : (ρ.range.subgroupOf (fixSub (quotAct (quotProj e') hπ hker ht))).index = 2 := by
      have h := (ρ.range.subgroupOf (fixSub (quotAct (quotProj e') hπ hker ht))).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbF).toEquiv, hKbcard, hFcard] at h
      omega
    rw [← hF']
    refine (Subgroup.eq_of_le_of_card_ge (commutator_le_of_index_two hidx) ?_).symm
    exact le_of_eq (by rw [hF', card_fixD_map_conj, hKbcard])
  have hCKb : Subgroup.centralizer (ρ.range : Set P) = ⊥ := by
    rw [hKbeq, eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    have hqD : g⁻¹ * q * g ∈ Subgroup.centralizer (fixD : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := Subgroup.mem_centralizer_iff.1 hq (g * d * g⁻¹) ⟨d, hd, rfl⟩
      calc d * (g⁻¹ * q * g) = g⁻¹ * ((g * d * g⁻¹) * q) * g := by group
        _ = g⁻¹ * (q * (g * d * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * q * g) * d := by group
    rw [centralizer_fixD_P, Subgroup.mem_bot] at hqD
    calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
      _ = 1 := by rw [hqD]; group
  have hBcard : Nat.card (actHom (quotProj e') hπ hker Y hYn).range ≤ 2 := by
    refine card_le_two_of_centralizer_trivial (le_of_eq card_outer_P) ρ.range hCKb _ ?_
    rintro _ ⟨y, rfl⟩ _ ⟨k, rfl⟩
    have hk : ((Subgroup.inclusion hKX k : X) : G) * (y : G) =
        (y : G) * ((Subgroup.inclusion hKX k : X) : G) :=
      Subgroup.mem_centralizer_iff.mp (hYc y.2) (k : G) k.2
    exact actHom_fix (quotProj e') hπ hker Y hYn hk
  rw [relIndex_eq_card_range (quotProj e') hπ hker Y hYn hX]
  exact hBcard

end CFSG.QuasithinUnique.Id2519.Tab
