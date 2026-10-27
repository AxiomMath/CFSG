module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Sect
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Base
public import CFSG.ClassicalInvolution.Q3.Q3T8L278A
public import CFSG.ClassicalInvolution.Q3.Q3T8L278B
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec
public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarNbr
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRDef
public import CFSG.ClassicalInvolution.Q3.Q3T8N01
public import CFSG.ClassicalInvolution.Q3.Q3T8N02
public import CFSG.ClassicalInvolution.Q3.Q3T8N05
public import CFSG.ClassicalInvolution.Q3.Q3T8NDef
public import CFSG.ClassicalInvolution.Asc77.AscT8V8
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
public import CFSG.ClassicalInvolution.Asc77.AscT8T4
public import CFSG.ClassicalInvolution.Asc77.AscT8T5
public import CFSG.ClassicalInvolution.Asc77.AscT8T6
public import CFSG.ClassicalInvolution.Asc77.AscT8T10
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B
public import CFSG.ClassicalInvolution.Q3.Q3T7M04
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A02
public import CFSG.ClassicalInvolution.Q3.Q3T8E274A
import CFSG.ClassicalInvolution.Asc77.AscT8T4Eng
import CFSG.ClassicalInvolution.Asc77.AscT8T6Eng
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFinal2
public import CFSG.ClassicalInvolution.Q3.Q3PStage

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Stand
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K L : Subgroup G}

theorem AscStand.ofMember (h : AscStand Ω K) (hL : L ∈ Ω) : AscStand Ω L where
  modU := h.modU
  hyp := h.hyp
  cls := h.cls
  rank := h.rank
  notFour := h.notFour
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := hL
  trans := by
    obtain ⟨g₀, hg₀⟩ := h.trans L hL
    intro J hJ
    obtain ⟨g, hg⟩ := h.trans J hJ
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [conjSub_mul, ← hg₀, conjSub_inv_conjSub, hg]
  gen := h.gen
end Stand
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
section Reps40
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem sylow_le_layerJoin (hs : Std8 Ω K J S R T W z t) {M P : Subgroup G}
    (hM : T8.XMem Ω (z * t) M) (hP : IsSylow2In P M) (hPa : P ≤ T8.cenZ (z * t)) :
    P ≤ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  intro u hu
  exact Q3NL.exactCore3_le_exactLayer3 (hM.mem_tqMembers3 hΩ hx)
    ((Layer.isSylow2In_exactCore3_of_le_cenZ hP hPa).1 hu)

theorem R_le_layerJoin (hs : Std8 Ω K J S R T W z t) : R ≤ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hRa : R ≤ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact T8.le_centralizer_mul hs
  exact sylow_le_layerJoin hs (Layer.xMem_zt3 hs)
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hs.hR.1 hs.hR.2.1)
        hRa

theorem T_le_layerJoin (hs : Std8 Ω K J S R T W z t) : T ≤ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  exact sylow_le_layerJoin hs (xMem_J hs)
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1)
        (T_le_cenZ hs)

theorem xMem_rep (hs : Std8 Ω K J S R T W z t) (ρ : Rep Ω W) (hK : ρ.K ≠ K) (hJ : ρ.K ≠ J)
    (hnK : ρ.K ∉ omegaNbr Ω K) (hnJ : ρ.K ∉ omegaNbr Ω J) {v : G}
    (hv : IsUniqueInvolution ρ.K v) :
    T8.XMem Ω (z * t) ρ.K ∧ ρ.R ≤ T8.cenZ (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hnK' : K ∉ omegaNbr Ω ρ.K := fun h =>
    hnK (Q3CL.T3.omegaNbr_symm (l6_2) hΩ ρ.hK hs.stand.mem h)
  have hnJ' : J ∉ omegaNbr Ω ρ.K := fun h =>
    hnJ (Q3CL.T3.omegaNbr_symm (l6_2) hΩ ρ.hK hs.hJ.1 h)
  have h1 : ρ.r * z * ρ.r⁻¹ = v * z := c.conj_involution ρ (T8.stdRepK hs) hK hnK' hv hs.hz
  have h2 : ρ.r * t * ρ.r⁻¹ = v * t := c.conj_involution ρ (T8.stdRepJ hs) hJ hnJ' hv hs.ht
  have hvW : v ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hv).2
  have hzW := z_mem_W hs
  have htW := t_mem_W hs
  have hvz : v * z = z * v := c.comm_W v hvW z hzW
  have hconj : ρ.r * (z * t) * ρ.r⁻¹ = z * t := by
    calc ρ.r * (z * t) * ρ.r⁻¹ = (ρ.r * z * ρ.r⁻¹) * (ρ.r * t * ρ.r⁻¹) := by group
      _ = (v * z) * (v * t) := by rw [h1, h2]
      _ = v * (z * v) * t := by group
      _ = v * (v * z) * t := by rw [hvz]
      _ = (v * v) * (z * t) := by group
      _ = z * t := by rw [hv.sq, one_mul]
  have hra : ρ.r * (z * t) = (z * t) * ρ.r := by
    calc ρ.r * (z * t) = (ρ.r * (z * t) * ρ.r⁻¹) * ρ.r := by group
      _ = (z * t) * ρ.r := by rw [hconj]
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcR : ∀ x ∈ ρ.R, x * (z * t) = (z * t) * x := centralizes_of_comm_r c ρ haW hra
  have hav : (z * t) * v = v * (z * t) := c.comm_W _ haW v hvW
  refine ⟨⟨ρ.hK, ?_, ρ.R, ρ.hRK, fun r hr => hcR r hr⟩, fun r hr => T8.mem_cenZ_iff.mpr (hcR r hr)⟩
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant ρ.hK (hnt _ ρ.hK) hv
    (Subgroup.mem_centralizer_singleton_iff.mpr hav)
end Reps40
section RepsBig
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem rep_K_eq [IsSimpleGroup G] (hE : E4SecNoRoot3)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)))
    (ρ : Rep Ω W) : ρ.K = K ∨ ρ.K = J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hρK, hρJ⟩ := hcon
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨v, hv⟩ := hΩ.exists_uniqueInvolution ρ.hK
  have hKJ : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
  by_cases h1 : ρ.K ∈ omegaNbr Ω K <;> by_cases h2 : ρ.K ∈ omegaNbr Ω J
  ·
    have hρ1 : K ∈ omegaNbr Ω ρ.K := Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem ρ.hK h1
    have hρ2 : J ∈ omegaNbr Ω ρ.K := Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.hJ.1 ρ.hK h2
    have hKJne : K ≠ J := hs.hJ.2.1.symm
    refine hdisc (T8.dstarConnected_layerFam3_of_reps hs.stand (T8.partIHyp_of_std8 hs) hs.hW.1 hnt
      ![T8.stdRepK hs, T8.stdRepJ hs, ρ] ![z, t, v] ?_ ?_ ?_ (Layer.zt_not_central3 hs))
    · intro i
      fin_cases i
      · exact hs.hz
      · exact hs.ht
      · exact hv
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hKJne
      · exact hρK.symm
      · exact hKJne.symm
      · exact absurd rfl hij
      · exact hρJ.symm
      · exact hρK
      · exact hρJ
      · exact absurd rfl hij
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hs.hJ
      · exact h1
      · exact hKJ
      · exact absurd rfl hij
      · exact h2
      · exact hρ1
      · exact hρ2
      · exact absurd rfl hij
  ·
    obtain ⟨g, hg, -, hgg⟩ := exists_sq_root c (T8.stdRepJ hs) hs.ht
    obtain ⟨y, hyW, hyy, hyJ, hyK⟩ := exists_y_left c (T8.stdRepJ hs) (T8.stdRepK hs) ρ
      hs.hJ hρJ.symm h2 h1 hs.ht hv hg hgg
    exact no_root_t hE hs hdisc hyW hyy hyK hyJ
  ·
    obtain ⟨g, hg, -, hgg⟩ := exists_sq_root c (T8.stdRepK hs) hs.hz
    obtain ⟨y, hyW, hyy, hyK, hyJ⟩ := exists_y_left c (T8.stdRepK hs) (T8.stdRepJ hs) ρ
      hKJ hρK.symm h1 h2 hs.hz hv hg hgg
    exact no_root_z hE hs hdisc hyW hyy hyK hyJ
  ·
    obtain ⟨hX, hRa⟩ := xMem_rep hs ρ hρK hρJ h1 h2 hv
    obtain ⟨g, hg, hgR, hgg⟩ := exists_sq_root c (T8.stdRepK hs) hs.hz
    obtain ⟨h, hh, hhR, hhh⟩ := exists_sq_root c (T8.stdRepJ hs) hs.ht
    obtain ⟨y, hyW, hy, hyy, hyK, hyJ⟩ := exists_y_both c (T8.stdRepK hs) (T8.stdRepJ hs) ρ
      hs.hJ hKJ hρK.symm hρJ.symm h1 h2 hs.hz hs.ht hv hg hgg hh hhh
    have h8 := hΩ.eight_le_of_mem_RSet ρ.hR.1
    have hvR : v ∈ ρ.R := T3.mem_of_isPGroup hv ρ.hRK.1 ρ.hRK.2.1 (by omega)
    have hyY : y ∈ Q3NL.exactLayer3 Ω (z * t) := by
      rw [hy]
      exact (Q3NL.exactLayer3 Ω (z * t)).mul_mem ((Q3NL.exactLayer3 Ω (z * t)).mul_mem
        (sylow_le_layerJoin hs hX ρ.hRK hRa hvR)
        ((Q3NL.exactLayer3 Ω (z * t)).inv_mem (R_le_layerJoin hs hgR)))
        ((Q3NL.exactLayer3 Ω (z * t)).inv_mem (T_le_layerJoin hs hhR))
    exact no_root_zt hE hs hdisc hyW hyY hyy hyK hyJ

theorem c27_Ysmall_of_e4sec (hE : E4SecNoRoot3) : C27_Ysmall3 := by
  intro G _ _ _ Ω K J S R T W z t hs _hD _hE4 hnab hdisc
  exfalso
  obtain ⟨d, hd, e, he, hde⟩ := T8.exists_noncomm_of_not_abelian hnab
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hKJ : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
  have key : ∀ ρ σ : Rep Ω W, (ρ.K = K ∨ ρ.K = J) → (σ.K = K ∨ σ.K = J) →
      T8.repElt ρ * T8.repElt σ = T8.repElt σ * T8.repElt ρ := by
    intro ρ σ hρ hσ
    by_cases h : ρ.K = σ.K
    · rw [(T8.repElt_eq_iff c ρ σ).mpr h]
    · refine (T8.repElt_commute_iff c ρ σ h).mpr ?_
      rcases hρ with h1 | h1 <;> rcases hσ with h2 | h2
      · exact absurd (h1.trans h2.symm) h
      · rw [h1, h2]
        exact hs.hJ
      · rw [h1, h2]
        exact hKJ
      · exact absurd (h1.trans h2.symm) h
  obtain ⟨ρ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := T8.exists_rep_of_mem_muDelta he
  exact hde (key ρ σ (rep_K_eq hE hs hdisc ρ) (rep_K_eq hE hs hdisc σ))
end RepsBig
end T8V
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Members
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G} {α₀ : Subgroup G}
end Members
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreOf_layerJoin_le_oddCoreOf_centralizer (hΩ : HypOmegaMod Ω) (a : G) :
    oddCoreOf (Q3NL.exactLayer3 Ω a) ≤ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
  have hYC : Q3NL.exactLayer3 Ω a ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact Layer.exactLayer3_le_cenZ Ω a
  intro x hx
  exact T8.oddCoreOf_le_oddCoreOf_of_normalized hYC
    (fun c hc => Layer.exactLayer3_conjSub_eq hΩ.conjInvariant
      (by rw [T8.cenZ_eq_centralizer]; exact hc)) hx
end Layer
end T8T
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Lift
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_mul_mem_sigmaNorm_of_centralizer (hs : Std8 Ω K J S R T W z t)
    (hconn : T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) (hcomp : dComp Ω K = dstarComp Ω K)
    {c : G} (hc : c ∈ Subgroup.centralizer ({z * t} : Set G)) :
    ∃ ν ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)), ν * c ∈ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hcz : c ∈ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact hc
  have hKc : T8.XMem Ω (z * t) (conjSub c K) := hKx.conj3 hΩ.conjInvariant hcz
  obtain ⟨ν, hν, hνK⟩ := Layer.exists_oddCore_conj_mem_dstarComp3 hL hKt hconn
    (hKc.mem_tqMembers3 hΩ hx)
  refine ⟨ν, hν, ?_⟩
  rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hs.stand.mem, conjSub_mul, hcomp]
  exact hνK
end Lift
section Const

@[expose] def C27_AlphaConst : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω →
      (∃ W ∈ WSet Ω, (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) ∧
        ¬ MuIsoE4 Ω W) →
      ∀ z : G, IsUniqueInvolution K z → ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
        ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set G))
end Const
section Sigma
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem alphaOf_eq_of_mem_dComp [IsSimpleGroup G] (hA : C27_AlphaConst)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hμ : ∃ W' ∈ WSet Ω, (∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x) ∧
      ¬ MuIsoE4 Ω W') {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y → IsUniqueInvolution L' y' →
      alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact CFSG.ClassicalInvolution.Asc77.T8T.alphaOf_eq_of_mem_dCompE
    (fun hA' hB' h => Q3CL.T3.omegaNbr_symm (l6_2) hΩ hA' hB' h)
    (fun hA' => hΩ.exists_uniqueInvolution hA')
    (fun c hcΩ z' hz' J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2 =>
      hA G Ω c (hs.stand.ofMember hcΩ) (hnt c hcΩ) hdisc hμ z' hz' J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2)
    hs.stand.mem hs.hz hs.hJ hs.ht hL
end Sigma
end T8T
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Tri

@[expose] def Hyp51Tri : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (M : Fin 3 → Subgroup G) (x : Fin 3 → G) (R : Fin 3 → Subgroup G),
    AscStand Ω (M 0) → (∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) → TriFrame Ω M x R →
      x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G) →
        Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set G))
end Tri
section Transfer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Transfer
section Nbr
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem centralizer_le_normalizer_alpha_of_nbr [IsSimpleGroup G]
    (h2 : C27_2) (hA : C27_AlphaConst) (hH : Hyp51Tri)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  obtain ⟨e⟩ := l7_5_2_proved G Ω hs.stand.modU W hs.hW.1 W' hstd.hW.1
  obtain ⟨hab', hE4'⟩ := muAbelian_notE4_transfer e hab hE4
  have hx : z * s * (z * s) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hM hs'
  have hKx : T8.XMem Ω (z * s) K := Layer.xMem_zt3 hstd
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * s) := hKx.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hstd.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * s) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hcomp := h2 G Ω K M S' R' T' W' z s hstd hdisc
  have hconn := T8.dstarConnected_layerFam3_of_abelian hstd hE4' hab'
  by_cases hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω M → ∀ z' : G,
      IsUniqueInvolution K' z' → z' ≠ z * s
  · obtain ⟨K'', R'', z'', hF, hind⟩ := exists_triFrame_of_std8 hstd hE4' hab' hE8
    have hHyp : Hyp51 (Subgroup.closure ({z, s, z''} : Set G)) :=
      hH G Ω ![K, M, K''] ![z, s, z''] ![R', T', R''] hstd.stand hnt hF hind
    have hc01 : z * s = s * z := hF.comm hΩ 0 1
    have hc02 : z * z'' = z'' * z := hF.comm hΩ 0 2
    have hc12 : s * z'' = z'' * s := hF.comm hΩ 1 2
    have hz2 : z * z = 1 := hF.sq 0
    have hs2 : s * s = 1 := hF.sq 1
    have hz''2 : z'' * z'' = 1 := hF.sq 2
    have hz1 : z ≠ 1 := hF.ne_one 0
    have hs1 : s ≠ 1 := hF.ne_one 1
    have hz''1 : z'' ≠ 1 := hF.ne_one 2
    have hzs : z ≠ s := hF.x_ne hnt (i := 0) (j := 1) (by decide)
    have hB : IsElemAbelian 2 (Subgroup.closure ({z, s, z''} : Set G)) :=
      isElemAbelian_closure_three hz2 hs2 hz''2 hc01 hc02 hc12
    have hB8 : Nat.card ↥(Subgroup.closure ({z, s, z''} : Set G)) = 8 :=
      natCard_closure_three hz2 hs2 hz''2 hc01 hc02 hc12 hz1 hs1 hzs hz''1 hind
    have hDB : Subgroup.closure ({s, z} : Set G) ≤ Subgroup.closure ({z, s, z''} : Set G) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hs2 hz2 hs1 hz1 hzs.symm hc01.symm
    have h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, s, z''} : Set G) →
        IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({s, z} : Set G)) :=
      (lemma54_odd_and_eq hHyp hDB hD).2
    have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) :=
      hA G Ω K hs.stand hs.noTwins hdisc ⟨W, hs.hW.1, hab, hE4⟩ z hs.hz M hM J hs.hJ s t hs'
        hs.ht
    intro c hc
    obtain ⟨ν, hν, hνc⟩ := exists_mul_mem_sigmaNorm_of_centralizer hstd hconn hcomp hc
    have hzsB : z * s ∈ Subgroup.closure ({z, s, z''} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hν' : ν ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({s, z} : Set G)) : Set G) :=
      oddCoreOf_centralizer_le_normalizer hB hB8 hzsB h3
        (oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ (z * s) hν)
    rw [hα] at hν'
    have hc' : c = ν⁻¹ * (ν * c) := by group
    rw [hc']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)
  · push Not at hE8
    obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
    have hY : oddCoreOf (Q3NL.exactLayer3 Ω (z * s)) ≤ sigmaNorm Ω K :=
      T8.oddCoreOf_layerJoin_le_of_zt hstd hK' (hzt ▸ hz')
    have hY1 : Q3NL.exactLayer3 Ω (z * s) ≤ sigmaNorm Ω K :=
      Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt hcomp hY hconn
    exact (Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hstd hY1).trans hN
end Nbr
end T8T
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Sigma
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem sigmaNorm_le_normalizer_alpha [IsSimpleGroup G] (hA : C27_AlphaConst)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    sigmaNorm Ω K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  exact CFSG.ClassicalInvolution.Asc77.T8T.sigmaNorm_le_normalizer_alphaE hΩ.conjInvariant hs.stand.mem hs.hJ hs.hz hs.ht
    (fun hL => alphaOf_eq_of_mem_dComp hA hs hdisc ⟨W, hs.hW.1, hab, hE4⟩ hL)
end Sigma
end T8T
section Main
end Main
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8T
open CFSG.ClassicalInvolution.Asc77.T8T
section Residual

@[expose] def C27_AlphaNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          (∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
            z' ≠ z * t) →
            T8.H274 Ω K z ≤
              Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G)
end Residual
end T8T
section Main

theorem c27_alphaNorm_of_alphaConst (h2 : C27_2) (hH : T8T.Hyp51Tri)
    (hA : T8T.C27_AlphaConst) : T8T.C27_AlphaNorm := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4 hab _
  have hN := T8T.sigmaNorm_le_normalizer_alpha hA hs hdisc hab hE4
  exact sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
    T8T.centralizer_le_normalizer_alpha_of_nbr h2 hA hH hs hdisc hab hE4 hN hM hs')

theorem c27_Oab_of_alphaNorm (h2 : C27_2) (h4 : C27_4) (hH : T8T.Hyp51Tri)
    (hN : T8T.C27_AlphaNorm) : C27_Oab3 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4 hab hE8
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  
  obtain ⟨K', R', z', hF, hind⟩ := T8T.exists_triFrame_of_std8 hs hE4 hab hE8
  have hHyp : Hyp51 (Subgroup.closure ({z, t, z'} : Set G)) :=
    hH G Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] hs.stand hnt hF hind
  have hzt : z * t = t * z := hF.comm hΩ 0 1
  have hz2 : z * z = 1 := hF.sq 0
  have ht2 : t * t = 1 := hF.sq 1
  have hz1 : z ≠ 1 := hF.ne_one 0
  have ht1 : t ≠ 1 := hF.ne_one 1
  have hzt' : t ≠ z := (hF.x_ne hnt (i := 0) (j := 1) (by decide)).symm
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, z'} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt' hzt.symm
  obtain ⟨hodd, -⟩ := lemma54_odd_and_eq hHyp hDB hD
  have hH274 := hN G Ω K J S R T W z t hs hdisc hE4 hab hE8
  have hcomp := h2 G Ω K J S R T W z t hs hdisc
  have htop : T8.H274 Ω K z = ⊤ := h4 G Ω K J S R T W z t hs hdisc
  rw [htop, top_le_iff] at hH274
  
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH274
  have hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
      have hdvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact T8.oddCoreOf_layerJoin_le_of_alpha hs hα
end Main
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
