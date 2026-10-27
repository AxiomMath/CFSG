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
public import CFSG.ClassicalInvolution.Asc77.AscT8Y6
public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.ClassicalInvolution.Asc77.AscT8V7
public import CFSG.ClassicalInvolution.Asc77.AscT8T2
import CFSG.ClassicalInvolution.Asc77.AscT8V7Eng
import CFSG.ClassicalInvolution.Asc77.AscT8Y6Eng
import CFSG.ClassicalInvolution.Asc77.AscT8T1Eng
import CFSG.ClassicalInvolution.Asc77.AscT8T2Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8T.TriFrame :=
  @CFSG.ClassicalInvolution.Asc77.T8T.TriFrame

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Zt
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem oddCoreOf_layerJoin_le_of_zt (hs : Std8 Ω K J S R T W z t) {K' : Subgroup G}
    (hK' : K' ∈ omegaNbr Ω K) (hz' : IsUniqueInvolution K' (z * t)) :
    oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have huv : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hne : z ≠ t := ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hgu : Subgroup.centralizer ({z} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz).trans
      (normalizer_le_sigmaNorm hΩ.conjInvariant hK)
  have hgv : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.hJ.1 (hnt _ hs.hJ.1) hs.ht).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK (mem_dComp_of_mem_omegaNbr hs.hJ))
  have hguv : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK'.1 (hnt _ hK'.1) hz').trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK (mem_dComp_of_mem_omegaNbr hK'))
  refine Layer.oddCoreOf_exactLayer3_le_of_good_pair hΩ.conjInvariant hs.hz.sq hs.ht.sq huv
    hs.hz.ne_one hs.ht.ne_one hne ?_ ?_ hgu hgv hguv
  · rw [mem_cenZ_iff]
    calc z * (z * t) = z * (t * z) := by rw [huv]
      _ = (z * t) * z := by group
  · rw [mem_cenZ_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [huv]

theorem exists_good_pair_of_nonabelian (hs : Std8 Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ (ρ σ : Rep Ω W) (u v : G), repElt ρ * repElt σ ≠ repElt σ * repElt ρ ∧
      IsUniqueInvolution ρ.K u ∧ IsUniqueInvolution σ.K v ∧ u * v = v * u ∧ u ≠ v ∧
      u ∈ cenZ (z * t) ∧ v ∈ cenZ (z * t) ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({v} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({u * v} : Set G) ≤ sigmaNorm Ω K := by
  have hP := partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact CFSG.ClassicalInvolution.Asc77.T8.exists_good_pair_of_nonabelianE hΩ.conjInvariant
    (fun hM => hΩ.exists_uniqueInvolution hM)
    (fun hM hR hRM hx => Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hM hR hRM hx) hc.comm_W
    (repElt_eq_iff hc) (repElt_commute_iff hc) (repElt_omegaStar hc)
    (fun ρ => mem_dComp_of_rep hs hcomp ρ) hK hnt hs.stand.aEmpty
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hK (stdRepK hs).hR (stdRepK hs).hRK hs.hz).2
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hs.hJ.1 (stdRepJ hs).hR (stdRepJ hs).hRK
        hs.ht).2 hab
end Zt
end T8
section Residual
end Residual
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
section Frame
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
variable {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}
section Comm
variable [Finite G]

theorem TriFrame.comm (hF : TriFrame Ω M x R) (hΩ : HypOmegaMod Ω)
    (i j : Fin 3) : x i * x j = x j * x i := by
  by_cases hij : i = j
  · rw [hij]
  · exact Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ (hF.inv i) (hF.nbr i j hij) (hF.inv j)
end Comm
end Frame
section ThreeGroup
variable {G : Type} [Group G]
variable [Finite G]
end ThreeGroup
section Extract
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_triFrame_of_std8 (hs : Std8 Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
      z' ≠ z * t) :
    ∃ (K' R' : Subgroup G) (z' : G), TriFrame Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] ∧
      z' ∉ Subgroup.closure ({z, t} : Set G) := by
  have hP := T8.partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨K', R', z', hmem, hinv, hnbr, hsyl, hcent, hz'⟩ :=
    CFSG.ClassicalInvolution.Asc77.T8T.exists_triFrame_of_std8E hnt (fun hM => hΩ.exists_uniqueInvolution hM) hs.hz hs.ht hs.hJ
      (T8.stdRepK hs) (T8.stdRepJ hs) rfl rfl rfl rfl (T8.exists_third_of_abelian hs hE4 hab)
      (T8.repElt_commute_iff hc) (T8.rep_le_centralizer hc)
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht) hab hE8
  exact ⟨K', R', z', ⟨hmem, hinv, hnbr, hsyl, hcent⟩, hz'⟩
end Extract
end T8T
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
section Roots
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem comm_mk_mem {a : G} {M : Subgroup G} (hM : M ∈ Q3NL.tqMembers3 Ω a)
    (e : ↥(Q3NL.exactLayer3 Ω a)) (hy : (e : G) ∈ T8.cenZ a)
    (hyN : (e : G) ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅(e : G), k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ Layer.layerImg3 Ω a M,
      ⁅(QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) e :
        Q3T7.layerQuot3 Ω a), kb⁆ ∈ oddCoreOf (Layer.layerImg3 Ω a M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hkL : (k' : G) ∈ Q3NL.exactCore3 a M := Subgroup.mem_subgroupOf.mp hk'
  have h3 := T8V.mk_mem_oddCoreOf_layerImg hM ⁅e, k'⁆
    (by
      have : ((⁅e, k'⁆ : ↥(Q3NL.exactLayer3 Ω a)) : G) = ⁅(e : G), (k' : G)⁆ := by
        simp [commutatorElement_def]
      rw [this]
      exact T8V.comm_mem_oddCoreOf_layerRes hy hyN hcomm hkL)
  rwa [map_commutatorElement] at h3

theorem layerMk_congr {x g h : G} (hg : g ∈ Q3NL.exactLayer3 Ω x) (hh : h ∈ Q3NL.exactLayer3 Ω x)
    (e : g = h) : layerMk x g hg = layerMk x h hh := by
  subst e
  rfl

theorem z_mem_W (hs : Std8 Ω K J S R T W z t) : z ∈ W := by
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW (T8.stdRepK hs).hK (T8.stdRepK hs).hR
    (T8.stdRepK hs).hRK hs.hz).2

theorem t_mem_W (hs : Std8 Ω K J S R T W z t) : t ∈ W := by
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW (T8.stdRepJ hs).hK (T8.stdRepJ hs).hR
    (T8.stdRepJ hs).hRK hs.ht).2

theorem y_data (hs : Std8 Ω K J S R T W z t) {y : G} (hyW : y ∈ W) (hy4 : y ^ 2 ^ 2 = 1)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) :
    y ∈ T8.cenZ (z * t) ∧ y ∈ Subgroup.normalizer (K : Set G) ∧
      y ∈ Subgroup.normalizer (J : Set G) ∧ (∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K) ∧
      (∀ k ∈ J, ⁅y, k⁆ ∈ oddCoreOf J) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact CFSG.ClassicalInvolution.Asc77.T8V.y_dataE hΩ.conjInvariant c.comm_W hs.stand.mem hs.hJ.1 hs.hz hs.ht hs.noTwins hnt (z_mem_W hs)
    (t_mem_W hs)
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hs.hR.1 hs.hR.2.1)
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1)
    (fun hM hR hy hym hyR' => comm_mem_oddCoreOf_of_pow hΩ hM hR hy hym hyR') hyW hy4 hyR hyT

theorem no_root_sq [IsSimpleGroup G] (hE : E4SecNoRoot3) (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) {y u : G}
    (hu : u ∈ Q3NL.exactLayer3 Ω (z * t)) (hyW : y ∈ W) (hyy : y * y = u) (hy4 : y ^ 2 ^ 2 = 1)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x)
    (hconj : MulAut.conj (layerMk (z * t) u hu) =
      MulAut.conj (layerMk (z * t) z (z_mem_layerJoin hs))) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := (Layer.xMem_zt3 hs).mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := (xMem_J hs).mem_tqMembers3 hΩ hx
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ := y_data hs hyW hy4 hyR hyT
  have hyN : y ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hycen)
  refine (e4_layer hE hs hdisc).1 (s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨y, hyN⟩)
    (s26Act_mul_inv_mem hΩ hKt hycen hyK hcK)
    (s26Act_mul_inv_mem hΩ hJt hycen hyJ hcJ) ?_
  rw [← map_mul]
  have e : (⟨y, hyN⟩ * ⟨y, hyN⟩ :
      ↥(Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G))) =
      ⟨u, Subgroup.le_normalizer hu⟩ := Subtype.ext hyy
  rw [e, s26Act_eq_conj (Q3NL.exactLayer3 Ω (z * t)) ⟨u, hu⟩]
  exact hconj

theorem no_root_z [IsSimpleGroup G] (hE : E4SecNoRoot3) (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyy : y * y = z) (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False :=
  no_root_sq hE hs hdisc (z_mem_layerJoin hs) hyW hyy
    (by rw [pow_two_pow_two_eq, hyy, hs.hz.sq]) hyR hyT rfl

theorem no_root_t [IsSimpleGroup G] (hE : E4SecNoRoot3) (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyy : y * y = t) (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False :=
  no_root_sq hE hs hdisc (t_mem_layerJoin hs) hyW hyy
    (by rw [pow_two_pow_two_eq, hyy, hs.ht.sq]) hyR hyT
    (conj_eq_of_central_mul (layerMk_z_sq hs) (layerMk_central hs))

theorem no_root_zt [IsSimpleGroup G] (hE : E4SecNoRoot3) (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyY : y ∈ Q3NL.exactLayer3 Ω (z * t)) (hyy : y * y = z * t)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := (Layer.xMem_zt3 hs).mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := (xMem_J hs).mem_tqMembers3 hΩ hx
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ :=
    y_data hs hyW (by rw [pow_two_pow_two_eq, hyy, hx]) hyR hyT
  refine (e4_layer hE hs hdisc).2 (layerMk (z * t) y hyY)
    (comm_mk_mem hKt ⟨y, hyY⟩ hycen hyK hcK)
    (comm_mk_mem hJt ⟨y, hyY⟩ hycen hyJ hcJ) ?_
  rw [layerMk_mul, layerMk_mul]
  exact layerMk_congr _ _ hyy
end Roots
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
section Consequences
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}

theorem TriFrame.xMem (hF : TriFrame Ω M x R) (hΩ : HypOmegaMod Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (i j : Fin 3) : T8.XMem Ω (x j) (M i) := by
  refine ⟨hF.mem i, ?_, R i, hF.syl i, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i) (hnt _ (hF.mem i))
      (hF.inv i) (Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm hΩ j i))
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hF.cent i j hr)

theorem TriFrame.le_trivialOnQuot (hF : TriFrame Ω M x R) (hΩ : HypOmegaMod Ω) (hnt : ∀ K ∈ Ω, ∀ K'
    ∈ twinSet Ω K, K' = K) (i : Fin 3) :
    Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤ trivialOnQuot (M i) := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.le_trivialOnQuotE i fun j =>
    (hF.xMem hΩ hnt i j).trivialOnQuot3 hΩ (hF.sq j)
end Consequences
end T8T
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
