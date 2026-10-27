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
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8V4
public import CFSG.ClassicalInvolution.Asc77.AscT8W7
public import CFSG.ClassicalInvolution.Asc77.AscT8V5
public import CFSG.ClassicalInvolution.Asc77.AscT8V6
public import CFSG.ClassicalInvolution.Asc77.AscT8W8
public import CFSG.ClassicalInvolution.Asc77.AscT8W9
public import CFSG.ClassicalInvolution.Asc77.AscT8W10
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B
public import CFSG.ClassicalInvolution.Q3.Q3T7M01
import CFSG.ClassicalInvolution.Asc77.AscT8V5Eng
import CFSG.ClassicalInvolution.Asc77.AscT8W8Eng
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.SmallCases.NDBH5
public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8V
open CFSG.ClassicalInvolution.Asc77.T8V
section Img
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_oddCoreOf_of_normal_odd' {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M :=
  CFSG.ClassicalInvolution.Asc77.T8V.le_oddCoreOf_of_normal_odd' hNM hn hodd

theorem comm_mem_oddCoreOf_layerRes {a y : G} {M : Subgroup G} (hy : y ∈ T8.cenZ a)
    (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) {k : G} (hk : k ∈ Q3NL.exactCore3 a M) :
    ⁅y, k⁆ ∈ oddCoreOf (Q3NL.exactCore3 a M) := by
  have hLM : Q3NL.exactCore3 a M ≤ M := Q3NL.exactCore3_le_left a M
  have hyL : y ∈ Subgroup.normalizer (Q3NL.exactCore3 a M : Set G) :=
    Layer.mem_normalizer_exactCore3 hyN hy
  set N : Subgroup G := oddCoreOf M ⊓ Q3NL.exactCore3 a M with hN
  have hNL : N ≤ Q3NL.exactCore3 a M := inf_le_right
  have hnorm : Q3NL.exactCore3 a M ≤ Subgroup.normalizer (N : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hu' : u ∈ M := hLM hu
    have h1 := mem_normalizer_oddCoreOf hu'
    constructor
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mp hn1, ?_⟩
      exact (Q3NL.exactCore3 a M).mul_mem ((Q3NL.exactCore3 a M).mul_mem hu hn2)
        ((Q3NL.exactCore3 a M).inv_mem hu)
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mpr hn1, ?_⟩
      have := (Q3NL.exactCore3 a M).mul_mem
        ((Q3NL.exactCore3 a M).mul_mem ((Q3NL.exactCore3 a M).inv_mem hu) hn2) hu
      simpa [mul_assoc] using this
  have hodd : Odd (Nat.card N) :=
    (oddCoreOf_odd_natCard M).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hmem : ⁅y, k⁆ ∈ N := by
    refine ⟨hcomm k (hLM hk), ?_⟩
    have h1 : y * k * y⁻¹ ∈ Q3NL.exactCore3 a M :=
      (Subgroup.mem_normalizer_iff.mp hyL k).mp hk
    rw [commutatorElement_def]
    exact (Q3NL.exactCore3 a M).mul_mem h1 ((Q3NL.exactCore3 a M).inv_mem hk)
  exact le_oddCoreOf_of_normal_odd' hNL hnorm hodd hmem

theorem mk_mem_oddCoreOf_layerImg {a : G} {M : Subgroup G} (hM : M ∈ Q3NL.tqMembers3 Ω a)
    (c : ↥(Q3NL.exactLayer3 Ω a)) (hc : (c : G) ∈ oddCoreOf (Q3NL.exactCore3 a M)) :
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) c :
        Q3T7.layerQuot3 Ω a) ∈ oddCoreOf (Layer.layerImg3 Ω a M) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLY : Q3NL.exactCore3 a M ≤ Q3NL.exactLayer3 Ω a := Q3NL.exactCore3_le_exactLayer3 hM
  have h1 : c ∈ oddCoreOf ((Q3NL.exactCore3 a M).subgroupOf (Q3NL.exactLayer3 Ω a)) := by
    rw [oddCoreOf_subgroupOf hLY]
    exact hc
  have h2 := oddCoreOf_map_mk_of_odd (K := (Q3NL.exactCore3 a M).subgroupOf (Q3NL.exactLayer3 Ω a))
    (X := classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) (odd_natCard_inf hodd _)
  unfold Layer.layerImg3
  rw [h2]
  exact Subgroup.mem_map_of_mem _ h1

theorem s26Act_mul_inv_mem (hΩ : HypOmegaMod Ω) {a y : G} {M : Subgroup G}
    (hM : M ∈ Q3NL.tqMembers3 Ω a) (hy : y ∈ T8.cenZ a) (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ Layer.layerImg3 Ω a M,
      s26Act (Q3NL.exactLayer3 Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hy)⟩ kb * kb⁻¹ ∈
          oddCoreOf (Layer.layerImg3 Ω a M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hyY : y ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω a : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hy)
  have hkL : (k' : G) ∈ Q3NL.exactCore3 a M := Subgroup.mem_subgroupOf.mp hk'
  have hyk : y * (k' : G) * y⁻¹ ∈ Q3NL.exactLayer3 Ω a :=
    (Subgroup.mem_normalizer_iff.mp hyY (k' : G)).mp k'.2
  have e := s26Act_mk (Q3NL.exactLayer3 Ω a) ⟨y, hyY⟩ k' ⟨y * (k' : G) * y⁻¹, hyk⟩ rfl
  have hc : ((⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹ : ↥(Q3NL.exactLayer3 Ω a)) : G) =
      ⁅y, (k' : G)⁆ := by
    simp [commutatorElement_def]
  have h3 := mk_mem_oddCoreOf_layerImg hM (⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹)
    (by rw [hc]; exact comm_mem_oddCoreOf_layerRes hy hyN hcomm hkL)
  change s26Act (Q3NL.exactLayer3 Ω a) ⟨y, hyY⟩ (QuotientGroup.mk k') * (QuotientGroup.mk k')⁻¹ ∈ _
  rw [e]
  simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h3
end Img
end T8V
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Good
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem oddCoreOf_layerJoin_le_E4 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨t₁, ht1sq, ht1ne, hne, htt1, hzt1, -, -, -, hC1, hC2, -⟩ :=
    exists_good_involution_E4 hs hdisc hE
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have htx : t ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    have h1 : t * (z * t) = z := by rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have h2 : z * t * t = z := by rw [mul_assoc, hs.ht.sq, mul_one]
    rw [h1, h2])
  have ht1x : t₁ ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    calc t₁ * (z * t) = (t₁ * z) * t := by rw [mul_assoc]
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by rw [mul_assoc]
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by rw [mul_assoc])
  exact Layer.oddCoreOf_exactLayer3_le_of_good_pair hΩ.conjInvariant hs.ht.sq ht1sq htt1
    hs.ht.ne_one ht1ne hne.symm htx ht1x hCt hC1 hC2
end Good
end T8W
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
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem z_mem_layerJoin (hs : Std8 Ω K J S R T W z t) : z ∈ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hK := (Layer.xMem_zt3 hs).mem_tqMembers3 hΩ hx
  have hRK : IsSylow2In R K :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hs.hR.1 hs.hR.2.1
  have hRa : R ≤ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact T8.le_centralizer_mul hs
  have hL := Layer.isSylow2In_exactCore3_of_le_cenZ hRK hRa
  have h8 := hΩ.eight_le_of_mem_RSet hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRK.2.1 (by omega)
  exact Q3NL.exactCore3_le_exactLayer3 hK (hL.1 hzR)

theorem T_le_cenZ (hs : Std8 Ω K J S R T W z t) : T ≤ T8.cenZ (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have c := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hn21 : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
  exact CFSG.ClassicalInvolution.Asc77.T8V.T_le_cenZE
    (T8.rep_le_centralizer c (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz)
    (T8.rep_le_centralizer c (T8.stdRepJ hs) (T8.stdRepJ hs) (Or.inl rfl) hs.ht)

theorem xMem_J (hs : Std8 Ω K J S R T W z t) : T8.XMem Ω (z * t) J := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hc := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  exact CFSG.ClassicalInvolution.Asc77.T8V.xMem_JE hΩ.conjInvariant hnt hs.hJ.1 hs.ht hc
    (Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1)
    (T_le_cenZ hs)

theorem t_mem_layerJoin (hs : Std8 Ω K J S R T W z t) : t ∈ Q3NL.exactLayer3 Ω (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hJ := (xMem_J hs).mem_tqMembers3 hΩ hx
  have hTJ : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hL := Layer.isSylow2In_exactCore3_of_le_cenZ hTJ (T_le_cenZ hs)
  have h8 := hΩ.eight_le_of_mem_RSet hs.hT.1
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTJ.2.1 (by omega)
  exact Q3NL.exactCore3_le_exactLayer3 hJ (hL.1 htT)

@[expose] noncomputable def layerMk (x g : G) (hg : g ∈ Q3NL.exactLayer3 Ω x) : Q3T7.layerQuot3 Ω x
    :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω x)) ⟨g, hg⟩
end Layer
end T8V
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
section LayerMk
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end LayerMk
section E4
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerMk_central (hs : Std8 Ω K J S R T W z t) :
    layerMk (z * t) z (z_mem_layerJoin hs) * layerMk (z * t) t (t_mem_layerJoin hs) ∈
      Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := by
  have hzY := z_mem_layerJoin hs
  have htY := t_mem_layerJoin hs
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hg : (g' : G) ∈ T8.cenZ (z * t) := Layer.exactLayer3_le_cenZ Ω (z * t) g'.2
  have hcz : (g' : G) * (z * t) = (z * t) * g' := T8.mem_cenZ_iff.mp hg
  have hm : layerMk (z * t) z hzY * layerMk (z * t) t htY =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))
        (⟨z, hzY⟩ * ⟨t, htY⟩) := by
    unfold layerMk
    rw [map_mul]
  have hc2 : g' * (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))) =
      (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))) * g' :=
    Subtype.ext (by simpa using hcz)
  rw [hm]
  change QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t))) g' * _ =
    _ * QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t))) g'
  rw [← map_mul, ← map_mul, hc2]
end E4
end T8V
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Lift
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_fixed_lift (hΩ : HypOmegaMod Ω) {a y : G} (hy : y ∈ T8.cenZ a)
    (hy2 : y * y = 1) (u : Q3T7.layerQuot3 Ω a)
    (hu : s26Act (Q3NL.exactLayer3 Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
      (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hy)⟩ u = u) :
    ∃ w : ↥(Q3NL.exactLayer3 Ω a), y * (w : G) * y⁻¹ = w ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) w :
        Q3T7.layerQuot3 Ω a) = u := by
  classical
  have hyY : y ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω a : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hy)
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hyk : y * (w₀ : G) * y⁻¹ ∈ Q3NL.exactLayer3 Ω a :=
    (Subgroup.mem_normalizer_iff.mp hyY (w₀ : G)).mp w₀.2
  have e := s26Act_mk (Q3NL.exactLayer3 Ω a) ⟨y, hyY⟩ w₀ ⟨y * (w₀ : G) * y⁻¹, hyk⟩ rfl
  have h1 : ((⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(Q3NL.exactLayer3 Ω a)) :
      Q3T7.layerQuot3 Ω a) = (w₀ : Q3T7.layerQuot3 Ω a) := e.symm.trans hu
  have h2 : (⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(Q3NL.exactLayer3 Ω a))⁻¹ * w₀ ∈
      classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a) := QuotientGroup.eq.mp h1
  set N : Subgroup G := oddCoreOf (Q3NL.exactLayer3 Ω a) with hN
  have hx : ∀ b ∈ Subgroup.zpowers y, (w₀ : G)⁻¹ * (b * (w₀ : G) * b⁻¹) ∈ N := by
    intro b hb
    rcases mem_zpowers_involution hy2 hb with hb1 | hb1
    · rw [hb1]
      simp
    · rw [hb1]
      have h3 : (y * (w₀ : G) * y⁻¹)⁻¹ * (w₀ : G) ∈ N := by
        refine mem_oddCoreOf_iff.mpr ⟨(Q3NL.exactLayer3 Ω a).mul_mem
          ((Q3NL.exactLayer3 Ω a).inv_mem hyk) w₀.2, ?_⟩
        convert h2 using 1
      have := N.inv_mem h3
      simpa [mul_assoc] using this
  have hAN : ∀ b ∈ Subgroup.zpowers y, ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
    intro b hb n hn
    have hbc : b ∈ T8.cenZ a := (Subgroup.zpowers_le.mpr hy) hb
    have := Layer.mem_normalizer_oddCoreOf_exactLayer3 hΩ.conjInvariant hbc
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow hy2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨n, hnN, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup hA2
    (odd_natCard_oddCoreOf _) hAN hx
  have hnY : n ∈ Q3NL.exactLayer3 Ω a := (mem_oddCoreOf_iff.mp hnN).1
  refine ⟨⟨(w₀ : G) * n, (Q3NL.exactLayer3 Ω a).mul_mem w₀.2 hnY⟩, ?_, ?_⟩
  · exact hfix y (Subgroup.mem_zpowers y)
  · apply QuotientGroup.eq.mpr
    have hn' := (mem_oddCoreOf_iff.mp hnN).2
    have hE : (⟨(w₀ : G) * n, (Q3NL.exactLayer3 Ω a).mul_mem w₀.2 hnY⟩ :
        ↥(Q3NL.exactLayer3 Ω a))⁻¹ * w₀ = (⟨n, hnY⟩ : ↥(Q3NL.exactLayer3 Ω a))⁻¹ := by
      apply Subtype.ext
      simp
    rw [hE]
    exact (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)).inv_mem hn'

@[expose] def layerImage (Ω : Set (Subgroup G)) (a : G) (H : Subgroup G) :
    Subgroup (Q3T7.layerQuot3 Ω a) :=
  (H.subgroupOf (Q3NL.exactLayer3 Ω a)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)))

theorem mem_layerImage_of_fixed (hΩ : HypOmegaMod Ω) {a y : G} {H : Subgroup G}
    (hy : y ∈ T8.cenZ a) (hy2 : y * y = 1) (hCy : Subgroup.centralizer ({y} : Set G) ≤ H)
    (u : Q3T7.layerQuot3 Ω a)
    (hu : s26Act (Q3NL.exactLayer3 Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
      (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hy)⟩ u = u) : u ∈ layerImage Ω a H := by
  exact CFSG.ClassicalInvolution.Asc77.T8W.mem_layerImage_of_fixedE hCy u (exists_fixed_lift hΩ hy hy2 u hu)

theorem layerJoin_le_of_closure {a : G} {H : Subgroup G}
    (hO : oddCoreOf (Q3NL.exactLayer3 Ω a) ≤ H) (S : Set (Q3T7.layerQuot3 Ω a))
    (hS : S ⊆ (layerImage Ω a H : Set (Q3T7.layerQuot3 Ω a)))
    (hgen : Subgroup.closure S = ⊤) : Q3NL.exactLayer3 Ω a ≤ H := by
  exact CFSG.ClassicalInvolution.Asc77.T8W.layerJoin_le_of_closureE hO S hS hgen
end Lift
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Triv
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem oddCoreOf_inf_le_oddCoreOf {L Y : Subgroup G} (hLY : L ≤ Y) :
    oddCoreOf Y ⊓ L ≤ oddCoreOf L :=
  CFSG.ClassicalInvolution.Asc77.T8W.oddCoreOf_inf_le_oddCoreOf hLY

theorem mem_oddCoreOf_layerRes_of_mk_mem {a : G} {M : Subgroup G}
    (hM : M ∈ Q3NL.tqMembers3 Ω a)
    (c : ↥(Q3NL.exactLayer3 Ω a)) (hcM : (c : G) ∈ Q3NL.exactCore3 a M)
    (hc : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) c :
      Q3T7.layerQuot3 Ω a) ∈ oddCoreOf (Layer.layerImg3 Ω a M)) :
    (c : G) ∈ oddCoreOf (Q3NL.exactCore3 a M) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLY : Q3NL.exactCore3 a M ≤ Q3NL.exactLayer3 Ω a := Q3NL.exactCore3_le_exactLayer3 hM
  have h2 := oddCoreOf_map_mk_of_odd (K := (Q3NL.exactCore3 a M).subgroupOf (Q3NL.exactLayer3 Ω a))
    (X := classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a)) (odd_natCard_inf hodd _)
  unfold Layer.layerImg3 at hc
  rw [h2] at hc
  obtain ⟨c', hc', hcc'⟩ := Subgroup.mem_map.mp hc
  rw [oddCoreOf_subgroupOf hLY] at hc'
  have hc'L : (c' : G) ∈ oddCoreOf (Q3NL.exactCore3 a M) := Subgroup.mem_subgroupOf.mp hc'
  have hdiv : c'⁻¹ * c ∈ classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω a) :=
    QuotientGroup.eq.mp hcc'
  have hmem : ((c' : G)⁻¹ * c) ∈ oddCoreOf (Q3NL.exactLayer3 Ω a) ⊓ Q3NL.exactCore3 a M := by
    refine ⟨mem_oddCoreOf_iff.mpr ⟨(Q3NL.exactLayer3 Ω a).mul_mem ((Q3NL.exactLayer3 Ω a).inv_mem
        c'.2)
      c.2, ?_⟩, ?_⟩
    · convert hdiv using 1
    · exact (Q3NL.exactCore3 a M).mul_mem ((Q3NL.exactCore3 a M).inv_mem (mem_oddCoreOf_iff.mp
        hc'L).1)
        hcM
  have h3 := oddCoreOf_inf_le_oddCoreOf hLY hmem
  have : (c : G) = (c' : G) * ((c' : G)⁻¹ * c) := by group
  rw [this]
  exact (oddCoreOf (Q3NL.exactCore3 a M)).mul_mem hc'L h3

theorem not_trivial_on_layerImg_J [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) {t₁ : G} (ht1 : t₁ ∈ T8.cenZ (z * t))
    (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t) (hnJ : conjSub t₁ J = J) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ Ω) (hJ₁X : J₁ ≤ omegaNbrGen Ω K) (hJ₁t : IsUniqueInvolution J₁ t₁) :
    ¬ ∀ kb ∈ Layer.layerImg3 Ω (z * t) J,
      s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, mem_normalizer_iff_conjSub_eq.mpr
        (Layer.exactLayer3_conjSub_eq hs.stand.hyp.conjInvariant ht1)⟩ kb * kb⁻¹ ∈
          oddCoreOf (Layer.layerImg3 Ω (z * t) J) := by
  intro H₀
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hyY : t₁ ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant ht1)
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (Q3NL.exactCore3 (z * t) J : Set G) :=
    Layer.mem_normalizer_exactCore3 hJN ht1
  
  have hstep1 : ∀ k ∈ Q3NL.exactCore3 (z * t) J, ⁅t₁, k⁆ ∈ oddCoreOf (Q3NL.exactCore3 (z * t) J) :=
      by
    intro k hk
    have hkY : k ∈ Q3NL.exactLayer3 Ω (z * t) := Q3NL.exactCore3_le_exactLayer3 hJt hk
    have hyk : t₁ * k * t₁⁻¹ ∈ Q3NL.exactLayer3 Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY k).mp hkY
    have hkb : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))
        (⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))) : Q3T7.layerQuot3 Ω (z * t)) ∈
        Layer.layerImg3 Ω (z * t) J := ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h0 := H₀ _ hkb
    have e := s26Act_mk (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY⟩ ⟨k, hkY⟩ ⟨t₁ * k * t₁⁻¹, hyk⟩ rfl
    have hc : ((⟨t₁ * k * t₁⁻¹, hyk⟩ * (⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t)))⁻¹ :
        ↥(Q3NL.exactLayer3 Ω (z * t))) : G) = ⁅t₁, k⁆ := by
      simp [commutatorElement_def]
    have hcomm_mem : ⁅t₁, k⁆ ∈ Q3NL.exactCore3 (z * t) J := by
      rw [commutatorElement_def]
      exact (Q3NL.exactCore3 (z * t) J).mul_mem ((Subgroup.mem_normalizer_iff.mp hLaN k).mp hk)
        ((Q3NL.exactCore3 (z * t) J).inv_mem hk)
    rw [← hc]
    refine mem_oddCoreOf_layerRes_of_mk_mem hJt _ (by rw [hc]; exact hcomm_mem) ?_
    change s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY⟩ (↑(⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z *
        t)))) *
      (↑(⟨k, hkY⟩ : ↥(Q3NL.exactLayer3 Ω (z * t))))⁻¹ ∈ _ at h0
    rw [e] at h0
    simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h0
  
  set La : Subgroup G := Q3NL.exactCore3 (z * t) J with hLa
  have hLaJ : La ≤ J := Q3NL.exactCore3_le_left _ J
  have hTJ : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hs.hT.1 hs.hT.2.1
  have hTLa : IsSylow2In T La := Layer.isSylow2In_exactCore3_of_le_cenZ hTJ (T8V.T_le_cenZ hs)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers t₁) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow ht1sq
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hĴN : La ⊔ Subgroup.zpowers t₁ ≤ Subgroup.normalizer (La : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hLaN)
  obtain ⟨V, hV, hVt⟩ := IsSylow2In.exists_ge hzp
    (le_sup_right : Subgroup.zpowers t₁ ≤ La ⊔ Subgroup.zpowers t₁)
  have hP : IsSylow2In (V ⊓ La) La :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hĴN
  have hPcard : Nat.card ↥(V ⊓ La) = Nat.card T := hP.natCard_eq hTLa
  have hPJ : IsSylow2In (V ⊓ La) J :=
    IsSylow2In.of_natCard_le hTJ hP.2.1 (inf_le_right.trans hLaJ) (le_of_eq hPcard.symm)
  have hPc : V ⊓ La ≤ Subgroup.centralizer ({t₁} : Set G) := by
    intro k hk
    have hkV : k ∈ V := hk.1
    have hkLa : k ∈ La := hk.2
    have ht1V : t₁ ∈ V := hVt (Subgroup.mem_zpowers t₁)
    have hmemV : ⁅t₁, k⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem ht1V hkV) (V.inv_mem ht1V)) (V.inv_mem hkV)
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅t₁, k⁆) :=
      hV.2.1.to_le (Subgroup.zpowers_le.mpr hmemV)
    have h1 : ⁅t₁, k⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hstep1 k hkLa) hpg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  
  have hPR : V ⊓ La ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hPJ
  have h8 : 8 ≤ Nat.card ↥(V ⊓ La) := hΩ.eight_le_of_mem_RSet hPR
  have hJJ₁ : J ≠ J₁ := by
    intro h
    have h1 : t₁ ∈ J := h ▸ hJ₁t.mem
    rcases hs.ht.unique t₁ h1 ht1sq with h2 | h2
    · exact hJ₁t.ne_one h2
    · exact hne h2
  have hPN : V ⊓ La ≤ Subgroup.normalizer (J₁ : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hJ₁ hJΩ (Ne.symm hJJ₁) hJ₁t
      (inf_le_right.trans hLaJ) hP.2.1 (by omega) hPc
  have hJnb : J ∈ omegaNbr Ω J₁ :=
    ⟨hJΩ, hJJ₁, V ⊓ La, hPR, inf_le_right.trans hLaJ, hPN⟩
  
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaMod (restrictFamily Ω X) := Sect.hypOmegaGen_restrict hs.stand.modU X
  have hJ₁Λ : J₁.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJ₁ hJ₁X
  have hJΛ : J.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJΩ hJX
  have h1 := C25J.omegaNbr_subgroupOf_gen hΩ hJ₁X hJX hJΩ hJnb
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have himg := T8S2.map_ne_of_noTwins hΛ hNodd (isUniqueInvolution_subgroupOf hJ₁t hJ₁X)
    (isUniqueInvolution_subgroupOf hs.ht hJX) h1 (by
      rintro ⟨-, z', hz'K, hz'J⟩
      have hJK : J ∈ twinSet Ω J₁ :=
        ⟨hJΩ, (z' : G), isUniqueInvolution_of_subgroupOf hz'K hJ₁X,
          isUniqueInvolution_of_subgroupOf hz'J hJX⟩
      rw [hnt J₁ hJ₁ J hJK])
  have hnbr' := T8S2.omegaNbr_map_odd hΛ hNodd h1 himg
  have hDE := s26XEdgeless_E4 hs hdisc hE
  exact hDE _ ⟨_, hJ₁Λ, rfl⟩ _ ⟨_, hJΛ, rfl⟩ (Or.inl hnbr')
end Triv
end T8W
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace T8W
open CFSG.ClassicalInvolution.Asc77.T8W
section Statement
end Statement
section Assembly
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layerJoin_le_sigmaNorm_E4 [IsSimpleGroup G] (hgen : E4SecGen3)
    (hs : Std8 Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) :
    Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hne0 : (Q3NL.tqMembers3 Ω (z * t)).Nonempty := ⟨K, hKt⟩
  have hO := oddCoreOf_layerJoin_le_E4 hs hdisc hE
  by_cases hconn : T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))
  · exact Layer.exactLayer3_le_sigmaNorm_of_lift hL hKt (s26_dComp_eq_of_e4 hs hE) hO hconn
  
  obtain ⟨t₁, ht1sq, ht1ne, hne, htt1, hzt1, -, hcommR, hnJ, hC1, hC2, J₁, hJ₁, hJ₁X, hJ₁t⟩ :=
    exists_good_involution_E4 hs hdisc hE
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have htcen : t ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    have h1 : t * (z * t) = z := by rw [hzt, ← mul_assoc, hs.ht.sq, one_mul]
    have h2 : z * t * t = z := by rw [mul_assoc, hs.ht.sq, mul_one]
    rw [h1, h2])
  have ht1cen : t₁ ∈ T8.cenZ (z * t) := T8.mem_cenZ_iff.mpr (by
    calc t₁ * (z * t) = (t₁ * z) * t := by rw [mul_assoc]
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by rw [mul_assoc]
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by rw [mul_assoc])
  have hJmem : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hs.hJ
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ sigmaNorm Ω K :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) hs.ht).trans
      (T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJmem)
  have htY := T8V.t_mem_layerJoin hs
  have hzY := T8V.z_mem_layerJoin hs
  have hyY1 : t₁ ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant ht1cen)
  have hyYt : t ∈ Subgroup.normalizer ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant htcen)
  set σ : MulAut (Q3T7.layerQuot3 Ω (z * t)) := s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY1⟩ with
      hσ
  set x' : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) t htY with hx'
  set x : Q3T7.layerQuot3 Ω (z * t) := T8V.layerMk (z * t) z hzY with hxdef
  have hσt : s26Act (Q3NL.exactLayer3 Ω (z * t)) ⟨t, hyYt⟩ = MulAut.conj x' :=
    s26Act_eq_conj (Q3NL.exactLayer3 Ω (z * t)) ⟨t, htY⟩
  
  have hS : ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪ {g | σ (x' * g * x'⁻¹) = g} :
      Set (Q3T7.layerQuot3 Ω (z * t))) ⊆ (T8W.layerImage Ω (z * t) (sigmaNorm Ω K) :
        Set (Q3T7.layerQuot3 Ω (z * t))) := by
    intro u hu
    rcases hu with (hu | hu) | hu
    · exact mem_layerImage_of_fixed hΩ ht1cen ht1sq hC1 u hu
    · refine mem_layerImage_of_fixed hΩ htcen hs.ht.sq hCt u ?_
      rw [hσt, MulAut.conj_apply]
      have hu' : x' * u = u * x' := hu
      calc x' * u * x'⁻¹ = u * x' * x'⁻¹ := by rw [hu']
        _ = u := by group
    · have hcen : t₁ * t ∈ T8.cenZ (z * t) := (T8.cenZ (z * t)).mul_mem ht1cen htcen
      have hsq : (t₁ * t) * (t₁ * t) = 1 := by
        calc (t₁ * t) * (t₁ * t) = t₁ * (t * t₁) * t := by group
          _ = t₁ * (t₁ * t) * t := by rw [htt1]
          _ = (t₁ * t₁) * (t * t) := by group
          _ = 1 := by rw [ht1sq, hs.ht.sq, mul_one]
      have hC : Subgroup.centralizer ({t₁ * t} : Set G) ≤ sigmaNorm Ω K := by
        rw [← htt1]
        exact hC2
      refine mem_layerImage_of_fixed hΩ hcen hsq hC u ?_
      have hmul : (⟨t₁ * t, mem_normalizer_iff_conjSub_eq.mpr
          (Layer.exactLayer3_conjSub_eq hΩ.conjInvariant hcen)⟩ : ↥(Subgroup.normalizer
            ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G))) = ⟨t₁, hyY1⟩ * ⟨t, hyYt⟩ := rfl
      rw [hmul, map_mul, ← hσ, hσt, MulAut.mul_apply, MulAut.conj_apply]
      exact hu
  
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) (Layer.zt_not_central3 hs)
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Q3NL.exactLayer3 Ω (z * t)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hne' : Layer.layerImg3 Ω (z * t) K ≠ Layer.layerImg3 Ω (z * t) J :=
    Layer.layerImg3_ne_of_involutions hL hXK hXJ hs.hz hs.ht hzt
      (T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hc : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    have hn21 : K ∈ omegaNbr Ω J :=
      Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ
    have h1 : y ∈ Subgroup.centralizer ({z} : Set G) :=
      T8.rep_le_centralizer hc (T8.stdRepJ hs) (T8.stdRepK hs) (Or.inr hn21) hs.hz hy
    exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.stand.mem hs.noTwins hs.hz h1
  have hAB : Layer.layerImg3 Ω (z * t) J ∈ omegaNbr (Q3T7.layerFam3 Ω (z * t))
      (Layer.layerImg3 Ω (z * t) K) :=
    Layer.layerImg3_omegaNbr hKt hJt hTJ (T8V.T_le_cenZ hs) hTN hne'
  have hLYK : Q3NL.exactCore3 (z * t) K ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hKt
  have hLYJ : Q3NL.exactCore3 (z * t) J ≤ Q3NL.exactLayer3 Ω (z * t) :=
    Q3NL.exactCore3_le_exactLayer3 hJt
  have hzL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) K) z :=
    Layer.isUniqueInvolution_exactCore3 hXK.2.1 hs.hz
  have htL : IsUniqueInvolution (Q3NL.exactCore3 (z * t) J) t :=
    Layer.isUniqueInvolution_exactCore3 hXJ.2.1 hs.ht
  have hxA : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) K) x :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf hzL hLYK)
  have hxB : IsUniqueInvolution (Layer.layerImg3 Ω (z * t) J) x' :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd _)
      (isUniqueInvolution_subgroupOf htL hLYJ)
  have hcen : x * x' ∈ Subgroup.center (Q3T7.layerQuot3 Ω (z * t)) := T8V.layerMk_central hs
  
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨t₁, hyY1⟩ * ⟨t₁, hyY1⟩ : ↥(Subgroup.normalizer
        ((Q3NL.exactLayer3 Ω (z * t) : Subgroup G) : Set G))) = 1 := Subtype.ext ht1sq
    rw [this, map_one]
  have hσx' : σ x' = x' := by
    refine s26Act_mk (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY1⟩ ⟨t, htY⟩ ⟨t, htY⟩ ?_
    show t = t₁ * t * t₁⁻¹
    calc t = t * t₁ * t₁⁻¹ := by group
      _ = t₁ * t * t₁⁻¹ := by rw [htt1]
  have hRsyl : IsSylow2In R K :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hyNK : t₁ ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hzt1.symm)
  have hcommK : ∀ k ∈ K, ⁅t₁, k⁆ ∈ oddCoreOf K :=
    commutator_mem_oddCoreOf_of_pow3 hs.hz hRsyl hyNK (m := 1)
      (by rw [pow_one, pow_two]; exact ht1sq) (fun r hr => (hcommR r hr).symm)
  have hσA : ∀ k ∈ Layer.layerImg3 Ω (z * t) K,
      σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t) K) :=
    T8V.s26Act_mul_inv_mem hΩ hKt ht1cen hyNK hcommK
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (Q3NL.exactCore3 (z * t) J : Set G) :=
    Layer.mem_normalizer_exactCore3 hJN ht1cen
  have hσB : ∀ k ∈ Layer.layerImg3 Ω (z * t) J, σ k ∈ Layer.layerImg3 Ω (z * t) J := by
    intro kb hkb
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
    have hkL : (k' : G) ∈ Q3NL.exactCore3 (z * t) J := Subgroup.mem_subgroupOf.mp hk'
    have hyk : t₁ * (k' : G) * t₁⁻¹ ∈ Q3NL.exactLayer3 Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY1 (k' : G)).mp k'.2
    have e := s26Act_mk (Q3NL.exactLayer3 Ω (z * t)) ⟨t₁, hyY1⟩ k' ⟨t₁ * (k' : G) * t₁⁻¹, hyk⟩ rfl
    change σ (↑k') ∈ _
    rw [hσ, e]
    exact ⟨⟨t₁ * (k' : G) * t₁⁻¹, hyk⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hLaN (k' : G)).mp hkL), rfl⟩
  have hσnt : ¬ ∀ k ∈ Layer.layerImg3 Ω (z * t) J, σ k * k⁻¹ ∈ oddCoreOf (Layer.layerImg3 Ω (z * t)
      J) :=
    not_trivial_on_layerImg_J hs hdisc hE ht1cen ht1sq hne hnJ hJ₁ hJ₁X hJ₁t
  have hclosure := hgen (Nat.card G) hs.stand.below hs.stand.ih (Q3T7.layerQuot3 Ω (z * t)) hlt
    (Q3T7.layerFam3 Ω (z * t)) (Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0)
    Q3T7.layerQuot3_oddCore_eq_bot (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0)
    (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0) (Layer.noTwins_layerFam3 hL hnt) hconn _
    (Layer.layerImg3_mem hKt) _ hAB x x' hxA hxB hcen σ hσsq hσx' hσA hσB hσnt
  exact layerJoin_le_of_closure hO _ hS hclosure

theorem c27_8E4_of_e4SecGen (hgen : E4SecGen3) : C27_8E4 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  exact Layer.centralizer_le_sigmaNorm_of_exactLayer3_le hs
    (layerJoin_le_sigmaNorm_E4 hgen hs hdisc hE4)
end Assembly
end T8W
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
