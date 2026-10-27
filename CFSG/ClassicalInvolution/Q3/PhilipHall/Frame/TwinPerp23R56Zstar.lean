module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf5Trans

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.R56

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer {n : ↥(coreHull Ω c)}
    (hn : (((n : ↥(Subgroup.centralizer ({c} : Set G))) : G)) ∈ oddCoreOf (coreLayer Ω c)) :
    n ∈ classicalInvolutionOddCore ↥(coreHull Ω c) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hiso : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective).toMonoidHom =
      classicalInvolutionOddCore ↥(coreLayer Ω c) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  obtain ⟨a, ha, hax⟩ := hn
  rw [← hiso] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbn : b = n := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hax
  exact hbn ▸ hb

theorem secCentral_of_zStar (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {t : G}
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hZ : t ∈ zStarOf (rLayer Ω c))
    (y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) * y := by
  induction y using QuotientGroup.induction_on with | H h => ?_
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set t' : ↥(coreHull Ω c) := ⟨⟨t, htC⟩, htH⟩ with ht'
  have hxL : (((h : ↥C) : G)) ∈ coreLayer Ω c := ⟨h, h.2, rfl⟩
  have hxR : (((h : ↥C) : G)) ∈ rLayer Ω c := TwinDisc.coreHull_map_le_rLayer hΩ hc2 hxL
  have hcomm := ((CFSG.ClassicalInvolution.Asc77.C25V.mem_zStarOf_iff' _).mp hZ).2 _ hxR
  rw [← TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2] at hcomm
  have hκ : (t'⁻¹ * h⁻¹ * t' * h : ↥(coreHull Ω c)) ∈
      classicalInvolutionOddCore ↥(coreHull Ω c) := by
    apply mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer
    exact hcomm
  show (QuotientGroup.mk h : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) t' =
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) t' * QuotientGroup.mk h
  rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥(coreHull Ω c)) h, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : (h * t')⁻¹ * (t' * h) = t'⁻¹ * h⁻¹ * t' * h := by group
  rw [this]
  exact hκ

end Layer

section U


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem u_trans_or_pair (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ J₁ J₂ : Subgroup Y, J₁ ∈ tqMembers3 (Om R) u ∧ J₂ ∈ tqMembers3 (Om R) u ∧
      IsUniqueInvolution J₁ (u * e) ∧ IsUniqueInvolution J₂ (u * e) ∧
      ((∀ K ∈ TwinDisc.secFam (Om R) u, ∀ L ∈ TwinDisc.secFam (Om R) u,
          ∃ x : SecQ R u, conjSub x K = L) ∨
        ∀ M ∈ TwinDisc.secFam (Om R) u,
          M = TwinDisc.secImg (Om R) u J₁ ∨ M = TwinDisc.secImg (Om R) u J₂) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₃u := conj_cent_u hc hR₁e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz (hR₁.1 hx)))
  have hR₃'u := conj_cent_u hc hR₁'e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz' (hR₁'.1 hx)))
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  obtain ⟨-, hdich⟩ := layer_exit_frame hT hc.std.perp hd.hu2 hd.hu1 hJ₁ hJ₂ hne₂ hτ₁ hτ₂
    hR₃ hR₃' hR₃u hR₃'u (hcomm.conjSub g) (perp_conj_pair hΩ hp₁ g) (perp_conj_pair hΩ hp₂ g)
  exact ⟨_, _, ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩,
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩, hτ₁, hτ₂,
    hdich⟩

theorem p23_zstar_cu (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) :
    u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hτ₁, hτ₂, hdich⟩ := u_trans_or_pair hT hc
  obtain ⟨htC, htH, hzz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  obtain ⟨htC₂, htH₂, hzz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hτ₂
  rcases hdich with htr | hpair
  · exact TwinPerpV3.mem_zStarOf_of_secCentral hΩ hc2 hJ₁ htC htH hzz₁ htr
      (secCentral_of_zStar hΩ h2 hc2 htC htH hZ)
  · refine TwinPerpV3.mem_zStarOf_of_allMembers hΩ hc2 hJ₁ htC htH ?_
    intro M hM
    rcases hpair M hM with rfl | rfl
    · exact hzz₁
    · exact hzz₂

theorem p23_cu_split (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) {x : Y} (hx : x ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∃ o ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y)),
      o⁻¹ * x ∈ Subgroup.centralizer ({u * e} : Set Y) := by
  have hz := p23_zstar_cu hT hc hZ
  have hcC := ue_comm_u hc
  have hinv : (u * e)⁻¹ = u * e := inv_eq_of_mul_eq_one_right (ue_sq hc)
  refine Q3T8.Asc77.exists_mem_oddCoreOf_centralizer_of_comm (ue_sq hc) ?_ ?_ hx
  · exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hcC)
  · intro y hy
    have h1 := ((CFSG.ClassicalInvolution.Asc77.C25V.mem_zStarOf_iff' _).mp hz).2 y⁻¹
      (Subgroup.inv_mem _ hy)
    rw [hinv, inv_inv] at h1
    rw [hinv]
    exact h1

end U

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.R56
