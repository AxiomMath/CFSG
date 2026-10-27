module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Type

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



section U1

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_oddCoreOf_coreLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {n : ↥(coreHull Ω c)} (hn : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    (((n : ↥(Subgroup.centralizer ({c} : Set G))) : G)) ∈ oddCoreOf (coreLayer Ω c) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hiso : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective).toMonoidHom =
      classicalInvolutionOddCore ↥(coreLayer Ω c) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  have h2 : (Subgroup.equivMapOfInjective (coreHull Ω c) C.subtype C.subtype_injective) n ∈
      classicalInvolutionOddCore ↥(coreLayer Ω c) := by
    rw [← hiso]
    exact Subgroup.mem_map_of_mem _ hn
  exact ⟨_, h2, rfl⟩

theorem layer_pair_zstar (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ tqMembers3 Ω c) (hJ₂ : J₂ ∈ tqMembers3 Ω c) {w : G}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ : Subgroup G}
    (hT₁ : IsSylow2In T₁ J₁) (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set G))
    (hpair : ∀ M ∈ TwinDisc.secFam Ω c, M = TwinDisc.secImg Ω c J₁ ∨ M = TwinDisc.secImg Ω c J₂) :
    w ∈ zStarOf (rLayer Ω c) := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hN
  have hwT : w ∈ T₁ := involution_mem_sylow hΩ hJ₁.1 hw₁ hT₁
  have hT₁R : T₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ₁.1 hT₁
  have hT₁L : T₁ ≤ rLayer Ω c :=
    le_iSup₂_of_le T₁ hT₁R (le_iSup (fun _ : T₁ ≤ C => T₁) hT₁c)
  have hwL : w ∈ rLayer Ω c := hT₁L hwT
  obtain ⟨htC, htY, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hw₁
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hw₂
  set wt : ↥H := ⟨⟨w, htC⟩, htY⟩ with hwt
  set zb : ↥H ⧸ N := QuotientGroup.mk wt with hzb
  have hgen : ∀ R ∈ RSet Ω, R ≤ C → ∀ (r : G) (hr : r ∈ R) (hrC : r ∈ C)
      (hrH : (⟨r, hrC⟩ : ↥C) ∈ H), zb * (QuotientGroup.mk (⟨⟨r, hrC⟩, hrH⟩ : ↥H) : ↥H ⧸ N) =
        (QuotientGroup.mk (⟨⟨r, hrC⟩, hrH⟩ : ↥H) : ↥H ⧸ N) * zb := by
    intro R hR hRc r hr hrC hrH
    obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    have hJtq : J ∈ tqMembers3 Ω c :=
      ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R, hRJ, hRc⟩⟩
    have hrcore : r ∈ TwinADescent.coreAt c J :=
      ((TwinADescent.isSylow2In_coreAt_iff hc2 hJtq.2).mpr ⟨hRJ, hRc⟩).1 hr
    have hmem : (QuotientGroup.mk (⟨⟨r, hrC⟩, hrH⟩ : ↥H) : ↥H ⧸ N) ∈ TwinDisc.secImg Ω c J :=
      ⟨⟨⟨r, hrC⟩, hrH⟩, hrcore, rfl⟩
    rcases hpair _ (secImg_mem_secFam hJtq) with h | h
    · rw [h] at hmem
      exact (hz₁.commute_of_mem hmem)
    · rw [h] at hmem
      exact (hz₂.commute_of_mem hmem)
  set Zc : Subgroup ↥H := (Subgroup.centralizer ({zb} : Set (↥H ⧸ N))).comap (QuotientGroup.mk' N)
    with hZc
  have hLsub : rLayer Ω c ≤ (Zc.map H.subtype).map C.subtype := by
    unfold rLayer
    refine iSup₂_le fun R hR => iSup_le fun hRc r hr => ?_
    have hrC : r ∈ C := hRc hr
    have hrH : (⟨r, hrC⟩ : ↥C) ∈ H := by
      have hRL : R ≤ rLayer Ω c := le_iSup₂_of_le R hR (le_iSup (fun _ : R ≤ C => R) hRc)
      have hrL : r ∈ coreLayer Ω c := rLayer_le_coreLayer hΩ h2 hc2 (hRL hr)
      obtain ⟨a, ha, hav⟩ := hrL
      have : a = ⟨r, hrC⟩ := Subtype.ext hav
      rw [← this]
      exact ha
    refine ⟨⟨r, hrC⟩, ⟨⟨⟨r, hrC⟩, hrH⟩, ?_, rfl⟩, rfl⟩
    show QuotientGroup.mk' N _ ∈ Subgroup.centralizer ({zb} : Set (↥H ⧸ N))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgen R hR hRc r hr hrC hrH).symm
  have hLC : rLayer Ω c ≤ coreLayer Ω c := rLayer_le_coreLayer hΩ h2 hc2
  set Lr := rLayer Ω c with hLr
  have hx : (⟨w, hwL⟩ : ↥Lr) ∈ (Subgroup.center (↥Lr ⧸ classicalInvolutionOddCore ↥Lr)).comap
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Lr)) := by
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with | H y => ?_
    show QuotientGroup.mk y * QuotientGroup.mk (⟨w, hwL⟩ : ↥Lr) =
      QuotientGroup.mk (⟨w, hwL⟩ : ↥Lr) * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨a, ha, hay⟩ := hLsub y.2
    obtain ⟨yt, hyt, hya⟩ := ha
    have hytc : QuotientGroup.mk' N yt ∈ Subgroup.centralizer ({zb} : Set (↥H ⧸ N)) := hyt
    rw [Subgroup.mem_centralizer_singleton_iff] at hytc
    have hcomm : zb * (QuotientGroup.mk yt : ↥H ⧸ N) = (QuotientGroup.mk yt : ↥H ⧸ N) * zb := hytc.symm
    rw [hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq] at hcomm
    have hY := mem_oddCoreOf_coreLayer hΩ hc2 hcomm
    have hEq : ((((y * ⟨w, hwL⟩)⁻¹ * (⟨w, hwL⟩ * y) : ↥Lr)) : G) =
        ((((yt * wt)⁻¹ * (wt * yt) : ↥H) : ↥C) : G) := by
      have h1 : (y : G) = ((yt : ↥C) : G) := by rw [← hay, ← hya]; rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
      rfl
    have hS : ((((y * ⟨w, hwL⟩)⁻¹ * (⟨w, hwL⟩ * y) : ↥Lr)) : G) ∈
        oddCoreOf (coreLayer Ω c) ⊓ Lr := by
      refine ⟨hEq ▸ hY, Subtype.mem _⟩
    have hSle : oddCoreOf (coreLayer Ω c) ⊓ Lr ≤ Balance.oddCoreIn Lr := by
      refine Balance.le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
      · intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have hA := Subgroup.mem_normalizer_iff.mp (Balance.normalizer_oddCoreIn _ (hLC ha)) h
        have hB := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ha) h
        simp only [Subgroup.mem_inf]
        exact and_congr hA hB
      · exact (Balance.odd_card_oddCoreIn (coreLayer Ω c)).of_dvd_nat
          (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨b, hb, hbv⟩ := hSle hS
    have : b = ((y * ⟨w, hwL⟩)⁻¹ * (⟨w, hwL⟩ * y) : ↥Lr) := Subtype.ext hbv
    rw [← this]
    exact hb
  exact ⟨_, hx, rfl⟩

end U1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
