module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU1

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

section U6

theorem map_sylow_eq_of_isPGroup {A B : Type*} [Group A] [Finite A] [Group B] (g : A →* B)
    (hg : Function.Surjective g) (hB : IsPGroup 2 B) (S : Sylow 2 A) :
    (S : Subgroup A).map g = ⊤ := by
  haveI : Finite B := Finite.of_surjective g hg
  have hle : (S : Subgroup A) ≤ ((S : Subgroup A).map g).comap g := Subgroup.le_comap_map _ _
  have h1 := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ hg] at h1
  obtain ⟨k, hk⟩ := hB.index ((S : Subgroup A).map g)
  have hS : ¬ 2 ∣ (S : Subgroup A).index := S.not_dvd_index
  have hk0 : k = 0 := by
    by_contra h
    exact hS (dvd_trans (dvd_pow_self 2 h) (hk ▸ h1))
  rw [hk0, pow_zero, Subgroup.index_eq_one] at hk
  exact hk

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem inf_oddCoreOf_coreLayer_le (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    oddCoreOf (coreLayer Ω c) ⊓ rLayer Ω c ≤ oddCoreOf (rLayer Ω c) := by
  have hLC : rLayer Ω c ≤ coreLayer Ω c := rLayer_le_coreLayer hΩ h2 hc2
  have hSle : oddCoreOf (coreLayer Ω c) ⊓ rLayer Ω c ≤ Balance.oddCoreIn (rLayer Ω c) := by
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
  exact hSle

theorem layer_pair_case1 (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (TwinDisc.secFam Ω c)) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ tqMembers3 Ω c) (hJ₂ : J₂ ∈ tqMembers3 Ω c) {w : G}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ T₂ : Subgroup G}
    (hT₁ : IsSylow2In T₁ J₁) (hT₂ : IsSylow2In T₂ J₂)
    (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set G)) (hT₂c : T₂ ≤ Subgroup.centralizer ({c} : Set G))
    {Nw : Subgroup G} (hN₁ : T₁ ≤ Nw) (hN₂ : T₂ ≤ Nw)
    (hpair : ∀ M ∈ TwinDisc.secFam Ω c, M = TwinDisc.secImg Ω c J₁ ∨ M = TwinDisc.secImg Ω c J₂) :
    rLayer Ω c ≤ oddCoreOf (rLayer Ω c) ⊔ (rLayer Ω c ⊓ Nw) := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hN
  obtain ⟨htC, htY, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hw₁
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hw₂
  set zb : ↥H ⧸ N := QuotientGroup.mk (⟨⟨w, htC⟩, htY⟩ : ↥H) with hzb
  have hcentTop : Subgroup.centralizer ({zb} : Set (↥H ⧸ N)) = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    refine iSup₂_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hpair M hM with h | h
    · rw [h] at hx
      exact (hz₁.commute_of_mem hx).symm
    · rw [h] at hx
      exact (hz₂.commute_of_mem hx).symm
  have hodd : oddCoreImg (Subgroup.centralizer ({zb} : Set (↥H ⧸ N))) = ⊥ := by
    rw [hcentTop]
    exact TwinExitPf12.oddCoreIn_top_eq_bot' hS.oddFree
  have hA₁ : IsPGroup 2 ↥(TwinDisc.secImg Ω c J₁) :=
    isPGroup_of_oddCent hS.hyp (secImg_mem_secFam hJ₁) hz₁ hodd
      (hS.two _ (secImg_mem_secFam hJ₁))
  have hA₂ : IsPGroup 2 ↥(TwinDisc.secImg Ω c J₂) :=
    isPGroup_of_oddCent hS.hyp (secImg_mem_secFam hJ₂) hz₂ hodd
      (hS.two _ (secImg_mem_secFam hJ₂))
  have hLC : rLayer Ω c ≤ coreLayer Ω c := rLayer_le_coreLayer hΩ h2 hc2
  have hSylL : ∀ {J T : Subgroup G}, J ∈ tqMembers3 Ω c → IsSylow2In T J →
      T ≤ C → T ≤ rLayer Ω c := by
    intro J T hJ hT hTc
    exact le_iSup₂_of_le T (mem_RSet_of_isSylow2In hJ.1 hT) (le_iSup (fun _ : T ≤ C => T) hTc)
  have key : ∀ {Ji Ti : Subgroup G}, Ji ∈ tqMembers3 Ω c → IsSylow2In Ti Ji → Ti ≤ C →
      Ti ≤ Nw → IsPGroup 2 ↥(TwinDisc.secImg Ω c Ji) →
      ∀ (J : Subgroup G), J ∈ tqMembers3 Ω c → TwinDisc.secImg Ω c J = TwinDisc.secImg Ω c Ji →
      ∀ (R : Subgroup G), IsSylow2In R J → R ≤ C →
      ∀ r ∈ R, r ∈ oddCoreOf (rLayer Ω c) ⊔ (rLayer Ω c ⊓ Nw) := by
    intro Ji Ti hJi hTi hTic hTiN hAi J hJ hJeq R hRJ hRc r hr
    have hrC : r ∈ C := hRc hr
    have hRL : R ≤ rLayer Ω c := hSylL hJ hRJ hRc
    have hrH : (⟨r, hrC⟩ : ↥C) ∈ H := by
      have hrL : r ∈ coreLayer Ω c := hLC (hRL hr)
      obtain ⟨a, ha, hav⟩ := hrL
      have : a = ⟨r, hrC⟩ := Subtype.ext hav
      rw [← this]
      exact ha
    have hrcore : r ∈ TwinADescent.coreAt c J :=
      ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hRJ, hRc⟩).1 hr
    have hmem : (QuotientGroup.mk (⟨⟨r, hrC⟩, hrH⟩ : ↥H) : ↥H ⧸ N) ∈ TwinDisc.secImg Ω c J :=
      ⟨⟨⟨r, hrC⟩, hrH⟩, hrcore, rfl⟩
    rw [hJeq] at hmem
    have hTs : IsSylow2In Ti (TwinADescent.coreAt c Ji) :=
      (TwinADescent.isSylow2In_coreAt_iff hc2 hJi.2).mpr ⟨hTi, hTic⟩
    have hTt := (hTs.subgroupOf (TwinADescent.coreAt_le_centralizer c Ji)).subgroupOf (le_coreHull hJi)
    set Ct : Subgroup ↥H := ((TwinADescent.coreAt c Ji).subgroupOf C).subgroupOf H with hCt
    set Tt : Subgroup ↥H := (Ti.subgroupOf C).subgroupOf H with hTt'
    have hBeq : TwinDisc.secImg Ω c Ji = Ct.map (QuotientGroup.mk' N) := rfl
    let g : ↥Ct →* ↥(TwinDisc.secImg Ω c Ji) :=
      ((QuotientGroup.mk' N).comp Ct.subtype).codRestrict (TwinDisc.secImg Ω c Ji)
        (fun x => ⟨x, x.2, rfl⟩)
    have hgs : Function.Surjective g := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hmap := map_sylow_eq_of_isPGroup g hgs hAi (Uniform.sylowOfIsSylow2In hTt)
    have hy : (⟨_, hmem⟩ : ↥(TwinDisc.secImg Ω c Ji)) ∈
        ((Uniform.sylowOfIsSylow2In hTt : Subgroup ↥Ct)).map g := by
      rw [hmap]; trivial
    obtain ⟨s, hs0, hsg⟩ := hy
    have hs : (s : ↥Ct) ∈ Tt.subgroupOf Ct := by
      rw [← Uniform.coe_sylowOfIsSylow2In hTt]; exact hs0
    have hsv : (QuotientGroup.mk' N) (s : ↥H) = QuotientGroup.mk (⟨⟨r, hrC⟩, hrH⟩ : ↥H) :=
      congrArg Subtype.val hsg
    have hsT : ((((s : ↥Ct) : ↥H) : ↥C) : G) ∈ Ti := hs
    have hsq : ((s : ↥Ct) : ↥H)⁻¹ * (⟨⟨r, hrC⟩, hrH⟩ : ↥H) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hsv
    have hY := mem_oddCoreOf_coreLayer hΩ hc2 hsq
    set τ : G := ((((s : ↥Ct) : ↥H) : ↥C) : G) with hτ
    have hτE : τ ∈ rLayer Ω c := hSylL hJi hTi hTic hsT
    have hY' : τ⁻¹ * r ∈ oddCoreOf (coreLayer Ω c) := by
      have : ((((((s : ↥Ct) : ↥H)⁻¹ * (⟨⟨r, hrC⟩, hrH⟩ : ↥H) : ↥H)) : ↥C) : G) = τ⁻¹ * r := rfl
      rw [← this]; exact hY
    have hrE : τ⁻¹ * r ∈ oddCoreOf (rLayer Ω c) :=
      inf_oddCoreOf_coreLayer_le hΩ h2 hc2 ⟨hY', Subgroup.mul_mem _ (Subgroup.inv_mem _ hτE) (hRL hr)⟩
    have : r = τ * (τ⁻¹ * r) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hτE, hTiN hsT⟩) (Subgroup.mem_sup_left hrE)
  unfold rLayer
  refine iSup₂_le fun R hR => iSup_le fun hRc r hr => ?_
  obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJtq : J ∈ tqMembers3 Ω c :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R, hRJ, hRc⟩⟩
  rcases hpair _ (secImg_mem_secFam hJtq) with h | h
  · exact key hJ₁ hT₁ hT₁c hN₁ hA₁ J hJtq h R hRJ hRc r hr
  · exact key hJ₂ hT₂ hT₂c hN₂ hA₂ J hJtq h R hRJ hRc r hr

end U6

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
