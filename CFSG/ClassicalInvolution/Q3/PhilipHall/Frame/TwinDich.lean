module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmAInner
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.TL3DichMain

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightCore_le_of_conj (_hd : Q8TwinDatum R S t) {H : Subgroup Y}
    (h : ∀ r ∈ R, conjSub r ((S : Subgroup R).map R.subtype) ≤ H) : tightCore R ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxR, hx2⟩
  set x' : ↥R := ⟨x, hxR⟩ with hx'
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x') := by
    refine (hx2.comap_subtype (K := R)).to_le ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers x)
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S P
  have hxP : x' ∈ (P : Subgroup R) := hP (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
  have hs : g⁻¹ * x' * g ∈ (S : Subgroup R) := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hxP
  refine h g g.2 ?_
  rw [mem_conjSub_iff]
  exact ⟨_, hs, by simp [hx']⟩

theorem eq_top_of_conj (hd : Q8TwinDatum R S t) (hgen : TightSelfGen R)
    {H : Subgroup Y} (h : ∀ y : Y, conjSub y ((S : Subgroup R).map R.subtype) ≤ H) : H = ⊤ := by
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  rw [eq_top_iff, ← hgen']
  refine iSup_le fun g => ?_
  have hK : tightCore R ≤ conjSub g⁻¹ H := tightCore_le_of_conj hd fun r _ =>
    calc conjSub r ((S : Subgroup R).map R.subtype)
        = conjSub g⁻¹ (conjSub (g * r) ((S : Subgroup R).map R.subtype)) := by
          rw [conjSub_mul, conjSub_inv_conjSub]
      _ ≤ conjSub g⁻¹ H := conjSub_mono (h (g * r))
  calc conjSub g (tightCore R) ≤ conjSub g (conjSub g⁻¹ H) := conjSub_mono hK
    _ = H := conjSub_conjSub_inv g H

theorem exists_S₀_pair (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype,
      r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Q8Datum.exists_S₀_pair hd hq8

theorem twinDichotomy_of_thmA (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hThmA : (¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) →
      ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ s ∈ (S : Subgroup R).map R.subtype,
        conjSub s A = A) :
    TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t := by
  classical
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  right
  have hE2' : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P := hE2
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hd.sylow_core.2.1
  have hmem : ∀ X : Subgroup Y, S₀ ⊓ X ≠ ⊥ → t ∈ X := fun X hX =>
    (Subgroup.mem_inf.mp (Inner.mem_of_ne_bot hd (inf_le_left.trans (Subgroup.map_subtype_le _))
      (hS₀2.to_le inf_le_left) hX)).2
  have h613 : ∀ X : Subgroup Y, X.Normal → t ∉ X → S₀ ≤ Subgroup.centralizer (X : Set Y) := by
    intro X hXn htX
    have hSX : S₀ ⊓ X = ⊥ := by
      by_contra hne
      exact htX (hmem X hne)
    have h1 := comm613Gen_normal hΩ (Inner.S₀_mem_RSet hd) hXn hSX
    have h2 : oddCoreOf X = ⊥ := by
      have := hXn
      rw [AscThmA.oddCoreOf_eq_inf, hO', inf_bot_eq]
    rw [h2, le_bot_iff] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hcen : ∀ X : Subgroup Y, X.Normal → S₀ ≤ Subgroup.centralizer (X : Set Y) →
      X ≤ Subgroup.center Y := by
    intro X hXn hSC
    have htop : Subgroup.centralizer (X : Set Y) = ⊤ := eq_top_of_conj hd hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ X := by simpa using hXn.conj_mem p hp y⁻¹
      have := Subgroup.mem_centralizer_iff.mp (hSC hx) _ hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [this]
        _ = x * p := by group
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (X : Set Y) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm
  have hFZ : genFittingFitting Y ≤ Subgroup.center Y := by
    have hFn : (genFittingFitting Y).Normal := genFittingFitting_normal
    have hF2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO'
    exact hcen _ hFn (h613 _ hFn fun h => hE2' ⟨_, hFn, hF2, h⟩)
  have hThmA : ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ s ∈ S₀, conjSub s A = A :=
    hThmA hE2'
  have hnorm : ∀ A : Subgroup Y, CFSG.IsComponent A → A.Normal := by
    intro A hA
    have htop : Subgroup.normalizer (A : Set Y) = ⊤ := eq_top_of_conj hd hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      refine mem_normalizer_iff_conjSub_eq.mpr ?_
      have h1 := hThmA _ (AscThmA.isComponent_conjSub hA y⁻¹) _ hx
      calc conjSub x A = conjSub y (conjSub (y⁻¹ * x * y) (conjSub y⁻¹ A)) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = A := by rw [h1, conjSub_conjSub_inv]
    exact Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := exists_S₀_pair hd hq8
  have hnab : r₁ * r₂ ≠ r₂ * r₁ := by
    intro hc
    have e : (r₁ * r₂) * (r₁ * r₂) = 1 := by
      calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
        _ = r₁ * (r₁ * r₂) * r₂ := by rw [hc]
        _ = (r₁ * r₁) * (r₂ * r₂) := by group
        _ = 1 := by rw [h1, h2, Inner.t_mul_t hd]
    have ht1 : t = 1 := h12.symm.trans e
    have := hd.order
    rw [ht1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hEn : (layer Y).Normal := AscThmA.normal_layer
  have htE : t ∈ layer Y := by
    by_contra htE
    have hSE := h613 (layer Y) hEn htE
    have hSF : S₀ ≤ Subgroup.centralizer (genFittingFStar Y : Set Y) := by
      rw [Subgroup.le_centralizer_iff]
      show genFittingFitting Y ⊔ genFittingLayer Y ≤ _
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro s _
        exact (Subgroup.mem_center_iff.mp (hFZ hx)) s
      · rw [genFittingLayer_eq_layer, ← Subgroup.le_centralizer_iff]
        exact hSE
    have hSFs : S₀ ≤ genFittingFStar Y :=
      hSF.trans (CFSG.Adapters.generalized_fitting_self_centralizing Y)
    exact hnab (Subgroup.mem_centralizer_iff.mp (hSF hr₂) r₁ (hSFs hr₁))
  have hL : ∃ L : Subgroup Y, CFSG.IsComponent L ∧ t ∈ L ∧ ∃ x ∈ L, x * t ≠ t * x := by
    by_contra hno
    push Not at hno
    have hcomp : ∀ A : Subgroup Y, CFSG.IsComponent A → ∀ x ∈ A, x * t = t * x := by
      intro A hA
      by_cases htA : t ∈ A
      · exact hno A hA htA
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mp (h613 A (hnorm A hA) htA hd.mem) x hx
    have hEt : layer Y ≤ Subgroup.centralizer ({t} : Set Y) := by
      show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ _
      exact sSup_le fun A hA x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomp A hA x hx)
    have htC : t ∈ Subgroup.centralizer (layer Y : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEt hh)
    exact hE2' ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup hO', htE, htC⟩
  obtain ⟨L, hLc, htL, hLnc⟩ := hL
  have hLn := hnorm L hLc
  have huniq : ∀ A : Subgroup Y, CFSG.IsComponent A → A = L := by
    intro A hA
    by_contra hAL
    have htA : t ∉ A := by
      intro htA
      obtain ⟨x, hxL, hxt⟩ := hLnc
      exact hxt (comm_of_ne hLc hA (Ne.symm hAL) hxL htA)
    have hAn := hnorm A hA
    have hAZ := hcen A hAn (h613 A hAn htA)
    obtain ⟨a, b, hab⟩ := hA.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hAZ b'.2) (a' : Y))
  have hlayer : layer Y = L := by
    refine le_antisymm ?_ (CFSG.LocalCores.component_le_layer hLc)
    show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ L
    exact sSup_le fun A hA => (huniq A hA).le
  have hFstar : genFittingFStar Y = genFittingFitting Y ⊔ L := by
    show genFittingFitting Y ⊔ genFittingLayer Y = _
    rw [genFittingLayer_eq_layer, hlayer]
  by_cases hFL : genFittingFitting Y ≤ L
  · left
    have e : genFittingFStar Y = L := by rw [hFstar, sup_eq_right.mpr hFL]
    show CFSG.Open.IsQuasisimple ↥(genFittingFStar Y)
    rw [e]
    exact ((CFSG.isComponent_iff_open L).mp hLc).2.2
  · right
    exact ⟨L, hLc, hLn, hlayer, htL, hLnc, hFZ, hFL⟩

theorem thmA_twin (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2))
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hE2 : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {s : Y} (hs : s ∈ (S : Subgroup R).map R.subtype) :
    conjSub s A = A :=
  QuaternionBridge.Q8TwinDatum.conjSub_component_eq_of_cases hd hΩ hq8 hO hE2 hA
    (Q8Datum.conjSub_t_eq hd hΩ hq8 hA)
    (fun _ hr hrA htA => Q8Datum.not_centralizes hd hΩ hA hr hrA htA) hs

theorem twinDichotomy_of (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) :
    TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t :=
  twinDichotomy_of_thmA hd hq8 hgen hO hΩ fun hE2 _ hA _ hs => thmA_twin hd hq8 hΩ hO hE2 hA hs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
