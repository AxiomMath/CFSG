module

public import CFSG.ClassicalInvolution.Q3.TL3DichThmB
public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem TightDatum.tightCore_le_of_conj [Finite Y] (_hd : TightDatum R S t) {H : Subgroup Y}
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

theorem TightDatum.eq_top_of_conj (hd : TightDatum R S t) (hgen : TightSelfGen R)
    {H : Subgroup Y} (h : ∀ y : Y, conjSub y ((S : Subgroup R).map R.subtype) ≤ H) : H = ⊤ := by
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  rw [eq_top_iff, ← hgen']
  refine iSup_le fun g => ?_
  have hK : tightCore R ≤ conjSub g⁻¹ H := hd.tightCore_le_of_conj fun r _ =>
    calc conjSub r ((S : Subgroup R).map R.subtype)
        = conjSub g⁻¹ (conjSub (g * r) ((S : Subgroup R).map R.subtype)) := by
          rw [conjSub_mul, conjSub_inv_conjSub]
      _ ≤ conjSub g⁻¹ H := conjSub_mono (h (g * r))
  calc conjSub g (tightCore R) ≤ conjSub g (conjSub g⁻¹ H) := conjSub_mono hK
    _ = H := conjSub_conjSub_inv g H

theorem TightDatum.le_center_of_normal_two (hd : TightDatum R S t) (hc : TightCls Y R S t)
    {N : Subgroup Y} (hNn : N.Normal) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    N ≤ Subgroup.center Y := by
  have htop : Subgroup.centralizer (N : Set Y) = ⊤ :=
    hd.eq_top_of_conj hc.2.1 fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ N := by simpa using hNn.conj_mem p hp y⁻¹
      have := hd.commute_of_normal_two hNn hN2 htN hx hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [← this]
        _ = x * p := by group
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (N : Set Y) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm

theorem TightDatum.not_tightE4 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) (hZ : Subgroup.center Y = ⊥) : ¬ TightE4 Y := by
  rintro ⟨Q, _, f, -, hf2, hf1, -⟩
  have hle := hd.le_center_of_normal_two hc (MonoidHom.normal_ker f) hf2
    fun h => hE2 ⟨_, MonoidHom.normal_ker f, hf2, h⟩
  rw [hZ, le_bot_iff] at hle
  exact hf1 hle

omit [Finite Y] in
theorem genFittingLayer_eq_layer : genFittingLayer Y = layer Y :=
  CFSG.Adapters.genFittingLayer_eq_foundations Y

theorem tightDichotomy_of (hd : TightDatum R S t) (hc : TightCls Y R S t) :
    TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t := by
  classical
  obtain ⟨hq8, hgen, hO⟩ := hc
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  by_cases hE2 : TightInO2 t
  · exact Or.inl hE2
  right
  have hE2' : ¬ ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 ↥P ∧ t ∈ P := hE2
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hd.sylow_core.2.1
  have hmem : ∀ X : Subgroup Y, S₀ ⊓ X ≠ ⊥ → t ∈ X := fun X hX =>
    (Subgroup.mem_inf.mp (hd.mem_of_ne_bot (inf_le_left.trans hd.S₀_le)
      (hS₀2.to_le inf_le_left) hX)).2
  have h613 : ∀ X : Subgroup Y, X.Normal → t ∉ X → S₀ ≤ Subgroup.centralizer (X : Set Y) := by
    intro X hXn htX
    have hSX : S₀ ⊓ X = ⊥ := by
      by_contra hne
      exact htX (hmem X hne)
    have h1 := comm613Gen_normal hd.hypOmegaGen hd.S₀_mem_RSet hXn hSX
    have h2 : oddCoreOf X = ⊥ := by
      have := hXn
      rw [AscThmA.oddCoreOf_eq_inf, hO', inf_bot_eq]
    rw [h2, le_bot_iff] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hcen : ∀ X : Subgroup Y, X.Normal → S₀ ≤ Subgroup.centralizer (X : Set Y) →
      X ≤ Subgroup.center Y := by
    intro X hXn hSC
    have htop : Subgroup.centralizer (X : Set Y) = ⊤ := hd.eq_top_of_conj hgen fun y x hx => by
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
    fun A hA s hs => hd.conjSub_component_eq hq8 hO' hE2' hA hs
  have hnorm : ∀ A : Subgroup Y, CFSG.IsComponent A → A.Normal := by
    intro A hA
    have htop : Subgroup.normalizer (A : Set Y) = ⊤ := hd.eq_top_of_conj hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      refine mem_normalizer_iff_conjSub_eq.mpr ?_
      have h1 := hThmA _ (AscThmA.isComponent_conjSub hA y⁻¹) _ hx
      calc conjSub x A = conjSub y (conjSub (y⁻¹ * x * y) (conjSub y⁻¹ A)) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = A := by rw [h1, conjSub_conjSub_inv]
    exact Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := hd.exists_S₀_pair hq8
  have hnab : r₁ * r₂ ≠ r₂ * r₁ := by
    intro hc
    have e : (r₁ * r₂) * (r₁ * r₂) = 1 := by
      calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
        _ = r₁ * (r₁ * r₂) * r₂ := by rw [hc]
        _ = (r₁ * r₁) * (r₂ * r₂) := by group
        _ = 1 := by rw [h1, h2, t_mul_t hd]
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

theorem tightDichotomy_holds (n : ℕ) : TightDichotomy n :=
  fun _ _ _ _ _ _ _ hd hc => tightDichotomy_of hd hc

section Cit3


theorem tightStep_of_parts₂ (htw : ∀ n, TightTwistStep n) (h1 : TightSmallBase)
    (h2 : ∀ n, TightLargeEdge n) (h3 : ∀ n, TightLargeLift n) : ∀ n, TightStep n :=
  tightStep_of_parts tightDichotomy_holds htw h1 h2 h3

end Cit3

end CFSG.ClassicalInvolution.Q3
