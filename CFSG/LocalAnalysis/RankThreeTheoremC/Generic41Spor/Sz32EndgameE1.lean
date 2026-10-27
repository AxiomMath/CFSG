module

import CFSG.Adapters.WholeGroupLayer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.Open.GLADefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

private theorem sz32E1_eq_bot_of_normal_in_normal {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hcore : primeComplementCore (G := Y) p = ⊥)
    {C D : Subgroup Y} [C.Normal] (hDC : D ≤ C) (hcop : Nat.Coprime p (Nat.card D))
    (hn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) : D = ⊥ := by
  set A : Subgroup C := primeComplementCore (G := C) p with hA
  have : A.Characteristic := primeComplementCore_characteristic p
  have hD' : (D.subgroupOf C).Normal :=
    ⟨fun d hd c => Subgroup.mem_subgroupOf.mpr (hn c c.2 d (Subgroup.mem_subgroupOf.mp hd))⟩
  have hDA : D.subgroupOf C ≤ A := by
    refine normal_coprime_le_primeComplementCore p _ hD' ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact hcop
  have hAn : (A.map C.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hAcop : Nat.Coprime p (Nat.card (A.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact primeComplementCore_coprime p
  have hAbot : A.map C.subtype = ⊥ := by
    have := normal_coprime_le_primeComplementCore p _ hAn hAcop
    rwa [hcore, le_bot_iff] at this
  rw [eq_bot_iff]
  intro d hd
  have h1 : (⟨d, hDC hd⟩ : C) ∈ A := hDA (Subgroup.mem_subgroupOf.mpr hd)
  have h2 : d ∈ A.map C.subtype := ⟨⟨d, hDC hd⟩, h1, rfl⟩
  rw [hAbot] at h2
  exact h2

theorem sz32_E1 {Y : Type} [Group Y] [Finite Y] (hcore : primeComplementCore (G := Y) 5 = ⊥)
    {Γ Ob R : Subgroup Y}
    (hΓ : GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y) ≤ Γ)
    (hObcop : Nat.Coprime 5 (Nat.card Ob)) (hObΓ : ∀ g ∈ Γ, ∀ o ∈ Ob, g * o * g⁻¹ ∈ Ob)
    (hR2 : IsPGroup 2 R) (hRO : R ≤ Ob) : R = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpc : pCoreOf 5 (⊤ : Subgroup Y) = CFSG.pCore 5 Y := by
    unfold pCoreOf
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 5 (Subgroup.topEquiv (G := Y)).symm,
      Subgroup.map_map]
    have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := Y)).symm.toMonoidHom =
        MonoidHom.id Y := by
      ext x
      rfl
    rw [this, Subgroup.map_id]
  have hFit : CFSG.fittingSubgroup Y = CFSG.pCore 5 Y := CFSG.Fitting_eq_pcore Y 5 hcore
  have hlayer : GLALayer (⊤ : Subgroup Y) = CFSG.layer Y :=
    (CFSG.WholeGroup.layerOf_congr (fun K => CFSG.isComponent_iff_open K)).symm
  have hX : GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y) = CFSG.generalizedFitting Y := by
    rw [hlayer, hpc, CFSG.generalizedFitting.eq_sup, hFit, sup_comm]
  have hXn : (GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y)).Normal := by
    rw [hX]
    exact (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  set X : Subgroup Y := GLALayer (⊤ : Subgroup Y) ⊔ pCoreOf 5 (⊤ : Subgroup Y)
  haveI : X.Normal := hXn
  have hD : Ob ⊓ X = ⊥ := by
    refine sz32E1_eq_bot_of_normal_in_normal hcore (C := X) inf_le_right
      (hObcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) ?_
    intro c hc d hd
    exact ⟨hObΓ c (hΓ hc) d hd.1, hXn.conj_mem d hd.2 c⟩
  have hRX : ∀ r ∈ R, ∀ g ∈ X, r * g = g * r := by
    intro r hr g hg
    have h1 : r * g * r⁻¹ * g⁻¹ ∈ Ob := by
      have := Ob.mul_mem (hRO hr) (hObΓ g (hΓ hg) r⁻¹ (Ob.inv_mem (hRO hr)))
      simpa [mul_assoc] using this
    have h2 : r * g * r⁻¹ * g⁻¹ ∈ X := X.mul_mem (hXn.conj_mem g hg r) (X.inv_mem hg)
    have h3 : r * g * r⁻¹ * g⁻¹ ∈ Ob ⊓ X := ⟨h1, h2⟩
    rw [hD, Subgroup.mem_bot] at h3
    have h4 : r * g * r⁻¹ = g := mul_inv_eq_one.mp h3
    calc r * g = (r * g * r⁻¹) * r := by group
      _ = g * r := by rw [h4]
  have hRle : R ≤ CFSG.pCore 5 Y := by
    intro r hr
    have hr' : r ∈ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hX] at hg
      exact (hRX r hr g hg).symm
    rw [← hFit]
    exact CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Y hr'
  have hR5 : IsPGroup 5 R := (CFSG.pCore_isPGroup (p := 5) (G := Y)).to_le hRle
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hR2
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 5)).mp hR5
  have hcard : Nat.card R = 1 := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [ha, h0]
      rfl
    · exfalso
      have h2 : 2 ∣ 5 ^ b := by
        rw [← hb, ha]
        exact dvd_pow_self 2 hpos.ne'
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      omega
  exact Subgroup.eq_bot_of_card_eq R hcard

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
