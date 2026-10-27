module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace SubCorrAux

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_singleton_subgroupOf {H : Subgroup G} {a : G} (ha : a ∈ H) :
    centralizer ({(⟨a, ha⟩ : H)} : Set H) = (centralizer ({a} : Set G)).subgroupOf H := by
  ext g
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun hg => congrArg Subtype.val hg, fun hg => Subtype.ext hg⟩

theorem isoCorrSub_subgroupOf {H J E L : Subgroup G} {a : G} (ha : a ∈ H) (hJ : J ≤ H)
    (hE : E ≤ H) (hL : L ≤ H) (hc : IsoCorrSub a J E L) :
    IsoCorrSub (⟨a, ha⟩ : H) (J.subgroupOf H) (E.subgroupOf H) (L.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLN, hLc, hLa, hsup, hfix⟩ := hc
  have hN : normalizer ((E.subgroupOf H : Subgroup H) : Set H) =
      (normalizer (E : Set G)).subgroupOf H := (subgroupOf_normalizer_eq hE).symm
  have hJE : GSLit.fixedLayer (J.subgroupOf H) (E.subgroupOf H) =
      (GSLit.fixedLayer J E).subgroupOf H := B5a.fixedLayer_subgroupOf hJ hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    exact fun z hz => hLN hz
  · have h1 : IsPComponent 2 (L.subgroupOf (normalizer (E : Set G) ⊓ H)) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLN hL) inf_le_left hLc
    rw [← isPComponent_subgroupOf_subgroupOf_iff' (inf_le_right : normalizer (E : Set G) ⊓ H ≤ H)
      2 Nat.prime_two, inf_subgroupOf_right] at h1
    rw [hN]
    exact h1
  · exact (conjugate_subgroupOf_eq L H ⟨a, ha⟩).trans (congrArg (fun M => M.subgroupOf H) hLa)
  · rw [hJE, B5a.oddCoreIn_subgroupOf hL, ← subgroupOf_sup (le_sup_left.trans (hsup.le.trans hL))
      (le_sup_right.trans (hsup.le.trans hL)), hsup]
  · have h1 : L.subgroupOf H ⊓ (centralizer ({a} : Set G)).subgroupOf H =
        (L ⊓ centralizer ({a} : Set G)).subgroupOf H := (comap_inf _ _ _).symm
    rw [hJE, centralizer_singleton_subgroupOf ha, h1, B5a.layerIn_subgroupOf (inf_le_left.trans hL),
      hfix]

end SubCorrAux

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SecCond

private theorem isoCorr_secBar_le (hc : h.SecCond y) (E' : Subgroup (h.secBar y))
    (hE'P : E' ≤ h.secImage y h.S ⊓ coreActionKernel (h.secImage y (h.secJ0 y)))
    (hE'c : Nat.card (h.secImage y h.B) < Nat.card E' ∨
      (Nat.card E' = Nat.card (h.secImage y h.B) ∧
        Nat.card ↥(h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))) <
          Nat.card ↥(h.secImage y h.S ⊓ normalizer (E' : Set (h.secBar y))))) :
    ∃ L : Subgroup X, L ≤ h.secL0 y ∧
      IsoCorrSub hc.secA (h.secImage y (h.secJ0 y)) E' (h.secImage y L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := h.secPre y E' with hE
  have hEG : E ≤ h.secG0 y := secPre_le_G0 E'
  have hBE : h.secB0 y ≤ E := secB0_le_secPre E'
  have hEimg : h.secImage y E = E' := secImage_secPre E'
  have hBS : h.secB0 y ≤ h.S := (h.secB0_le_B y).trans (h.B_le.trans inf_le_left)
  have hEP : E ≤ h.S ⊓ coreActionKernel h.J := by
    intro e he
    have he' := secMk_mem_of_mem_secPre he
    obtain ⟨heS', heK'⟩ := mem_inf.mp (hE'P he')
    have heS : e ∈ h.S := (secMk_mem_secImage_iff hBS _).mp heS'
    have heJ : e ∈ normalizer (h.J : Set X) := (mem_inf.mp (h.S_le heS)).2
    have : Group.IsPerfect (h.secJ0 y) := isPerfect_secJ0
    have heK0 : e ∈ coreActionKernel (h.secJ0 y) :=
      mem_coreActionKernel_of_secMk (h.secJ0_le_G0 y) ((h.secJ0_le y).trans inf_le_right)
        (hEG he) (mem_normalizer_secJ0 (hEG he) heJ) heK'
    refine mem_inf.mpr ⟨heS, B5a.mem_coreActionKernel_of_sup heJ
      ((GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left) secJ0_sup_core.1
      fun t ht => ?_⟩
    have h1 : t⁻¹ * e⁻¹ * t * e ∈ oddCoreIn (h.secJ0 y) := (mem_coreActionKernel.mp heK0).2 t ht
    rw [secJ0_sup_core.2] at h1
    exact (mem_inf.mp h1).2
  have hB0pos : 0 < Nat.card (h.secB0 y) := Nat.card_pos
  have hcE : Nat.card E' * Nat.card (h.secB0 y) = Nat.card E := by
    rw [← hEimg]
    exact card_secImage hBE hEG
  have hcB : Nat.card (h.secImage y h.B) * Nat.card (h.secB0 y) = Nat.card h.B :=
    card_secImage (h.secB0_le_B y) hc.B_le_G0
  have hQimg : h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y)) =
      h.secImage y h.Q := by
    rw [hc.normalizer_secB, ← secImage_inf hBS]
  have hBQ : h.secB0 y ≤ h.Q := (h.secB0_le_B y).trans h.B_le_Q
  have hcQ : Nat.card (h.secImage y h.Q) * Nat.card (h.secB0 y) = Nat.card h.Q :=
    card_secImage hBQ hc.Q_le
  set NE := h.S ⊓ normalizer (E : Set X) ⊓ h.secG0 y with hNE
  have hBNE : h.secB0 y ≤ NE := le_inf (le_inf hBS (hBE.trans le_normalizer)) (h.secB0_le_G0 y)
  have hEimgN : h.secImage y h.S ⊓ normalizer (E' : Set (h.secBar y)) = h.secImage y NE := by
    rw [← hEimg, normalizer_secImage hBE hEG, ← secImage_inf hBS]
    show _ = (NE.subgroupOf (h.secG0 y)).map (h.secMk y)
    rw [hNE, inf_subgroupOf_right]
  have hcNE : Nat.card (h.secImage y NE) * Nat.card (h.secB0 y) = Nat.card NE :=
    card_secImage hBNE inf_le_right
  have hNEle : Nat.card NE ≤ Nat.card ↥(h.S ⊓ normalizer (E : Set X)) :=
    Subgroup.card_le_of_le inf_le_left
  have hcard : Nat.card h.B < Nat.card E ∨ (Nat.card E = Nat.card h.B ∧
      Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) < Nat.card ↥(h.S ⊓ normalizer (E : Set X))) := by
    rcases hE'c with hlt | ⟨heq, hlt⟩
    · left
      rw [← hcE, ← hcB]
      exact Nat.mul_lt_mul_of_pos_right hlt hB0pos
    · right
      refine ⟨by rw [← hcE, ← hcB, heq], ?_⟩
      rw [hQimg, hEimgN] at hlt
      have h1 : Nat.card h.Q < Nat.card NE := by
        rw [← hcQ, ← hcNE]
        exact Nat.mul_lt_mul_of_pos_right hlt hB0pos
      exact lt_of_lt_of_le h1 hNEle
  obtain ⟨L, hLN, hLc, hLa, hsup, hfix⟩ := h.isoCorr_of_lt E hEP hcard
  have hE2 : IsPGroup 2 E := (B5a.isPGroup_S h).to_le (hEP.trans inf_le_left)
  have hL0 : L ≤ h.secL0 y := Sub58.le_layerIn_centralizer_of_isPComponent hE2 hBE hEG hLN hLc
  have hLE : L ≤ centralizer (E : Set X) := by
    have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) E hE2
    rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
    have h2 : L ≤ (pLayer ↥(normalizer (E : Set X)) 2).map (normalizer (E : Set X)).subtype := by
      have h3 := map_mono (f := (normalizer (E : Set X)).subtype)
        (show L.subgroupOf (normalizer (E : Set X)) ≤ pLayer _ 2 from le_sSup hLc)
      rwa [map_subgroupOf_eq_of_le hLN] at h3
    exact (h2.trans h1).trans (map_subtype_le _)
  have hLB : L ≤ centralizer (h.secB0 y : Set X) :=
    hLE.trans (centralizer_le (SetLike.coe_subset_coe.mpr hBE))
  have hLG : L ≤ h.secG0 y := hLB.trans (h.centralizer_le_G0 y)
  refine ⟨L, hL0, ?_⟩
  set L' := h.secImage y L with hL'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hEimg, normalizer_secImage hBE hEG]
    exact secImage_mono hLN
  · set N₀ := normalizer (E : Set X) ⊓ h.secG0 y with hN₀
    have hLN₀ : L ≤ N₀ := le_inf hLN hLG
    have h1 : IsPComponent 2 (L.subgroupOf N₀) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hLN₀ inf_le_left hLc
    have h2 := secImage_isPComponent hLN₀ inf_le_right hLB h1
    have h3 : h.secImage y N₀ = normalizer (E' : Set (h.secBar y)) := by
      rw [← hEimg, normalizer_secImage hBE hEG]
      show (N₀.subgroupOf (h.secG0 y)).map (h.secMk y) = _
      rw [hN₀, inf_subgroupOf_right]
    rwa [h3] at h2
  · rw [hL', ← secImage_conjugate L hc.a_mem_G0, hLa]
  · have hJE : GSLit.fixedLayer (h.secImage y (h.secJ0 y)) E' =
        h.secImage y (GSLit.fixedLayer h.J E) := by
      rw [← hEimg, ← secImage_fixedLayer (h.secJ0_le_G0 y) ((h.secJ0_le y).trans inf_le_right)
        hBE hEG, fixedLayer_secJ0 hBE hEG hEP]
    rw [hJE, hL', ← secImage_oddCoreIn hLG hLB, ← secImage_sup
      (show GSLit.fixedLayer h.J E ≤ h.secG0 y from le_sup_left.trans (hsup.le.trans hLG))
      (show oddCoreIn L ≤ h.secG0 y from (map_subtype_le _).trans hLG), hsup]
  · have hA₀G : h.secB0 y ⊔ zpowers h.a ≤ h.secG0 y :=
      sup_le (h.secB0_le_G0 y) (zpowers_le.mpr hc.a_mem_G0)
    have hfix' : GSLit.fixedLayer h.J E = GSLit.fixedLayer L (h.secB0 y ⊔ zpowers h.a) := by
      rw [hfix]
      show layerIn (L ⊓ centralizer ({h.a} : Set X)) =
        layerIn (L ⊓ centralizer ((h.secB0 y ⊔ zpowers h.a : Subgroup X) : Set X))
      rw [centralizer_sup_zpowers, ← inf_assoc, inf_of_le_left hLB]
    have hJE : GSLit.fixedLayer (h.secImage y (h.secJ0 y)) E' =
        h.secImage y (GSLit.fixedLayer h.J E) := by
      rw [← hEimg, ← secImage_fixedLayer (h.secJ0_le_G0 y) ((h.secJ0_le y).trans inf_le_right)
        hBE hEG, fixedLayer_secJ0 hBE hEG hEP]
    rw [hJE, hfix', secImage_fixedLayer hLG hLB le_sup_left hA₀G,
      secImage_sup (h.secB0_le_G0 y) (zpowers_le.mpr hc.a_mem_G0), secImage_secB0, bot_sup_eq,
      secImage_zpowers hc.a_mem_G0]
    show layerIn (L' ⊓ centralizer ((zpowers hc.secA : Subgroup (h.secBar y)) :
      Set (h.secBar y))) = _
    rw [centralizer_zpowers_eq]

end SecCond

theorem SecCond.isoCorr_subBar (hc : h.SecCond y) (E : Subgroup ↥(h.secSubImg y))
    (hE : E ≤ h.subS y ⊓ coreActionKernel (h.subJ y))
    (hEc : Nat.card (h.subB y) < Nat.card E ∨ (Nat.card E = Nat.card (h.subB y) ∧
      Nat.card ↥(h.subS y ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y))) <
        Nat.card ↥(h.subS y ⊓ normalizer (E : Set ↥(h.secSubImg y))))) :
    ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L := by
  set E₁ := E.map (h.secSubImg y).subtype with hE₁
  have hE₁H : E₁ ≤ h.secSubImg y := map_subtype_le E
  have hEE₁ : E₁.subgroupOf (h.secSubImg y) = E :=
    comap_map_eq_self_of_injective (h.secSubImg y).subtype_injective E
  have hSH : h.secImage y h.S ≤ h.secSubImg y := h.secImage_S_le y
  have hK : coreActionKernel (h.subJ y) =
      (coreActionKernel (h.secImage y (h.secJ0 y))).subgroupOf (h.secSubImg y) :=
    B5a.coreActionKernel_subgroupOf (h.secImage_secJ0_le y)
  have hE₁P : E₁ ≤ h.secImage y h.S ⊓ coreActionKernel (h.secImage y (h.secJ0 y)) := by
    intro x hx
    rw [hE₁] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨heS, heK⟩ := mem_inf.mp (hE he)
    rw [hK] at heK
    exact mem_inf.mpr ⟨heS, heK⟩
  have hcard {A : Subgroup (h.secBar y)} (hA : A ≤ h.secSubImg y) :
      Nat.card ↥(A.subgroupOf (h.secSubImg y)) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  have hcE : Nat.card E₁ = Nat.card E :=
    card_map_of_injective (h.secSubImg y).subtype_injective
  have hcB : Nat.card (h.subB y) = Nat.card (h.secImage y h.B) := hcard (h.secImage_B_le y)
  have hcNB : Nat.card ↥(h.subS y ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
      Set ↥(h.secSubImg y))) =
      Nat.card ↥(h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))) := by
    have h1 : h.subS y ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y)) =
        (h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))).subgroupOf
          (h.secSubImg y) := by
      rw [normalizer_subB]
      exact (comap_inf _ _ _).symm
    rw [h1]
    exact hcard (inf_le_left.trans hSH)
  have hcNE : Nat.card ↥(h.subS y ⊓ normalizer (E : Set ↥(h.secSubImg y))) =
      Nat.card ↥(h.secImage y h.S ⊓ normalizer (E₁ : Set (h.secBar y))) := by
    have h1 : normalizer (E : Set ↥(h.secSubImg y)) =
        (normalizer (E₁ : Set (h.secBar y))).subgroupOf (h.secSubImg y) := by
      have h2 := subgroupOf_normalizer_eq hE₁H
      rw [hEE₁] at h2
      exact h2.symm
    have h2 : h.subS y ⊓ normalizer (E : Set ↥(h.secSubImg y)) =
        (h.secImage y h.S ⊓ normalizer (E₁ : Set (h.secBar y))).subgroupOf (h.secSubImg y) := by
      rw [h1]
      exact (comap_inf _ _ _).symm
    rw [h2]
    exact hcard (inf_le_left.trans hSH)
  have hE₁c : Nat.card (h.secImage y h.B) < Nat.card E₁ ∨
      (Nat.card E₁ = Nat.card (h.secImage y h.B) ∧
        Nat.card ↥(h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))) <
          Nat.card ↥(h.secImage y h.S ⊓ normalizer (E₁ : Set (h.secBar y)))) := by
    rw [hcB, hcNB, hcNE, ← hcE] at hEc
    exact hEc
  obtain ⟨L, hL0, hcorr⟩ := SecCond.isoCorr_secBar_le hc E₁ hE₁P hE₁c
  have hLH : h.secImage y L ≤ h.secSubImg y := secImage_mono (hL0.trans (h.secL0_le_secSub y))
  have h1 := SubCorrAux.isoCorrSub_subgroupOf hc.secA_mem_secSubImg (h.secImage_secJ0_le y) hE₁H
    hLH hcorr
  rw [hEE₁] at h1
  exact ⟨_, h1⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
