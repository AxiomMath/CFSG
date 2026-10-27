module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecJ

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem fixedLayer_secJ0 {E : Subgroup X} (hBE : h.secB0 y ≤ E) (hEG : E ≤ h.secG0 y)
    (hEP : E ≤ h.S ⊓ coreActionKernel h.J) :
    GSLit.fixedLayer (h.secJ0 y) E = GSLit.fixedLayer h.J E := by
  have hE2 : IsPGroup 2 E := (B5a.isPGroup_S h).to_le (hEP.trans inf_le_left)
  have hEJ : E ≤ coreActionKernel h.J := hEP.trans inf_le_right
  have hEJ0 : E ≤ coreActionKernel (h.secJ0 y) := fun e he =>
    mem_coreActionKernel_secJ0 (hEG he) (hEJ he)
  rw [(GSLit.fixedLayer_nested_core isQuasisimple_secJ0 hEJ0 hE2).1 E le_rfl,
    (GSLit.fixedLayer_nested_core (B5a.isQuasisimple_J h) hEJ hE2).1 E le_rfl]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, mem_inf]
  constructor
  · rintro ⟨⟨hg, hgE⟩, hk⟩
    exact ⟨⟨((GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left) hg, hgE⟩, hk⟩
  · rintro ⟨⟨hg, hgE⟩, k, hk⟩
    refine ⟨⟨?_, hgE⟩, k, hk⟩
    have hB0J : h.secB0 y ≤ coreActionKernel h.J := hBE.trans hEJ
    rw [show h.secJ0 y = GSLit.fixedLayer h.J (h.secB0 y) from rfl,
      (GSLit.fixedLayer_nested_core (B5a.isQuasisimple_J h) hB0J (h.isPGroup_secB0 y)).1 _ le_rfl]
    exact subset_closure ⟨mem_inf.mpr ⟨hg, centralizer_le (SetLike.coe_subset_coe.mpr hBE) hgE⟩,
      k, hk⟩

omit [Finite X] in
theorem centralizer_sup_zpowers (A : Subgroup X) (t : X) :
    centralizer ((A ⊔ zpowers t : Subgroup X) : Set X) =
      centralizer (A : Set X) ⊓ centralizer ({t} : Set X) := by
  apply le_antisymm
  · refine le_inf (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)) ?_
    rw [← centralizer_zpowers_eq]
    exact centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
  · rw [le_centralizer_iff]
    refine sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp ?_)
    rw [centralizer_zpowers_eq]
    exact inf_le_right

theorem secImage_sup {A C : Subgroup X} (hA : A ≤ h.secG0 y) (hC : C ≤ h.secG0 y) :
    h.secImage y (A ⊔ C) = h.secImage y A ⊔ h.secImage y C := by
  show ((A ⊔ C).subgroupOf (h.secG0 y)).map (h.secMk y) = _
  have h1 : (A ⊔ C).subgroupOf (h.secG0 y) = A.subgroupOf (h.secG0 y) ⊔ C.subgroupOf (h.secG0 y)
      := by
    apply map_injective (h.secG0 y).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hA hC), map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le hC]
  rw [h1, Subgroup.map_sup]

theorem secImage_secB0 : h.secImage y (h.secB0 y) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨b, hb, rfl⟩
  have h1 : b ∈ (h.secMk y).ker := by rw [ker_secMk]; exact hb
  exact h1

theorem secImage_zpowers {g : X} (hg : g ∈ h.secG0 y) :
    h.secImage y (zpowers g) = zpowers (h.secMk y ⟨g, hg⟩) := by
  show ((zpowers g).subgroupOf (h.secG0 y)).map (h.secMk y) = _
  have h1 : (zpowers g).subgroupOf (h.secG0 y) = zpowers (⟨g, hg⟩ : ↥(h.secG0 y)) := by
    apply map_injective (h.secG0 y).subtype_injective
    rw [map_subgroupOf_eq_of_le ((zpowers_le).mpr hg), MonoidHom.map_zpowers]
    rfl
  rw [h1, MonoidHom.map_zpowers]

abbrev secPre (h : Hyp52 X) (y : X) (E' : Subgroup (h.secBar y)) : Subgroup X :=
  (E'.comap (h.secMk y)).map (h.secG0 y).subtype

theorem secPre_le_G0 (E' : Subgroup (h.secBar y)) : h.secPre y E' ≤ h.secG0 y := map_subtype_le _

theorem secPre_subgroupOf (E' : Subgroup (h.secBar y)) :
    (h.secPre y E').subgroupOf (h.secG0 y) = E'.comap (h.secMk y) :=
  comap_map_eq_self_of_injective (h.secG0 y).subtype_injective _

theorem secImage_secPre (E' : Subgroup (h.secBar y)) : h.secImage y (h.secPre y E') = E' := by
  show ((h.secPre y E').subgroupOf (h.secG0 y)).map (h.secMk y) = _
  rw [secPre_subgroupOf, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem secB0_le_secPre (E' : Subgroup (h.secBar y)) : h.secB0 y ≤ h.secPre y E' := by
  intro b hb
  refine ⟨⟨b, h.secB0_le_G0 y hb⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap]
  have h1 : (⟨b, h.secB0_le_G0 y hb⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := by
    rw [ker_secMk]
    exact hb
  rw [MonoidHom.mem_ker] at h1
  rw [h1]
  exact one_mem _

theorem secMk_mem_of_mem_secPre {E' : Subgroup (h.secBar y)} {g : X} (hg : g ∈ h.secPre y E') :
    h.secMk y ⟨g, secPre_le_G0 E' hg⟩ ∈ E' := by
  obtain ⟨g', hg', rfl⟩ := mem_map.mp hg
  exact hg'

theorem mem_normalizer_secJ0 {g : X} (hgG : g ∈ h.secG0 y) (hgJ : g ∈ normalizer (h.J : Set X)) :
    g ∈ normalizer (h.secJ0 y : Set X) := by
  have hconj : conjugate (h.secJ0 y) g = h.secJ0 y := by
    change (GSLit.fixedLayer h.J (h.secB0 y)).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [GSLit.map_fixedLayer]
    change GSLit.fixedLayer (conjugate h.J g) (conjugate (h.secB0 y) g) = _
    rw [conjugate_eq_of_mem_normalizer hgJ, conjugate_eq_of_mem_normalizer hgG]
  exact mem_normalizer_of_conjugate_eq hconj

theorem isPerfect_secJ0 : Group.IsPerfect (h.secJ0 y) :=
  B5a.isPerfect_of_isPComponent_subgroupOf (h.secJ0_le y) isPComponent_secJ0

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem isoCorr_secBar (E' : Subgroup (h.secBar y))
    (hE'P : E' ≤ h.secImage y h.S ⊓ coreActionKernel (h.secImage y (h.secJ0 y)))
    (hE'c : Nat.card (h.secImage y h.B) < Nat.card E' ∨
      (Nat.card E' = Nat.card (h.secImage y h.B) ∧
        Nat.card ↥(h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y))) <
          Nat.card ↥(h.secImage y h.S ⊓ normalizer (E' : Set (h.secBar y))))) :
    ∃ L' : Subgroup (h.secBar y), IsoCorrSub hc.secA (h.secImage y (h.secJ0 y)) E' L' := by
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
  set L' := h.secImage y L with hL'
  refine ⟨L', ?_, ?_, ?_, ?_, ?_⟩
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

end Hyp52

end CFSG.ComponentClassification.GSThmB
