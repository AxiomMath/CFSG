module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalOrbit
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem heldKComponentStepBal_of_exclusions (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    (hB : HeldKStableProper) (hC : HeldKSwapped) : HeldKComponentStepBal := by
  intro X _ _ L hset hbal u hu
  obtain ⟨a, ha, ha2, haC, hTC, hT, hTE⟩ := heldKOrbitData hLay hAK hset hu
  have ht2 : orderOf (⟨a, ha⟩ : ↥(centralizer ({u} : Set X))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ha2
  have hDcore : pPrimeCore 2 ↥(centralizer ({u} : Set X)) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hbal u hu.2.1
  rcases fixedComponent_orbit_trichotomy ht2 hDcore hTC hT hTE with
    h | ⟨M, hM, hTM, hTp, ⟨hMt, hTM', hlt⟩ | hMt⟩
  · exact h
  · have hC' : (M ⊔ conjugate M ⟨a, ha⟩) ⊓
        centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))) =
        M ⊓ centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))) := by
      rw [hMt, sup_idem]
    rw [hC'] at hTp
    exact (hB X L hset hbal u hu a ha ha2 haC M hM hMt hTM' hTp hlt).elim
  · exact (hC X L hset hbal u hu a ha ha2 haC M hM hMt hTM hTp).elim

theorem heldKStableProper_of_centre (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    (hP1 : HeldKStableCentre) : HeldKStableProper := by
  intro X _ _ L hset hbal u hu a ha ha2 haC M hM hMt hTM hTp hlt
  obtain ⟨⟨hsimple, hnonab, hKP, -⟩, -, -, ⟨eL⟩, -⟩ := id hset
  have hu1 : u ≠ 1 := fun h => by have := hu.2.1; rw [h, orderOf_one] at this; omega
  have hDne : centralizer ({u} : Set X) ≠ ⊤ := by
    intro htop
    have hc : u ∈ Subgroup.center X := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({u} : Set X) := htop ▸ Subgroup.mem_top g
      exact (mem_centralizer_singleton_iff.mp this)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · rw [h, Subgroup.mem_bot] at hc; exact hu1 hc
    · obtain ⟨x, y, hxy⟩ := hnonab
      have hx : x ∈ Subgroup.center X := h ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.1 hx y).symm
  have hKG : SectionRank.IsKGroupCat ↥(centralizer ({u} : Set X)) :=
    CFSG.QuasithinUnique.isKGroupCat_of_kProper hKP hDne
  have hDcore : pPrimeCore 2 ↥(centralizer ({u} : Set X)) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hbal u hu.2.1
  have ht2 : orderOf (⟨a, ha⟩ : ↥(centralizer ({u} : Set X))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ha2
  have hKLD : gsFixedLayer L u ≤ L ⊓ centralizer ({u} : Set X) := gsFixedLayer_le_inf L u
  have hKD : gsFixedLayer L u ≤ centralizer ({u} : Set X) := hKLD.trans inf_le_right
  have hKL : gsFixedLayer L u ≤ L := hKLD.trans inf_le_left
  have hKtype := isHeldKType_gsFixedLayer hLay hAK hset hu
  have hTtype : IsHeldKType ↥((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) :=
    IsHeldKType.of_mulEquiv (subgroupOfEquivOfLe hKD).symm hKtype
  have huK : u ∈ gsFixedLayer L u := by
    obtain ⟨-, -, hKC⟩ := hAK X L ⟨eL⟩ u hu
    have hcomm : ∀ k ∈ gsFixedLayer L u, u * k = k * u := fun k hk =>
      (mem_centralizer_singleton_iff.mp (hKD hk)).symm
    rcases hKC u hu.1 hcomm with h | ⟨-, hz⟩
    · exact absurd h hu1
    · obtain ⟨z, -, hzu⟩ := hz
      have h2 : (z : X) ∈ gsFixedLayer L u := z.2
      have h3 : (z : X) = u := hzu
      exact Eq.mp (congrArg (fun x : X => x ∈ gsFixedLayer L u) h3) h2
  have huD : u ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  set u' : ↥(centralizer ({u} : Set X)) := ⟨u, huD⟩ with hu'def
  have hu'T : u' ∈ (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) :=
    mem_subgroupOf.mpr huK
  have hu'M : u' ∈ M := hTM hu'T
  have hu'Z : u' ∈ (center ↥M).map M.subtype := by
    refine ⟨⟨u', hu'M⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (g : ↥(centralizer ({u} : Set X))).2
  have hcentre := hP1 ↥(centralizer ({u} : Set X)) hKG hDcore ⟨a, ha⟩ ht2 M
    ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) hM hMt
    (le_inf hTM (by
      intro x hx
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_iff.mp haC (x : X) (hKL (mem_subgroupOf.mp hx)))))
    hTp hlt hTtype
  have hmem : u' ∈ (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) ⊓
      (center ↥M).map M.subtype := ⟨hu'T, hu'Z⟩
  rw [hcentre, Subgroup.mem_bot] at hmem
  exact hu1 (congrArg Subtype.val hmem)

theorem heldKComponentStepBal_of_P1_P2 (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    (hP1 : HeldKStableCentre) (hP2 : HeldKSwapped) : HeldKComponentStepBal :=
  heldKComponentStepBal_of_exclusions hLay hAK (heldKStableProper_of_centre hLay hAK hP1) hP2

end CFSG.ComponentClassification.GrSLit
