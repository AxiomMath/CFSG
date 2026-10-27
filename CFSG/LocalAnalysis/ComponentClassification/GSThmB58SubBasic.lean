module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Sub58

variable {G : Type*} [Group G]

theorem centralizer_singleton_subgroupOf {H : Subgroup G} (t : ↥H) :
    centralizer ({t} : Set ↥H) = (centralizer ({(t : G)} : Set G)).subgroupOf H := by
  ext z
  rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
  exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩

theorem inf_subgroupOf (A C H : Subgroup G) :
    (A ⊓ C).subgroupOf H = A.subgroupOf H ⊓ C.subgroupOf H :=
  Subgroup.comap_inf _ _ _

theorem subgroupOf_injective_of_le {H A C : Subgroup G} (hA : A ≤ H) (hC : C ≤ H)
    (heq : A.subgroupOf H = C.subgroupOf H) : A = C := by
  rw [subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hC] at heq
  exact heq

theorem isPComponent_subgroupOf_restrict [Finite G] {L C H : Subgroup G} (hLC : L ≤ C)
    (hLH : L ≤ H) (hL : IsPComponent 2 (L.subgroupOf C)) :
    IsPComponent 2 ((L.subgroupOf H).subgroupOf (C.subgroupOf H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPComponent 2 (L.subgroupOf (C ⊓ H)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLC hLH) inf_le_left hL
  rw [← isPComponent_subgroupOf_subgroupOf_iff' (inf_le_right : C ⊓ H ≤ H) 2 Nat.prime_two,
    inf_subgroupOf_right] at h1
  exact h1

end Sub58

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

theorem kProper_subBar : Assembly.KProper Blueprint.Catalog ↥(h.secSubImg y) :=
  LocalAnalysis.ComponentInitial.kProper_subgroup (fun e h => SectionRank.catalog_of_mulEquiv e h)
    SecCond.kProper_secBar (h.secSubImg y)

theorem coreActionKernel_subJ :
    coreActionKernel (h.subJ y) =
      (coreActionKernel (h.secImage y (h.secJ0 y))).subgroupOf (h.secSubImg y) :=
  B5a.coreActionKernel_subgroupOf (h.secImage_secJ0_le y)

theorem normalizer_subJ :
    normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (normalizer (h.secImage y (h.secJ0 y) : Set (h.secBar y))).subgroupOf (h.secSubImg y) :=
  (subgroupOf_normalizer_eq (h.secImage_secJ0_le y)).symm

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem kGroup_normalizer_subB :
    SectionRank.IsKGroupCat ↥(normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
      Set ↥(h.secSubImg y))) := by
  set N := normalizer (h.secImage y h.B : Set (h.secBar y)) with hN
  let e : ↥((h.secSubImg y).subgroupOf N) ≃* ↥(N.subgroupOf (h.secSubImg y)) :=
    { toFun := fun g => ⟨⟨g.1.1, g.2⟩, g.1.2⟩
      invFun := fun g => ⟨⟨g.1.1, g.2⟩, g.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have h1 : SectionRank.IsKGroupCat ↥(N.subgroupOf (h.secSubImg y)) :=
    (hc.kGroup_normalizer_secB.subgroup _).of_mulEquiv e.symm
  exact h1.of_mulEquiv (MulEquiv.subgroupCongr (normalizer_subB (h := h) (y := y)))

theorem normalizer_subB_ne_top :
    normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ≠ ⊤ := by
  intro htop
  have h1 : hc.subX ∈ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
      Set ↥(h.secSubImg y)) := htop ▸ mem_top _
  rw [normalizer_subB, mem_subgroupOf] at h1
  have h2 : hc.secX ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := h1
  rw [hc.normalizer_secB, secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)] at h2
  exact hc.y_not_mem_normalizer h2

theorem orderOf_subA : orderOf hc.subA = 2 := by
  rw [Subgroup.orderOf_mk]
  exact hc.orderOf_secA

theorem subJ_le : h.subJ y ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) := by
  intro z hz
  rw [Sub58.centralizer_singleton_subgroupOf, mem_subgroupOf]
  exact hc.secJ_le (mem_subgroupOf.mp hz)

theorem isPComponent_subJ :
    IsPComponent 2 ((h.subJ y).subgroupOf (centralizer ({hc.subA} : Set ↥(h.secSubImg y)))) := by
  rw [Sub58.centralizer_singleton_subgroupOf]
  exact Sub58.isPComponent_subgroupOf_restrict hc.secJ_le (h.secImage_secJ0_le y)
    hc.isPComponent_secJ

theorem subS_le : h.subS y ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
    normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) := by
  intro z hz
  obtain ⟨h1, h2⟩ := mem_inf.mp (hc.secS_le (mem_subgroupOf.mp hz))
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [Sub58.centralizer_singleton_subgroupOf, mem_subgroupOf]
    exact h1
  · rw [normalizer_subJ, mem_subgroupOf]
    exact h2

theorem subB_ne_bot : h.subB y ≠ ⊥ := by
  intro hbot
  apply hc.secB_ne_bot
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, h.secImage_B_le y hz⟩ : ↥(h.secSubImg y)) ∈ h.subB y := hz
  rw [hbot, mem_bot] at h1
  exact mem_bot.mpr (congrArg Subtype.val h1)

theorem subX_mem : hc.subX ∈ h.subS y := hc.secX_mem

theorem subB_inf_conjugate : h.subB y ⊓ conjugate (h.subB y) hc.subX = ⊥ := by
  rw [conjugate_subgroupOf_eq, ← Sub58.inf_subgroupOf]
  have h1 : h.secImage y h.B ⊓ conjugate (h.secImage y h.B) (hc.subX : h.secBar y) = ⊥ :=
    hc.secB_inf_conjugate
  rw [h1, bot_subgroupOf]

theorem subX_sq_mem : hc.subX ^ 2 ∈ h.subS y ⊓ coreActionKernel (h.subJ y) ⊓
    normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) := by
  have hm := hc.secX_sq_mem
  rw [mem_inf, mem_inf] at hm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hm
  have hcoe : ((hc.subX ^ 2 : ↥(h.secSubImg y)) : h.secBar y) = hc.secX ^ 2 :=
    SubgroupClass.coe_pow _ _
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [mem_subgroupOf, hcoe]
    exact h1
  · rw [coreActionKernel_subJ, mem_subgroupOf, hcoe]
    exact h2
  · rw [normalizer_subB, mem_subgroupOf, hcoe]
    exact h3

theorem subS_inf_coreActionKernel : h.subS y ⊓ coreActionKernel (h.subJ y) =
    (h.secImage y h.P).subgroupOf (h.secSubImg y) := by
  rw [coreActionKernel_subJ, ← Sub58.inf_subgroupOf, secImage_P]

theorem subS_inf_normalizer : h.subS y ⊓
    normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.Q).subgroupOf (h.secSubImg y) := by
  rw [normalizer_subB, ← Sub58.inf_subgroupOf, hc.secImage_Q]

end SecCond

theorem SecCond.secImage_T_eq (hc : h.SecCond y) :
    h.secImage y h.T = h.secImage y h.Q ⊓ coreActionKernel (h.secImage y (h.secJ0 y)) := by
  rw [show h.T = h.Q ⊓ h.P from rfl, secImage_inf ((h.secB0_le_B y).trans h.B_le_Q),
    ← secImage_P]
  apply le_antisymm
  · exact inf_le_inf_left _ inf_le_right
  · exact le_inf inf_le_left
      (le_inf (inf_le_left.trans (secImage_mono inf_le_left)) inf_le_right)

theorem smallType_subJ : SmallType (h.subJ y) := by
  let e₁ : ↥(h.subJ y) ≃* ↥(h.secImage y (h.secJ0 y)) :=
    subgroupOfEquivOfLe (h.secImage_secJ0_le y)
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  obtain ⟨e₃⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv e₂
  rcases SecCond.smallType_secJ (h := h) (y := y) with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, hpf, hm⟩ | hm
  · exact Or.inl ⟨e₂.trans e⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hpf, OddQuot.lieModel_of_equiv e₂.symm hm⟩)
  · exact Or.inr (Or.inr (OddQuot.lieModel_of_equiv e₃.symm hm))

theorem subB_le : h.subB y ≤ h.subS y ⊓ coreActionKernel (h.subJ y) := by
  intro z hz
  obtain ⟨h1, h2⟩ := mem_inf.mp (SecCond.secB_le (mem_subgroupOf.mp hz))
  refine mem_inf.mpr ⟨h1, ?_⟩
  rw [coreActionKernel_subJ, mem_subgroupOf]
  exact h2

end Hyp52

end CFSG.ComponentClassification.GSThmB
