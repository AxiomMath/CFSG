module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_mul_iff {s a t : G} (hst : s * t = t * s) :
    s * (a * t) = a * t * s ↔ s * a = a * s := by
  have hc : Commute s t := hst
  constructor
  · intro h
    have h1 := ((show Commute s (a * t) from h).mul_right hc.inv_right).eq
    rwa [mul_inv_cancel_right] at h1
  · intro h
    exact ((show Commute s a from h).mul_right hc).eq

theorem exists_unbalancing_commutator
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hElem : L34ElementaryCenterSylowFact) (hNE : L34NonelementaryCenterCommutatorFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (hZ : S ⊓ coreActionKernel L ⊓ L ≠ ⊥) :
    ∃ u ∈ L34UnbalancingSet L t S, ∃ w ∈ omegaOne (S ⊓ coreActionKernel L), w ≠ 1 ∧
      w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, -, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hZeq : S ⊓ coreActionKernel L ⊓ L = S ⊓ L ⊓ zStarIn L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hxL⟩ := mem_inf.mp hx
      obtain ⟨hxS, hxK⟩ := mem_inf.mp hx1
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxS, hxL⟩,
        inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hxL, hxK⟩)⟩
    · intro x hx
      obtain ⟨hx1, hxZ⟩ := mem_inf.mp hx
      obtain ⟨hxS, hxL⟩ := mem_inf.mp hx1
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxS, zStarIn_le_coreActionKernel L hxZ⟩, hxL⟩
  have key : ∀ a ∈ S ⊓ L, a * a = 1 → a ∉ zStarIn L → ∀ w ∈ S ⊓ L ⊓ zStarIn L, w ≠ 1 →
      w * w = 1 → w ∈ ⁅S ⊓ L ⊓ centralizer ({a} : Set G), S ⊓ L ⊓ centralizer ({a} : Set G)⁆ →
      ∃ u ∈ L34UnbalancingSet L t S, ∃ w ∈ omegaOne (S ⊓ coreActionKernel L), w ≠ 1 ∧
        w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆ := by
    intro a ha ha2 haZ w hw hw1 hw2 hwc
    have haS : a ∈ S := (mem_inf.mp ha).1
    have haK : a ∉ coreActionKernel L := fun h =>
      haZ (inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨(mem_inf.mp ha).2, h⟩))
    have ha1 : a ≠ 1 := fun h => haZ (h ▸ one_mem _)
    have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    have hat : a * t = t * a := hZS a haS
    have hat1 : a * t ≠ 1 := fun h => haK (by
      rw [show a = t⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h]]
      exact inv_mem htK)
    have hato : orderOf (a * t) = 2 := by
      refine orderOf_eq_prime ?_ hat1
      rw [pow_two, show a * t * (a * t) = (a * a) * (t * t) by
        rw [mul_assoc, ← mul_assoc t a t, ← hat]; group, ha2,
        show t * t = 1 by rw [← pow_two, ← hto, pow_orderOf_eq_one], one_mul]
    obtain ⟨-, u₁, hu₁, hu₁n⟩ := l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset a haS
      hao haK (mem_sup_left (mem_inf.mp ha).2)
    have hw' : w ∈ omegaOne (S ⊓ coreActionKernel L) := subset_closure
      ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hw).1).1,
        zStarIn_le_coreActionKernel L (mem_inf.mp hw).2⟩, hw2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu₁
    rcases hu₁ with rfl | rfl
    · exact ⟨u₁, ⟨mem_sup_left ha, hao, hu₁n⟩, w, hw', hw1, hwc⟩
    · have hcen : S ⊓ L ⊓ centralizer ({a * t} : Set G) =
          S ⊓ L ⊓ centralizer ({a} : Set G) := by
        ext s
        simp only [mem_inf, mem_centralizer_singleton_iff]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (commute_mul_iff (hZS s h1.1)).mp h2⟩,
          fun ⟨h1, h2⟩ => ⟨h1, (commute_mul_iff (hZS s h1.1)).mpr h2⟩⟩
      refine ⟨a * t, ⟨mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers t)), hato, hu₁n⟩,
        w, hw', hw1, ?_⟩
      rw [hcen]
      exact hwc
  have hZ' : S ⊓ L ⊓ zStarIn L ≠ ⊥ := hZeq ▸ hZ
  obtain ⟨w, hwZ, hw1⟩ : ∃ w ∈ S ⊓ L ⊓ zStarIn L, w ≠ 1 := by
    by_contra h
    push Not at h
    exact hZ' (eq_bot_iff.mpr fun x hx => mem_bot.mpr (h x hx))
  have helem : (∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1) →
      ∃ u ∈ L34UnbalancingSet L t S, ∃ w ∈ omegaOne (S ⊓ coreActionKernel L), w ≠ 1 ∧
        w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆ := by
    intro hel
    have hel' : ∀ z ∈ S ⊓ L ⊓ zStarIn L, z * z = 1 := fun z hz => hel z (hZeq ▸ hz)
    obtain ⟨hE, hcard, hder⟩ := hElem G L (S ⊓ L) hperf htypeL hS₀ hel'
    obtain ⟨a, haC, haZ⟩ : ∃ a ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G),
        a ∉ zStarIn L := by
      by_contra h
      push Not at h
      have hle : S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L ⊓ zStarIn L :=
        fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).1, h x hx⟩
      have h1 := card_le_of_le hle
      have h2 : 0 < Nat.card ↥(S ⊓ L ⊓ zStarIn L) := Nat.card_pos
      omega
    have haS₀ : a ∈ S ⊓ L := (mem_inf.mp haC).1
    have hSa : S ⊓ L ⊓ centralizer ({a} : Set G) = S ⊓ L := inf_eq_left.mpr fun s hs =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp haC).2 s hs)
    have hwS₀ : w ∈ S ⊓ L := (mem_inf.mp hwZ).1
    have hwK : w ∈ coreActionKernel L := zStarIn_le_coreActionKernel L (mem_inf.mp hwZ).2
    have hwC : w ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
      mem_inf.mpr ⟨hwS₀, mem_centralizer_iff.mpr fun h hh =>
        (commute_of_mem_coreActionKernel hS2 (mem_inf.mp hwS₀).1 hwK (mem_inf.mp hh).1
          (mem_inf.mp hh).2).symm⟩
    refine key a haS₀ (hE.2 a haC) haZ w hwZ hw1 (hel' w hwZ) ?_
    rw [hSa]
    exact hder hwC
  by_cases hel : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1
  · exact helem hel
  · push Not at hel
    obtain ⟨z, hz, hz2⟩ := hel
    obtain ⟨a, ha, ha2, haZ, w', hw', hw'1, hw'2, hw'c⟩ :=
      hNE G L (S ⊓ L) hperf htypeL hS₀ ⟨z, hZeq ▸ hz, hz2⟩
    exact key a ha ha2 haZ w' hw' hw'1 hw'2 hw'c

end CFSG.ComponentClassification.GrSLit.GrS5
