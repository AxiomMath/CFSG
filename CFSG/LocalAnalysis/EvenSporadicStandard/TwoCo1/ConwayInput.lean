module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.UniqueCo1
public import CFSG.Monster.Existence.Compat.Co1Iso
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Perf

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster
  CFSG.Monster.ScalarKernel CFSG.Monster.Existence.Compat

@[expose] def Co0Classify : Prop :=
  ∀ y ∈ (⊤ : Subgroup monsterCo0), orderOf y = 2 → y ≠ negCo0 →
    Nat.card (centIn (⊤ : Subgroup monsterCo0) y) = co0C2 ∨
      Nat.card (centIn (⊤ : Subgroup monsterCo0) y) = co0C3

@[expose] def Co0PCoreTypeC : Prop :=
  ∀ y, InvType (⊤ : Subgroup monsterCo0) negCo0 co0C3 y →
    negCo0 ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) ∧
    pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) ≤ (⊤ : Subgroup monsterCo0) ∧
    (∀ a ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y),
      ∀ b ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y), a * b = b * a) ∧
    (∀ a ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y), a ^ 2 = 1) ∧
    Nat.card (pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y)) = 2 ^ 12 ∧
    (⊤ : Subgroup monsterCo0) ⊓
        centralizer ((pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) : Subgroup monsterCo0) :
          Set monsterCo0) ≤ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y)

@[expose] def Co0OrbitTypeC : Prop :=
  ∀ y, InvType (⊤ : Subgroup monsterCo0) negCo0 co0C3 y →
    Nat.card {t : monsterCo0 | t ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) ∧
      InvType (⊤ : Subgroup monsterCo0) negCo0 co0C3 t} = 2576 ∧
    ∀ t, t ∈ pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) →
      InvType (⊤ : Subgroup monsterCo0) negCo0 co0C3 t →
        ∃ n ∈ (⊤ : Subgroup monsterCo0) ⊓ normalizer
          ((pCoreOf 2 (centIn (⊤ : Subgroup monsterCo0) y) : Subgroup monsterCo0) :
            Set monsterCo0), n * y * n⁻¹ = t

structure Co0ConwayFacts : Prop where
  classify : Co0Classify
  pCore_typeC : Co0PCoreTypeC
  orbit_typeC : Co0OrbitTypeC

theorem Co0ConwayFacts.toCo0Facts (h : Co0ConwayFacts) :
    Co0Facts (⊤ : Subgroup monsterCo0) negCo0 co0C2 co0C3 :=
  ⟨h.classify, h.pCore_typeC, h.orbit_typeC⟩

theorem co0LocalFacts_of_conway
    (h : Co0ConwayFacts) : Co0LocalFacts := by
  intro G _ _ L z hz2 hCz hZ h2 hperf hQ
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  have hzL : z ∈ L := hCz ▸ mem_centralizer_singleton_iff.2 rfl
  have hmCo0 : IsSporadic (monsterCo0 ⧸ center monsterCo0) .Co1 := ⟨co1EquivMonsterCo1.symm⟩
  have hnegsq : negCo0 ^ 2 = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    show (negCo0 * negCo0 : monsterCo0).1 v = v
    show (negCo0 : monsterCo0).1 ((negCo0 : monsterCo0).1 v) = v
    rw [coe_negCo0, coe_negCo0, neg_neg]
  have hnegne : negCo0 ≠ 1 := by
    intro h1
    rw [← co0Equiv_negOneO] at h1
    have h2' : negOneO = 1 := co0Equiv.injective (h1.trans (map_one co0Equiv).symm)
    have h3 := congrArg (fun g => mat g (0 : Fin 24) 0) h2'
    simp [mat_negOneO, mat_one] at h3
    norm_num at h3
  have hc2 : Nat.card (center monsterCo0) = 2 := by
    rw [center_monsterCo0, Nat.card_zpowers]
    exact orderOf_eq_prime hnegsq hnegne
  have hfin : Finite monsterCo0 := by
    have hfC : Finite NativeSporadic.Co1 := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
    have hfQ : Finite MonsterCo1 := Finite.of_equiv _ co1EquivMonsterCo1.toEquiv
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center monsterCo0), hc2]
    have : Nat.card (monsterCo0 ⧸ center monsterCo0) ≠ 0 := Nat.card_pos.ne'
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_doubleCovers_Co1 hperf monsterCo0_isPerfect h2 hc2 hQ hmCo0
  obtain ⟨w, hw, hwz⟩ : z ∈ (center L).map L.subtype := hZ ▸ mem_zpowers z
  have hez : e w = negCo0 := by
    have hcen : e w ∈ center monsterCo0 := by
      rw [mem_center_iff]
      intro m
      obtain ⟨a, rfl⟩ := e.surjective m
      rw [← map_mul, ← map_mul, mem_center_iff.1 hw a]
    have hne : e w ≠ 1 := fun h1 => hz1 (by
      have : w = 1 := e.injective (h1.trans (map_one e).symm)
      rw [← hwz, this]; rfl)
    rw [center_monsterCo0] at hcen
    rcases eq_one_or_eq_of_mem_zpowers hnegsq hcen with h1 | h1
    · exact absurd h1 hne
    · exact h1
  let φ : monsterCo0 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hφz : φ negCo0 = z := by
    rw [← hez]
    show (e.symm (e w) : G) = z
    rw [MulEquiv.symm_apply_apply]
    exact hwz
  have hmap : (⊤ : Subgroup monsterCo0).map φ = L := by
    rw [Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective]
    simp [Subgroup.map_top]
  have := Co0Facts.map φ hφ h.toCo0Facts
  rwa [hmap, hφz] at this

end CFSG.EvenSporadicStandard.TwoCo1
