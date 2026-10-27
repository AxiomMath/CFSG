module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def elementFixedSet (H : Subgroup G) (x : G) : Set (pointRightCosetSpace H) :=
  {a | pointRightCosetMul H a x = a}

@[expose] def denominatorFourGroup (u t : G) : Subgroup G :=
  Subgroup.closure ({u, t} : Set G)

theorem right_involution_flip_reverse (H : Subgroup G) (t : G)
    (ht : orderOf t = 2) (a b : pointRightCosetSpace H)
    (hab : pointRightCosetMul H a t = b) : pointRightCosetMul H b t = a := by
  have htt : t * t = 1 := by
    have hp := pow_orderOf_eq_one t
    rw [ht, pow_two] at hp
    exact hp
  rw [← hab, pointRightCosetMul_mul, htt, pointRightCosetMul_one]

theorem right_pair_flip_normalizes (H : Subgroup G) (t : G)
    (ht : orderOf t = 2) (a b : pointRightCosetSpace H)
    (hab : pointRightCosetMul H a t = b) :
    t ∈ Subgroup.normalizer
      ((rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G) : Set G) := by
  have hba := right_involution_flip_reverse H t ht a b hab
  have htinv := inv_eq_self_of_orderOf_eq_two ht
  have hforward : ∀ x ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b,
      t * x * t⁻¹ ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b := by
    intro x hx
    have hxa := (mem_point_right_stabilizer_iff H a x).mp hx.1
    have hxb := (mem_point_right_stabilizer_iff H b x).mp hx.2
    constructor
    · apply (mem_point_right_stabilizer_iff H a _).mpr
      rw [htinv, ← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hab, hxb, hba]
    · apply (mem_point_right_stabilizer_iff H b _).mpr
      rw [htinv, ← pointRightCosetMul_mul, ← pointRightCosetMul_mul, hba, hxa, hab]
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hforward x
  · intro hx
    have hb := hforward (t * x * t⁻¹) hx
    have he : t * (t * x * t⁻¹) * t⁻¹ = x := by
      have htt : t * t = 1 := by
        simpa only [ht, pow_two] using pow_orderOf_eq_one t
      rw [htinv]
      calc
        t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [htt, one_mul, mul_one]
    rwa [he] at hb

theorem pair_hull_orbit_premises (H : Subgroup G) (a b : pointRightCosetSpace H)
    (t v : G) (ht : orderOf t = 2) (hflip : pointRightCosetMul H a t = b)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal)
    (htL : t ∈ L) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({v} : Set G)
    W ≤ E ∧ t ∈ Subgroup.normalizer (W : Set G) ∧
      ∀ e ∈ E, rightConjugateElem t e * t ∈ W := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  let E := D ⊓ Subgroup.centralizer ({v} : Set G)
  have hCN := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLnormal
  have htD := right_pair_flip_normalizes H t ht a b hflip
  have htW : t ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨L.le_normalizer htL, htD⟩
  refine ⟨fun _ hx => ⟨hx.2, hLC hx.1⟩, htW, ?_⟩
  intro e he
  have hteL : rightConjugateElem t e ∈ L :=
    (Subgroup.mem_normalizer_iff''.mp (hCN he.2) t).mp htL
  refine ⟨L.mul_mem hteL htL, ?_⟩
  have hea := (mem_point_right_stabilizer_iff H a e).mp he.1.1
  have heb := (mem_point_right_stabilizer_iff H b e).mp he.1.2
  have heia := (mem_point_right_stabilizer_iff H a e⁻¹).mp
    ((rightCosetStabilizer H a).inv_mem he.1.1)
  have heib := (mem_point_right_stabilizer_iff H b e⁻¹).mp
    ((rightCosetStabilizer H b).inv_mem he.1.2)
  have hba := right_involution_flip_reverse H t ht a b hflip
  constructor
  · apply (mem_point_right_stabilizer_iff H a _).mpr
    simp only [rightConjugateElem, ← pointRightCosetMul_mul, heia, hflip, heb, hba]
  · apply (mem_point_right_stabilizer_iff H b _).mpr
    simp only [rightConjugateElem, ← pointRightCosetMul_mul, heib, hba, hea, hflip]

theorem pair_second_centralizer_eq (D : Subgroup G) (u t : G)
    (ht : orderOf t = 2) :
    (D ⊓ Subgroup.centralizer ({u * t} : Set G)) ⊓ Subgroup.centralizer ({t} : Set G) =
      D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G) := by
  have htt : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  rw [denominatorFourGroup, Subgroup.centralizer_closure]
  ext c
  constructor
  · rintro ⟨⟨hcD, hcv⟩, hct⟩
    have hcV : Commute c (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hcv
    have hcT : Commute c t := Subgroup.mem_centralizer_singleton_iff.mp hct
    have hcU : Commute c u := by
      simpa only [mul_assoc, htt, mul_one] using hcV.mul_right hcT
    refine ⟨hcD, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · exact hcU.eq.symm
    · have hxt : x = t := Set.mem_singleton_iff.mp hx
      subst x
      exact hcT.eq.symm
  · rintro ⟨hcD, hc⟩
    have hcU : Commute c u := (Subgroup.mem_centralizer_iff.mp hc u (by simp)).symm
    have hcT : Commute c t := (Subgroup.mem_centralizer_iff.mp hc t (by simp)).symm
    exact ⟨⟨hcD, Subgroup.mem_centralizer_singleton_iff.mpr (hcU.mul_right hcT).eq⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hcT.eq⟩

variable [Finite G]

theorem pair_hull_intersection_odd {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (L : Subgroup G) (hclass : ∀ x ∈ L, orderOf x = 2 → x ∈ involutionPointClass z) :
    Odd (Nat.card (L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (even_iff_two_dvd.mp heven)
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hunique := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨c, _, hc⟩ := hunique x (hclass x x.property.1 hxG)
  exact hab (((hc a ((mem_point_right_stabilizer_iff H a x).mp x.property.2.1))).trans
    (hc b ((mem_point_right_stabilizer_iff H b x).mp x.property.2.2)).symm)

omit [Finite G] in
theorem odd_pair_intersection_trivial_centralizer (L W : Subgroup G) (hWL : W ≤ L)
    (t : G) (htL : t ∈ L) (hWodd : Odd (Nat.card W))
    (hCtwo : IsPGroup 2 (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L))) :
    W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  let C := Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)
  let f : (W ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) →* C :=
    { toFun := fun w => ⟨⟨w, hWL w.property.1⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w.property.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : L) : G)) hab
  have htwo : IsPGroup 2 (W ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :=
    hCtwo.of_injective f hf
  have hodd : Odd (Nat.card (W ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) :=
    hWodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subgroup.card_eq_one.mp
  rcases htwo.card_eq_or_dvd with hc | hc
  · exact hc
  · exact False.elim (hodd.not_two_dvd_nat hc)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
