module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {Y : Type} [Group Y]

private theorem isKleinFour_subgroupOf_of_le {X A : Subgroup Y} (hAX : A ≤ X)
    (hA : IsKleinFour A) : IsKleinFour (A.subgroupOf X) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv).trans hA.card_four
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact FooteLit.sq_eq_one_of_isKleinFour hA (Subgroup.mem_subgroupOf.mp hx)

private theorem ncard_eq_four {B : Subgroup Y} (hB : IsKleinFour B) :
    (B : Set Y).ncard = 4 := by
  rw [← Nat.card_coe_set_eq]
  exact hB.card_four

private theorem exists_ne_one_ne {B : Subgroup Y} (hB : IsKleinFour B) (z : Y) :
    ∃ b ∈ B, b ≠ 1 ∧ b ≠ z := by
  by_contra h
  push Not at h
  have hsub : (B : Set Y) ⊆ ({1, z} : Set Y) := by
    intro b hb
    by_cases h1 : b = 1
    · exact Set.mem_insert_iff.mpr (Or.inl h1)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (h b hb h1)))
  have hle := Set.ncard_le_ncard hsub
  have h2 : ({1, z} : Set Y).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : Y) {z}
    rw [Set.ncard_singleton] at this
    omega
  have h4 := ncard_eq_four hB
  omega

private theorem le_centralizer_kleinFour {z b : Y} (hz2 : z * z = 1) (hb2 : b * b = 1)
    (hzb : Commute z b) (S : Subgroup Y) (hSz : ∀ g ∈ S, g * z = z * g)
    (hSb : ∀ g ∈ S, g * b = b * g) :
    S ≤ centralizer ((CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions z b hz2 hb2 hzb :
      Subgroup Y) : Set Y) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  change h ∈ ({z * b, z, b, 1} : Set Y) at hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with hh | hh | hh | hh
  · rw [hh]
    calc z * b * g = z * (b * g) := mul_assoc _ _ _
      _ = z * (g * b) := by rw [hSb g hg]
      _ = z * g * b := (mul_assoc _ _ _).symm
      _ = g * z * b := by rw [hSz g hg]
      _ = g * (z * b) := mul_assoc _ _ _
  · rw [hh]
    exact (hSz g hg).symm
  · rw [hh]
    exact (hSb g hg).symm
  · rw [hh]
    simp

private theorem joined_to_X {X : Subgroup Y} {z : Y} (hz2 : orderOf z = 2) (hzc : z ∈ center Y)
    (hcov : ∀ y : Y, ∃ x ∈ X, x⁻¹ * y ∈ centralizer (X : Set Y))
    (hA : ∀ x ∈ X, x * x ∈ centralizer (X : Set Y) →
      ∃ A : Subgroup Y, IsKleinFour A ∧ A ≤ X ∧ A ≤ centralizer {x})
    {B : Subgroup Y} (hB : IsKleinFour B) :
    ∃ A : Subgroup Y, IsKleinFour A ∧ A ≤ X ∧
      Relation.ReflTransGen (CommFourAdj Y) B A := by
  obtain ⟨b, hbB, hb1, hbz⟩ := exists_ne_one_ne hB z
  have hz_sq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact h
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hb_sq : b * b = 1 := by
    have h := FooteLit.sq_eq_one_of_isKleinFour hB hbB
    rwa [pow_two] at h
  have hzb : Commute z b := (Subgroup.mem_center_iff.mp hzc b).symm
  have hbz' : z ≠ b := fun h => hbz h.symm
  set V : Subgroup Y :=
    CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions z b hz_sq hb_sq hzb
  have hV : IsKleinFour V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z b hz_sq hb_sq hz1 hb1
      hbz' hzb
  have hBV : CommFourAdj Y B V :=
    ⟨hB, hV, le_centralizer_kleinFour hz_sq hb_sq hzb B
      (fun g _ => Subgroup.mem_center_iff.mp hzc g)
      (fun g hg => FooteLit.commute_of_sq_eq_one
        (fun x hx => FooteLit.sq_eq_one_of_isKleinFour hB hx) hg hbB)⟩
  obtain ⟨x, hxX, hxc'⟩ := hcov b
  obtain ⟨c, hcC, hxc⟩ : ∃ c ∈ centralizer (X : Set Y), x * c = b :=
    ⟨x⁻¹ * b, hxc', mul_inv_cancel_left x b⟩
  have hcomm : ∀ g ∈ X, g * c = c * g := fun g hg => Subgroup.mem_centralizer_iff.mp hcC g hg
  have hxx : x * x ∈ centralizer (X : Set Y) := by
    have key : x * x * (c * c) = 1 := by
      calc x * x * (c * c) = x * (x * c) * c := by simp only [mul_assoc]
        _ = x * (c * x) * c := by rw [← hcomm x hxX]
        _ = (x * c) * (x * c) := by simp only [mul_assoc]
        _ = b * b := by rw [hxc]
        _ = 1 := hb_sq
    rw [eq_inv_of_mul_eq_one_left key]
    exact inv_mem (mul_mem hcC hcC)
  obtain ⟨A, hA4, hAX, hAx⟩ := hA x hxX hxx
  have hAz : ∀ g ∈ A, g * z = z * g := fun g _ => Subgroup.mem_center_iff.mp hzc g
  have hAb : ∀ g ∈ A, g * b = b * g := by
    intro g hg
    have h1 : x * g = g * x := Subgroup.mem_centralizer_iff.mp (hAx hg) x (Set.mem_singleton x)
    have h2 : g * c = c * g := hcomm g (hAX hg)
    rw [← hxc]
    calc g * (x * c) = g * x * c := (mul_assoc _ _ _).symm
      _ = x * g * c := by rw [h1]
      _ = x * (g * c) := mul_assoc _ _ _
      _ = x * (c * g) := by rw [h2]
      _ = x * c * g := (mul_assoc _ _ _).symm
  have hAV : CommFourAdj Y A V :=
    ⟨hA4, hV, le_centralizer_kleinFour hz_sq hb_sq hzb A hAz hAb⟩
  have h1 : Relation.ReflTransGen (CommFourAdj Y) B V := Relation.ReflTransGen.single hBV
  exact ⟨A, hA4, hAX, h1.tail (commFourAdj_symm hAV)⟩

private theorem reflTransGen_of_le {X : Subgroup Y}
    (hX : ∀ P Q : Subgroup X, IsKleinFour P → IsKleinFour Q →
      Relation.ReflTransGen (CommFourAdj X) P Q)
    {A C : Subgroup Y} (hA : IsKleinFour A) (hC : IsKleinFour C) (hAX : A ≤ X) (hCX : C ≤ X) :
    Relation.ReflTransGen (CommFourAdj Y) A C := by
  have h := GSYard02.reflTransGen_commFourAdj_map_injective (f := X.subtype) X.subtype_injective
    (hX (A.subgroupOf X) (C.subgroupOf X) (isKleinFour_subgroupOf_of_le hAX hA)
      (isKleinFour_subgroupOf_of_le hCX hC))
  have e : ∀ D : Subgroup Y, D ≤ X → (D.subgroupOf X).map X.subtype = D := fun D hD => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD]
  rwa [e A hAX, e C hCX] at h

theorem centralInvolutionJoin : CentralInvolutionJoin := by
  intro Y _ X z hz2 _ hzc hcov hX hA
  have hXjoin : ∀ P Q : Subgroup X, IsKleinFour P → IsKleinFour Q →
      Relation.ReflTransGen (CommFourAdj X) P Q := fun P Q hP hQ => by
    by_contra h
    exact hX ⟨P, Q, hP, hQ, h⟩
  rintro ⟨B₀, B₁, hB₀, hB₁, hnot⟩
  obtain ⟨A₀, hA₀, hA₀X, h₀⟩ := joined_to_X hz2 hzc hcov hA hB₀
  obtain ⟨A₁, hA₁, hA₁X, h₁⟩ := joined_to_X hz2 hzc hcov hA hB₁
  exact hnot (h₀.trans ((reflTransGen_of_le hXjoin hA₀ hA₁ hA₀X hA₁X).trans
    (reflTransGen_commFourAdj_symm h₁)))

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
