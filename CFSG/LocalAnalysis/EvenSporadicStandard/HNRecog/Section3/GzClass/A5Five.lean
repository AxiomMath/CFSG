module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped Classical

private def a5CentCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

private theorem a5CentCard_four :
    ∀ x : alternatingGroup (Fin 5), x ≠ 1 → x ^ 2 = 1 → a5CentCard x = 4 := by
  decide +kernel

private theorem a5CentCard_five :
    ∀ x : alternatingGroup (Fin 5), x ^ 5 = 1 → x ≠ 1 → a5CentCard x = 5 := by
  decide +kernel

private theorem card_centralizer_a5_involution {x : alternatingGroup (Fin 5)} (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    apply Finset.filter_congr
    intro y _
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  have h := a5CentCard_four x hx1 hx2
  simpa [a5CentCard] using h

private theorem card_centralizer_a5_five {x : alternatingGroup (Fin 5)} (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    apply Finset.filter_congr
    intro y _
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  have h := a5CentCard_five x hx5 hx1
  simpa [a5CentCard] using h

private theorem card_centralizer_one_a5 :
    Nat.card ↥(Subgroup.centralizer ({1} : Set (alternatingGroup (Fin 5)))) = 60 := by
  have htop : Subgroup.centralizer ({1} : Set (alternatingGroup (Fin 5))) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_center_iff.mpr fun g => by simp
  rw [htop, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

private theorem card_centralizer_one_A5WrTwo :
    Nat.card ↥(Subgroup.centralizer ({1} : Set A5WrTwo)) = 7200 := by
  have htop : Subgroup.centralizer ({1} : Set A5WrTwo) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_center_iff.mpr fun g => by simp
  rw [htop, Subgroup.card_top, natCard_A5WrTwo]

private theorem a5_coord_eq_one_of_commute {r x : alternatingGroup (Fin 5)} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hr5 : r ^ 5 = 1) (hcomm : r * x = x * r) : r = 1 := by
  have hxcard :
      Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 :=
    card_centralizer_a5_involution hx1 hx2
  have hmem : r ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have h4sub :
      (⟨r, hmem⟩ : ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5))))) ^ 4 = 1 := by
    rw [← hxcard]
    exact pow_card_eq_one'
  have hr4 : r ^ 4 = 1 := by
    have := congrArg Subtype.val h4sub
    simpa using this
  have hd4 : orderOf r ∣ 4 := orderOf_dvd_of_pow_eq_one hr4
  have hd5 : orderOf r ∣ 5 := orderOf_dvd_of_pow_eq_one hr5
  have hd1 : orderOf r ∣ 1 := by
    have h := Nat.dvd_gcd hd4 hd5
    have hg : Nat.gcd 4 5 = 1 := by norm_num
    rw [hg] at h
    exact h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

theorem card_centralizer_five {u ρ : A5WrTwo} (hu : u ∈ commutator A5WrTwo) (hu2 : u ^ 2 = 1)
    (hu240 : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 240) (hρ : orderOf ρ = 5)
    (hρu : ρ * u = u * ρ) :
    Nat.card ↥(Subgroup.centralizer ({ρ} : Set A5WrTwo)) = 300 := by
  have hu1 : u ≠ 1 := by
    intro h
    have hcard : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 7200 := by
      rw [h]
      exact card_centralizer_one_A5WrTwo
    rw [hcard] at hu240
    norm_num at hu240
  have hρker :
      ρ ∈ (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker := by
    rw [MonoidHom.mem_ker]
    have hdvd5 : orderOf (RegularWreathProduct.rightHom ρ) ∣ 5 := by
      simpa [hρ] using
        orderOf_map_dvd (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)) ρ
    have hdvd2 : orderOf (RegularWreathProduct.rightHom ρ) ∣ 2 := by
      calc orderOf (RegularWreathProduct.rightHom ρ) ∣ Nat.card (Multiplicative (ZMod 2)) :=
            orderOf_dvd_natCard _
        _ = 2 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hd1 : orderOf (RegularWreathProduct.rightHom ρ) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd5 hdvd2
      have hg : Nat.gcd 5 2 = 1 := by norm_num
      rw [hg] at h
      exact h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  have hρcomm : ρ ∈ commutator A5WrTwo := by
    rw [A5WrTwo.commutator_eq_ker]
    exact hρker
  have hρrange : ρ ∈ A5WrTwo.baseEmb.range := by
    rw [A5WrTwo.range_baseEmb]
    exact hρcomm
  rcases hρrange with ⟨⟨r1, r2⟩, hρeq⟩
  have hρ5 : ρ ^ 5 = 1 := by
    simpa only [hρ] using pow_orderOf_eq_one ρ
  have hρne : ρ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hρ
    norm_num at hρ
  have hpoweq : (r1 ^ 5, r2 ^ 5) = (1, 1) := by
    apply A5WrTwo.baseEmb_injective
    have h : A5WrTwo.baseEmb ((r1, r2) ^ 5) = 1 := by
      rw [map_pow, hρeq, hρ5]
    rw [show A5WrTwo.baseEmb (1, 1) = 1 from map_one A5WrTwo.baseEmb]
    simpa using h
  have hr1pow : r1 ^ 5 = 1 := congrArg Prod.fst hpoweq
  have hr2pow : r2 ^ 5 = 1 := congrArg Prod.snd hpoweq
  rcases baseInvolution_cases hu hu2 hu1 with
    ⟨x, hx2, hx1, hu_cases, hu240'⟩ | ⟨x, y, hx2, hy2, hx1, hy1, hueq, hu32⟩
  · rcases hu_cases with hueq | hueq
    ·
      have hcomm_pair : (r1, r2) * (x, 1) = (x, 1) * (r1, r2) := by
        apply A5WrTwo.baseEmb_injective
        rw [map_mul, map_mul, hρeq, ← hueq]
        exact hρu
      have hr1comm : r1 * x = x * r1 := by
        have := congrArg Prod.fst hcomm_pair
        simpa using this
      have hr1eq : r1 = 1 := a5_coord_eq_one_of_commute hx2 hx1 hr1pow hr1comm
      have hρbase : ρ = A5WrTwo.baseEmb (1, r2) := by
        rw [← hρeq, hr1eq]
      have hr2ne : r2 ≠ 1 := by
        intro h
        apply hρne
        rw [hρbase, h]
        exact map_one A5WrTwo.baseEmb
      have hnot : ¬ IsConj (1 : alternatingGroup (Fin 5)) r2 := by
        intro h
        exact hr2ne (isConj_one_right.mp h)
      rw [hρbase, card_centralizer_baseEmb_of_not_isConj hnot,
        card_centralizer_one_a5, card_centralizer_a5_five hr2pow hr2ne]
    ·
      have hcomm_pair : (r1, r2) * (1, x) = (1, x) * (r1, r2) := by
        apply A5WrTwo.baseEmb_injective
        rw [map_mul, map_mul, hρeq, ← hueq]
        exact hρu
      have hr2comm : r2 * x = x * r2 := by
        have := congrArg Prod.snd hcomm_pair
        simpa using this
      have hr2eq : r2 = 1 := a5_coord_eq_one_of_commute hx2 hx1 hr2pow hr2comm
      have hρbase : ρ = A5WrTwo.baseEmb (r1, 1) := by
        rw [← hρeq, hr2eq]
      have hr1ne : r1 ≠ 1 := by
        intro h
        apply hρne
        rw [hρbase, h]
        exact map_one A5WrTwo.baseEmb
      have hnot : ¬ IsConj r1 (1 : alternatingGroup (Fin 5)) := by
        intro h
        exact hr1ne (isConj_one_left.mp h)
      rw [hρbase, card_centralizer_baseEmb_of_not_isConj hnot,
        card_centralizer_a5_five hr1pow hr1ne, card_centralizer_one_a5]
  ·
    rw [hu240] at hu32
    norm_num at hu32

end CFSG.EvenSporadicStandard.HNRecog.Section3
