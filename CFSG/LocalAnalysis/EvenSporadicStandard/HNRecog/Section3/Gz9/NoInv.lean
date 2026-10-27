module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

private theorem natCard_Gbar {G : Type} [Group G] {z : G} (e : Gbar z ≃* A5WrTwo) :
    Nat.card (Gbar z) = 7200 := by
  rw [Nat.card_congr e.toEquiv, natCard_A5WrTwo]

theorem gz9_no_involution {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hNo : GzNoFacts a z) (t : ↥(Gx z)) (ht : t ∈ commutator ↥(Gx z)) (ht2 : t ^ 2 = 1) :
    ¬ Nonempty (↥(Subgroup.centralizer ({barOf z t} : Set (Gbar z)) ⊓
        (commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))) ≃*
      Elem2 2 × alternatingGroup (Fin 5)) := by
  rintro ⟨φ⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  haveI : Finite (Gbar z) := Finite.of_equiv _ e.symm.toEquiv
  have hL : (commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) =
      commutator (Gbar z) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hu : barOf z t ∈ commutator (Gbar z) := by
    rw [← hL]
    exact Subgroup.mem_map_of_mem _ ht
  have hu2 : (barOf z t) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ht2, QuotientGroup.mk_one]
  have h240 : Nat.card ↥(Subgroup.centralizer ({barOf z t} : Set (Gbar z)) ⊓
      (commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))) = 240 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, card_Elem2_eq 2, nat_card_alternatingGroup,
      Nat.card_fin]
    norm_num [Nat.factorial]
  have hindex : (commutator (Gbar z)).index = 2 := by
    rw [← Subgroup.index_map_equiv (H := commutator (Gbar z)) e]
    have hmap : (commutator (Gbar z)).map (e : Gbar z →* A5WrTwo) = commutator A5WrTwo := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [hmap, A5WrTwo.index_commutator]
  have hcardComm : Nat.card ↥(commutator (Gbar z)) = 3600 := by
    have hc := Subgroup.card_mul_index (commutator (Gbar z))
    rw [hindex, natCard_Gbar e] at hc
    omega
  have hu1 : barOf z t ≠ 1 := by
    intro h1
    have htop : Subgroup.centralizer ({barOf z t} : Set (Gbar z)) = ⊤ := by
      rw [h1]
      simp
    have h240L : Nat.card ↥((commutator ↥(Gx z)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))) = 240 := by
      have h := h240
      rw [htop, top_inf_eq] at h
      exact h
    have h3600 : Nat.card ↥((commutator ↥(Gx z)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))) = 3600 := by
      rw [hL]
      exact hcardComm
    rw [h3600] at h240L
    omega
  rcases involution_cases_of_mulEquiv e hu2 hu1 with ⟨hn, -⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
  · exact hn hu
  · have heq : Subgroup.centralizer ({barOf z t} : Set (Gbar z)) ⊓
        (commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) =
        Subgroup.centralizer ({barOf z t} : Set (Gbar z)) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hNo.no_twoTwoA5 ⟨t, by simpa using congrArg Subtype.val ht2,
      ⟨(MulEquiv.subgroupCongr heq.symm).trans φ⟩⟩
  · have hle := Subgroup.card_le_of_le
        (H := Subgroup.centralizer ({barOf z t} : Set (Gbar z)) ⊓
          (commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))))
        (K := Subgroup.centralizer ({barOf z t} : Set (Gbar z))) inf_le_left
    rw [h240, hc] at hle
    omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
