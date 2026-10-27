module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private theorem tableVII_fiveRows_card_d10 :
    Nat.card (Multiplicative (ZMod 2) × DihedralGroup 5) = 20 := by
  rw [Nat.card_prod, DihedralGroup.nat_card,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

private theorem tableVII_fiveRows_not_both {Y : Type*} [Group Y] (h1 : IsNonsplitDoubleCoverOfS5 Y)
    (h2 : Nonempty (Y ≃* Multiplicative (ZMod 2) × DihedralGroup 5)) : False := by
  obtain ⟨e⟩ := h2
  have hc := tableVII_card_of_shape h1
  rw [Nat.card_congr e.toEquiv, tableVII_fiveRows_card_d10] at hc
  exact absurd hc (by decide)

theorem tableVII_row5_iff [Finite G] (hT6 : TableVIFacts a z) {c t : G} (ht : t ∈ orb2B a z a)
    (hc : c ∈ tSet a z t 5 ∨ c ∈ tSet a z t 6) :
    c ∈ tSet a z t 5 ↔ 16 ∣ Nat.card ↥(Gxy a c) := by
  constructor
  · intro h5
    have h240 : Nat.card ↥(Gxy a t ⊓ Gx c) = 240 := hT6.card_stab t ht 5 c h5
    have hle : Gxy a t ⊓ Gx c ≤ Gxy a c := fun g hg =>
      mem_Gxy.2 ⟨(mem_Gxy.1 (Subgroup.mem_inf.1 hg).1).1, (Subgroup.mem_inf.1 hg).2⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [h240] at hdvd
    exact dvd_trans ⟨15, rfl⟩ hdvd
  · intro h16
    rcases hc with h5 | h6
    · exact h5
    · exfalso
      have hv := hT6.two_part_5E t ht c h6
      have hpos : Nat.card ↥(Gxy a c) ≠ 0 := Nat.card_pos.ne'
      have h16' : 2 ^ 4 ∣ Nat.card ↥(Gxy a c) := by norm_num; exact h16
      have h4 := (padicValNat_dvd_iff_le hpos).1 h16'
      omega

theorem tableVII_mem_orb5A_or_orb5E [Finite G] (h : IsF5Type a z) (hPar : ParityFacts a z)
    (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) {c : G}
    (hc : c ∈ oddSet a a) (h5 : orderOf (a * c) = 5) : c ∈ orb5A a a ∨ c ∈ orb5E a a := by
  by_cases h16 : 16 ∣ Nat.card ↥(Gxy a c)
  · refine Or.inl ⟨hc, h5, fun t ht htc => ?_⟩
    obtain ⟨htB, hrow⟩ := tableVII_five_rows h hPar hT4 hT5 hT6 hc h5 ht htc
    exact hT6.shape_5A t htB c ((tableVII_row5_iff hT6 htB hrow).2 h16)
  · refine Or.inr ⟨hc, h5, fun t ht htc => ?_⟩
    obtain ⟨htB, hrow⟩ := tableVII_five_rows h hPar hT4 hT5 hT6 hc h5 ht htc
    have h6 : c ∈ tSet a z t 6 := by
      rcases id hrow with h5' | h6'
      · exact absurd ((tableVII_row5_iff hT6 htB hrow).1 h5') h16
      · exact h6'
    exact hT6.shape_5E t htB c h6

theorem tableVII_disjoint_5A_5E : Disjoint (orb5A a a) (orb5E a a) := by
  refine Set.disjoint_left.2 fun c hA hE => ?_
  obtain ⟨hodd, -, hA'⟩ := hA
  obtain ⟨-, -, hE'⟩ := hE
  obtain ⟨-, -, -, t, ht, htc⟩ := hodd
  exact tableVII_fiveRows_not_both (hA' t ht htc) (hE' t ht htc)

theorem tableVII_row5_of_orb5A (h : IsF5Type a z) (hPar : ParityFacts a z)
    (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) {c t : G}
    (hc : c ∈ orb5A a a) (ht : IsConj a t) (htc : t ∈ Gxy a c) :
    t ∈ orb2B a z a ∧ c ∈ tSet a z t 5 := by
  obtain ⟨hodd, h5, hA⟩ := hc
  obtain ⟨htB, hrow⟩ := tableVII_five_rows h hPar hT4 hT5 hT6 hodd h5 ht htc
  refine ⟨htB, ?_⟩
  rcases hrow with h5' | h6'
  · exact h5'
  · exact (tableVII_fiveRows_not_both (hA t ht htc) (hT6.shape_5E t htB c h6')).elim

theorem tableVII_row6_of_orb5E (h : IsF5Type a z) (hPar : ParityFacts a z)
    (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) {c t : G}
    (hc : c ∈ orb5E a a) (ht : IsConj a t) (htc : t ∈ Gxy a c) :
    t ∈ orb2B a z a ∧ c ∈ tSet a z t 6 := by
  obtain ⟨hodd, h5, hE⟩ := hc
  obtain ⟨htB, hrow⟩ := tableVII_five_rows h hPar hT4 hT5 hT6 hodd h5 ht htc
  refine ⟨htB, ?_⟩
  rcases hrow with h5' | h6'
  · exact (tableVII_fiveRows_not_both (hT6.shape_5A t htB c h5') (hE t ht htc)).elim
  · exact h6'

end CFSG.EvenSporadicStandard.HNRecog.Section3
