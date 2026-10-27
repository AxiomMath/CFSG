module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.CoreRho
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Shape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma fiveE_mul_self_eq_one_of_orderOf_eq_two {G : Type} [Group G] {a : G}
    (ha : orderOf a = 2) : a * a = 1 := by
  have h := pow_orderOf_eq_one a
  rw [ha, pow_two] at h
  exact h

private lemma fiveE_commute_mul_of_mem_Gxy {G : Type} [Group G] {a x l : G}
    (hl : l ∈ Gxy a x) : l * (a * x) = (a * x) * l := by
  rw [mem_Gxy] at hl
  have hla : a * l = l * a := mem_Gx.mp hl.1
  have hlx : x * l = l * x := mem_Gx.mp hl.2
  calc l * (a * x) = (l * a) * x := by rw [← mul_assoc l a x]
    _ = (a * l) * x := by rw [← hla]
    _ = a * (l * x) := by rw [mul_assoc a l x]
    _ = a * (x * l) := by rw [← hlx]
    _ = (a * x) * l := by rw [← mul_assoc a x l]

private lemma fiveE_commute_a_of_mem_Gxy {G : Type} [Group G] {a x l : G}
    (hl : l ∈ Gxy a x) : l * a = a * l := by
  rw [mem_Gxy] at hl
  exact (mem_Gx.mp hl.1).symm

private lemma fiveE_le_Gx_mul_Gxy {G : Type} [Group G] (a x : G) : Gxy a x ≤ Gx (a * x) := by
  intro l hl
  rw [mem_Gx]
  exact (fiveE_commute_mul_of_mem_Gxy hl).symm

private lemma fiveE_conj_inv_of_mul_self_eq_one {G : Type} [Group G] {a x : G}
    (ha : a * a = 1) (hx : x * x = 1) : a * (a * x) * a = (a * x)⁻¹ := by
  have h2 : (a * x)⁻¹ = x * a := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right ha]
  have h1 : a * (a * x) * a = x * a := by
    rw [← mul_assoc a a x, ha, one_mul]
  rw [h1, h2]

theorem orb5E_structure (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z) (hPar : ParityFacts a z)
    (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z)
    (hT6 : TableVIFacts a z) (hT7 : TableVIIFacts a z) (hGam : GammaFacts a z) {x : G}
    (hx : x ∈ orb5E a a) :
    Nat.card ↥(Gxy a x) = 500 ∧ IsShapeFiveCubeByTwoTwo ↥(Gxy a x) ∧
      Gx (a * x) = Gxy a x ⊔ Subgroup.zpowers (a * x) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ha2 : a * a = 1 := fiveE_mul_self_eq_one_of_orderOf_eq_two h.orderOf_a
  have hxa : IsConj a x := hx.1.1
  have hxord : orderOf x = 2 := by
    obtain ⟨c, hc⟩ := hxa
    rw [← SemiconjBy.orderOf_eq (↑c) hc, h.orderOf_a]
  have hx2 : x * x = 1 := fiveE_mul_self_eq_one_of_orderOf_eq_two hxord
  have hρ5 : orderOf (a * x) = 5 := hx.2.1
  have hinv : a * (a * x) * a = (a * x)⁻¹ := fiveE_conj_inv_of_mul_self_eq_one ha2 hx2
  have hodd : Odd (orderOf (a * x)) := by rw [hρ5]; decide
  have hρcomm : ∀ l ∈ Gxy a x, l * (a * x) = (a * x) * l :=
    fun l hl => fiveE_commute_mul_of_mem_Gxy hl
  have hacomm : ∀ l ∈ Gxy a x, l * a = a * l :=
    fun l hl => fiveE_commute_a_of_mem_Gxy hl
  have hLK : Gxy a x ≤ Gx (a * x) := fiveE_le_Gx_mul_Gxy a x
  obtain ⟨s, z', hs, hz, hsz, hsx, hz'ρ, hszcomm, hcardT0, hT0iso, N, hNK, hNn, hN5,
    hNcard_le, hsup, hinf⟩ :=
    exists_core_of_orb5E hI h hCore hPar hCls hT4 hT6 hx
  have hT : Subgroup.closure ({s, z'} : Set G) ≤ Gx (a * x) :=
    le_sup_right.trans hsup.le
  have hquot : Nonempty (↥(Gx (a * x)) ⧸ N.subgroupOf (Gx (a * x)) ≃*
      ↥(Subgroup.closure ({s, z'} : Set G))) :=
    nonempty_quotient_mulEquiv_of_complement hNK hNn hT hinf hsup
  have hcardK : Nat.card ↥(Gx (a * x)) = 4 * Nat.card ↥N := by
    obtain ⟨e⟩ := hquot
    have hq : Nat.card (↥(Gx (a * x)) ⧸ N.subgroupOf (Gx (a * x))) = 4 :=
      (Nat.card_congr e.toEquiv).trans hcardT0
    have hN : Nat.card (N.subgroupOf (Gx (a * x))) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (N.subgroupOf (Gx (a * x))), hq, hN]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 5) (G := ↥N)).mp hN5
  have hjle : j ≤ 4 := by
    have hle : 5 ^ j ≤ 5 ^ 4 := by rw [← hj]; exact hNcard_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp hle
  have hKdvd : Nat.card ↥(Gx (a * x)) ∣ 2500 := by
    have h5 : 5 ^ j ∣ 5 ^ 4 := pow_dvd_pow 5 hjle
    have h : 4 * 5 ^ j ∣ 4 * 5 ^ 4 := Nat.mul_dvd_mul_left 4 h5
    rw [hcardK, hj, show (2500 : ℕ) = 4 * 5 ^ 4 by norm_num]
    exact h
  have hKle : Nat.card ↥(Gx (a * x)) ≤ 2500 := Nat.le_of_dvd (by norm_num) hKdvd
  have hGxyz_le : Gxyz a s x ≤ Gxy a x := by
    intro g hg
    rw [mem_Gxyz] at hg
    rw [mem_Gxy]
    exact ⟨hg.1, hg.2.2⟩
  obtain ⟨e5⟩ := hx.2.2 s hs hsx
  have hcard2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardGxyz : Nat.card ↥(Gxyz a s x) = 20 := by
    rw [Nat.card_congr e5.toEquiv, Nat.card_prod, hcard2, DihedralGroup.nat_card]
  have h20 : 20 ∣ Nat.card ↥(Gxy a x) := by
    rw [← hcardGxyz]
    exact Subgroup.card_dvd_of_le hGxyz_le
  have hsupL : Nat.card ↥(Gxy a x ⊔ Subgroup.zpowers (a * x)) =
      Nat.card ↥(Gxy a x) * orderOf (a * x) :=
    card_sup_zpowers_of_inverted (L := Gxy a x) (a := a) (ρ := a * x)
      ha2 hinv hodd hρcomm hacomm
  have hsup_le : Gxy a x ⊔ Subgroup.zpowers (a * x) ≤ Gx (a * x) := by
    apply sup_le hLK
    rw [Subgroup.zpowers_le]
    exact self_mem_Gx (a * x)
  have hle500 : Nat.card ↥(Gxy a x) * 5 ≤ 2500 := by
    have h1 : Nat.card ↥(Gxy a x ⊔ Subgroup.zpowers (a * x)) ≤
        Nat.card ↥(Gx (a * x)) := Subgroup.card_le_of_le hsup_le
    rw [hsupL, hρ5] at h1
    exact h1.trans hKle
  have hle : Nat.card ↥(Gxy a x) ≤ 500 := by omega
  have hdvd : Nat.card ↥(Gxy a x) ∣ 2500 := (Subgroup.card_dvd_of_le hLK).trans hKdvd
  have hL500 : Nat.card ↥(Gxy a x) = 500 :=
    card_Gxy_eq_of_orb5E hI hU h hGam hT5 hT7 hx hdvd h20 hle
  have hKsup : Gx (a * x) = Gxy a x ⊔ Subgroup.zpowers (a * x) := by
    have hcard_le : Nat.card ↥(Gx (a * x)) ≤
        Nat.card ↥(Gxy a x ⊔ Subgroup.zpowers (a * x)) := by
      rw [hsupL, hρ5, hL500]
      omega
    exact (eq_of_le_of_card_le (K := Gx (a * x))
      (L := Gxy a x ⊔ Subgroup.zpowers (a * x)) hsup_le hcard_le).symm
  have hKN : Nonempty (↥(Gx (a * x)) ⧸ N.subgroupOf (Gx (a * x)) ≃* Elem2 2) := by
    obtain ⟨e⟩ := hquot
    obtain ⟨e2⟩ := hT0iso
    exact ⟨e.trans e2⟩
  have hshape : IsShapeFiveCubeByTwoTwo ↥(Gxy a x) :=
    isShapeFiveCubeByTwoTwo_of_le (K := Gx (a * x)) (L := Gxy a x) (N := N)
      hLK hNK hNn hN5 hKN (by rw [hL500]; norm_num)
  exact ⟨hL500, hshape, hKsup⟩

theorem isShapeFiveCubeByTwoTwo_of_orb5E (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z)
    (hPar : ParityFacts a z) (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z)
    (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) (hT7 : TableVIIFacts a z)
    (hGam : GammaFacts a z) {x : G} (hx : x ∈ orb5E a a) : IsShapeFiveCubeByTwoTwo ↥(Gxy a x) :=
  (orb5E_structure hI hU h hCore hPar hCls hT4 hT5 hT6 hT7 hGam hx).2.1

theorem mem_Gxy_of_orb5E (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z) (hPar : ParityFacts a z)
    (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z)
    (hT6 : TableVIFacts a z) (hT7 : TableVIIFacts a z) (hGam : GammaFacts a z) {x : G}
    (hx : x ∈ orb5E a a) {t : G} (ht : orderOf t = 2) (htρ : t ∈ Gx (a * x)) : t ∈ Gxy a x := by
  have hKsup : Gx (a * x) = Gxy a x ⊔ Subgroup.zpowers (a * x) :=
    (orb5E_structure hI hU h hCore hPar hCls hT4 hT5 hT6 hT7 hGam hx).2.2
  have ha2 : a * a = 1 := fiveE_mul_self_eq_one_of_orderOf_eq_two h.orderOf_a
  have hxa : IsConj a x := hx.1.1
  have hxord : orderOf x = 2 := by
    obtain ⟨c, hc⟩ := hxa
    rw [← SemiconjBy.orderOf_eq (↑c) hc, h.orderOf_a]
  have hx2 : x * x = 1 := fiveE_mul_self_eq_one_of_orderOf_eq_two hxord
  have hinv : a * (a * x) * a = (a * x)⁻¹ := fiveE_conj_inv_of_mul_self_eq_one ha2 hx2
  have hodd : Odd (orderOf (a * x)) := by rw [hx.2.1]; decide
  have hρcomm : ∀ l ∈ Gxy a x, l * (a * x) = (a * x) * l :=
    fun l hl => fiveE_commute_mul_of_mem_Gxy hl
  have hacomm : ∀ l ∈ Gxy a x, l * a = a * l :=
    fun l hl => fiveE_commute_a_of_mem_Gxy hl
  have ht2 : t * t = 1 := fiveE_mul_self_eq_one_of_orderOf_eq_two ht
  have htmem : t ∈ Gxy a x ⊔ Subgroup.zpowers (a * x) := by
    rw [← hKsup]
    exact htρ
  exact mem_of_mul_self_eq_one_of_mem_sup (L := Gxy a x) (a := a) (ρ := a * x)
    ha2 hinv hodd hρcomm hacomm htmem ht2

theorem exists_klein_of_orb5E (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z) (hPar : ParityFacts a z)
    (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z)
    (hT6 : TableVIFacts a z) (hT7 : TableVIIFacts a z) (hGam : GammaFacts a z) {x : G}
    (hx : x ∈ orb5E a a) :
    ∃ t t' : G, IsConj a t ∧ IsConj z t' ∧ IsConj z (t * t') ∧ t ∈ Gxy a x ∧ t' ∈ Gxy a x ∧
      t * t' = t' * t := by
  obtain ⟨s, z', hs, hz, hsz, hsx, hz'ρ, hszcomm, _, _, _, _, _, _, _, _, _⟩ :=
    exists_core_of_orb5E hI h hCore hPar hCls hT4 hT6 hx
  have hz'ord : orderOf z' = 2 := by
    obtain ⟨c, hc⟩ := hz
    rw [← SemiconjBy.orderOf_eq (↑c) hc, h.orderOf_z]
  have hz'L : z' ∈ Gxy a x :=
    mem_Gxy_of_orb5E hI hU h hCore hPar hCls hT4 hT5 hT6 hT7 hGam hx hz'ord hz'ρ
  exact ⟨s, z', hs, hz, hsz, hsx, hz'L, hszcomm⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
