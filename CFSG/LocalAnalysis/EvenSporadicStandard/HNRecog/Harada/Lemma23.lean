module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.IndexTwo

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

theorem card_subtype_eq_of_iff {P : V6 → Prop} {F : Finset V6} (h : ∀ v, P v ↔ v ∈ F) :
    Nat.card {v : V6 // P v} = F.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_coe]

private lemma zmod_two_eq_of_eq_one_iff {a b : ZMod 2} (h : a = 1 ↔ b = 1) : a = b := by
  revert a b
  decide

private lemma lam_tv_eq_zero : lam tv = 0 := by
  simp [lam, tv, Pi.single_eq_of_ne]

private lemma isConj_conj_iff' (t x n : G) : IsConj t (n * x * n⁻¹) ↔ IsConj t x := by
  constructor
  · intro h
    exact h.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩)
  · intro h
    exact h.trans (isConj_iff.mpr ⟨n, by group⟩)

theorem inducedGroup_le_orthOf (hι : Function.Injective ι) {q : V6 → ZMod 2}
    (hq : ∀ v, IsConj t (coordElt ι v) ↔ q v = 1) : inducedGroup ι ≤ OrthOf q := by
  intro g hg
  have hadd := isAddPerm_of_mem_inducedGroup hι hg
  obtain ⟨n, _hn, hn⟩ := hg
  refine ⟨hadd, fun x => ?_⟩
  have hconj : IsConj t (coordElt ι (g x)) ↔ IsConj t (coordElt ι x) := by
    rw [← hn x]
    exact isConj_conj_iff' t (coordElt ι x) n
  exact zmod_two_eq_of_eq_one_iff ((hq (g x)).symm.trans (hconj.trans (hq x)))

theorem HData.exists_lam_one_isConj [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    ∃ v : V6, lam v = 1 ∧ IsConj t (coordElt ι v) := by
  obtain ⟨_u, _hu, _hu', _hu2, _hut, _huz, _hcard, _hnz, w, hwS, hwE, hw2, hwconj⟩ :=
    harada_lemma_2_2 hnonab hD
  have hwC : w ∈ centralizer ({t} : Set G) := hD.S_le_centralizer hwS
  obtain ⟨h, _hhC, hhb | hhz⟩ := hD.inv_outer w hwC hw2 hwE
  · obtain ⟨v, hvcoord, hvl, _hvq⟩ := hD.coords_b
    exact ⟨v, hvl, by rw [hvcoord, ← hhb]; exact (isConj_conj_iff' t w h).mpr hwconj⟩
  · obtain ⟨v, hvcoord, hvl, _hvq⟩ := hD.coords_z₁
    exact ⟨v, hvl, by rw [hvcoord, ← hhz]; exact (isConj_conj_iff' t w h).mpr hwconj⟩

theorem HData.not_X48 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD : HData G t z b z₁ S Eg T T' W0 ι)
    (hX : ∀ v, IsConj t (coordElt ι v) ↔ v ∈ X48) : False := by
  obtain ⟨w0, hw0lam, hw0conj⟩ := HData.exists_lam_one_isConj hnonab hD
  obtain ⟨n, hn, hnt⟩ :=
    hD.exists_normalizer_conj_t (x := coordElt ι w0) ⟨Multiplicative.ofAdd w0, rfl⟩ hw0conj
  obtain ⟨g, hgadd, hgv⟩ := exists_perm_of_mem_normalizer hD.injective_ι hn
  have hstab : ∀ x, g x ∈ X48 ↔ x ∈ X48 := by
    intro x
    rw [← hX (g x), ← hX x]
    have hconj : IsConj t (coordElt ι (g x)) ↔ IsConj t (coordElt ι x) := by
      rw [← hgv x]
      exact isConj_conj_iff' t (coordElt ι x) n
    exact hconj
  have hgtv : g tv = tv := rigid_X48 g hgadd hstab
  have hcoord : coordElt ι (g tv) = coordElt ι w0 := by
    rw [← hgv tv, hD.ι_tv, hnt]
  have hg_eq : g tv = w0 := Multiplicative.ofAdd.injective (hD.injective_ι hcoord)
  have hw0_eq : w0 = tv := by rw [← hg_eq, hgtv]
  have hzero : lam w0 = 0 := by rw [hw0_eq, lam_tv_eq_zero]
  exact absurd (hzero ▸ hw0lam : (0 : ZMod 2) = 1) (by decide)

theorem harada_lemma_2_3 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    ((∀ v, IsConj t (coordElt ι v) ↔ qm v = 1) ∧ inducedGroup ι = OmegaMinus) ∨
      ((∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) ∧ inducedGroup ι = OmegaPlus) := by
  obtain ⟨u, _hu, _hu', _hu2, hut, _huz, _hcard, hnz, _houter⟩ := harada_lemma_2_2 hnonab hD
  have htz : IsConj t (t * z) := isConj_iff.mpr ⟨u, hut⟩
  have hex : ∃ v : V6, lam v = 1 ∧ IsConj t (coordElt ι v) :=
    HData.exists_lam_one_isConj hnonab hD
  rcases hD.X_cases_lemma23 hnz htz hex with hX | hX | hX
  · left
    have hq : ∀ v, IsConj t (coordElt ι v) ↔ qm v = 1 := fun v => (hX v).trans (by simp [X36])
    have hle : inducedGroup ι ≤ OrthMinus := inducedGroup_le_orthOf hD.injective_ι hq
    have hcardX : Nat.card {v : V6 // IsConj t (coordElt ι v)} = 36 := by
      rw [card_subtype_eq_of_iff hX, card_X36]
    have hc : Nat.card (inducedGroup ι) = 25920 := by
      have h := hD.card_inducedGroup
      rw [hcardX] at h
      omega
    exact ⟨hq, eq_omegaMinus_of_card hle hc⟩
  · right
    have hq : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1 := fun v => (hX v).trans (by simp [X28])
    have hle : inducedGroup ι ≤ OrthPlus := inducedGroup_le_orthOf hD.injective_ι hq
    have hcardX : Nat.card {v : V6 // IsConj t (coordElt ι v)} = 28 := by
      rw [card_subtype_eq_of_iff hX, card_X28]
    have hc : Nat.card (inducedGroup ι) = 20160 := by
      have h := hD.card_inducedGroup
      rw [hcardX] at h
      omega
    exact ⟨hq, eq_omegaPlus_of_card hle hc⟩
  · exact (HData.not_X48 hnonab hD hX).elim

end CFSG.EvenSporadicStandard.HNRecog.Harada
