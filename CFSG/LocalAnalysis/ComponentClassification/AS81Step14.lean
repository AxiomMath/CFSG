module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b

theorem step14_of (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step14 := by
  intro G _ _ A hB hL R hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRe, ⟨g, hg, hgc⟩, hle⟩ := h11 G A hB R hR
  obtain ⟨hR4, D, hD, hRgD, -, hZeq⟩ := exists_sylow_centerIn_eq h11 hE16 hB hL hR hg hgc
  obtain ⟨c⟩ := l34Cover_of_base h11 hB hL
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hAR : A ≤ centralizer (R : Set G) := le_centralizer_iff.mp hRA
  obtain ⟨hRD, ⟨T, hT⟩, hDeq⟩ := sylow_sup_structure hRA hR.isPGroup hD
  obtain ⟨H₁, H₂, hH₁T, hH₂T, hH₁e, hH₂e, hH₁c, hH₂c, hsupH, hinfH, -, -⟩ :=
    sylow_structure c T
  have hkerc := card_ker_eq c T
  have hTZR : ((T : Subgroup ↥A) ⊓ center ↥A).map A.subtype ≤ R := by
    rintro _ ⟨z, ⟨hzT, hzZ⟩, rfl⟩
    have h2 : IsPGroup 2 (zpowers (z : G)) := by
      have := (T.2.to_le (zpowers_le.mpr hzT)).map A.subtype
      rwa [MonoidHom.map_zpowers] at this
    exact mem_of_mem_centralizer_of_isPGroup hR z.2 (mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (mem_center_iff.mp hzZ ⟨a, ha⟩)) h2
  have hCZ : (T : Subgroup ↥A) ⊓ center ↥A ≤ centerIn (T : Subgroup ↥A) := by
    rintro z ⟨hzT, hzZ⟩
    refine ⟨hzT, ?_⟩
    show z ∈ centralizer ((T : Subgroup ↥A) : Set ↥A)
    rw [mem_centralizer_iff]
    intro s _
    exact mem_center_iff.mp hzZ s
  have hZH₁ : centerIn (T : Subgroup ↥A) ≤ H₁ := hinfH ▸ inf_le_left
  have hZH₂ : centerIn (T : Subgroup ↥A) ≤ H₂ := hinfH ▸ inf_le_right
  have hplane : ∀ H : Subgroup ↥A, H ≤ T → IsElemAbelian 2 H →
      Nat.card H = 16 * Nat.card c.π.ker → (T : Subgroup ↥A) ⊓ center ↥A ≤ H →
      IsElemAbelian 2 (H.map A.subtype ⊔ R) ∧
        Nat.card (H.map A.subtype ⊔ R : Subgroup G) = 64 := by
    intro H hHT hHe hHc hCH
    have hH'R : H.map A.subtype ≤ centralizer (R : Set G) := (map_subtype_le H).trans hAR
    refine ⟨isElemAbelian_sup_of_le_centralizer
      (RankTwoSporadic.isElemAbelian_map hHe A.subtype) hRe hH'R, ?_⟩
    have hinf : (H.map A.subtype ⊓ R : Subgroup G) =
        ((T : Subgroup ↥A) ⊓ center ↥A).map A.subtype := by
      refine le_antisymm (fun y hy => ?_) (le_inf (map_mono hCH) hTZR)
      obtain ⟨⟨h, hh, rfl⟩, hhR⟩ := hy
      exact ⟨h, ⟨hHT hh, mem_center_iff.mpr fun a =>
        Subtype.ext (mem_centralizer_iff.mp (hRA hhR) a a.2)⟩, rfl⟩
    have hprod := card_sup_mul_card_inf (H := H.map A.subtype) (R := R)
      ((le_centralizer_iff.mp hH'R).trans (Subgroup.centralizer_le_normalizer _))
    rw [hinf, card_map_of_injective A.subtype_injective,
      card_map_of_injective A.subtype_injective, hHc, ← hkerc, hR4] at hprod
    have hpos : 0 < Nat.card c.π.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hprod]; ring)
  obtain ⟨hEe, hEc⟩ := hplane H₁ hH₁T hH₁e hH₁c (hCZ.trans hZH₁)
  obtain ⟨hFe, hFc⟩ := hplane H₂ hH₂T hH₂e hH₂c (hCZ.trans hZH₂)
  have hEF : (H₁.map A.subtype ⊔ R) ⊔ (H₂.map A.subtype ⊔ R) = D := by
    rw [hDeq, ← hT, ← hsupH, Subgroup.map_sup]
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
  have hinfZ : (H₁.map A.subtype ⊔ R) ⊓ (H₂.map A.subtype ⊔ R) = centerIn D := by
    apply le_antisymm
    · intro y hy
      refine ⟨hEF ▸ mem_sup_left hy.1, ?_⟩
      show y ∈ centralizer (D : Set G)
      rw [mem_centralizer_iff]
      intro d hd
      have hcomm : (H₁.map A.subtype ⊔ R) ⊔ (H₂.map A.subtype ⊔ R) ≤
          centralizer ({y} : Set G) := by
        refine sup_le (fun e he => ?_) (fun f hf => ?_)
        · exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, he⟩ ⟨y, hy.1⟩))
        · exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (hFe.1.is_comm.comm ⟨f, hf⟩ ⟨y, hy.2⟩))
      exact mem_centralizer_singleton_iff.mp (hcomm (hEF.symm ▸ hd))
    · have hZD : centerIn D ≤ centerIn ((T : Subgroup ↥A).map A.subtype) ⊔ R := by
        rw [hT]
        exact centerIn_le_sup_of_le_sup hRA hRD hD.le
      refine hZD.trans (sup_le ?_ (le_inf le_sup_right le_sup_right))
      refine (centerIn_map_subtype_le (T : Subgroup ↥A)).trans ?_
      rw [← hinfH]
      exact le_inf ((map_mono inf_le_left).trans le_sup_left)
        ((map_mono inf_le_right).trans le_sup_left)
  have hRRg16 : Nat.card (R ⊔ rightConjugate R g : Subgroup G) ≤ 16 := by
    have h := card_sup_mul_card_inf (H := R) (R := rightConjugate R g)
      (hgc.trans (Subgroup.centralizer_le_normalizer _))
    rw [rightConjugate_card, hR4] at h
    have hpos : 0 < Nat.card (R ⊓ rightConjugate R g : Subgroup G) := Nat.card_pos
    have := Nat.le_mul_of_pos_right (Nat.card (R ⊔ rightConjugate R g : Subgroup G)) hpos
    omega
  refine ⟨g, H₁.map A.subtype ⊔ R, H₂.map A.subtype ⊔ R,
    { base := hB
      le := le_rfl
      quasisimple := hB.hyp.standard.1
      typeA₁ := hL
      sylowR := hR
      elemR := hRe
      cardR := hR4
      not_mem := hg
      comm := hgc
      conj_le := hle g hg hgc
      E_le := sup_le_sup_right (map_subtype_le H₁) R
      F_le := sup_le_sup_right (map_subtype_le H₂) R
      R_le_E := le_sup_right
      R_le_F := le_sup_right
      elemE := hEe
      elemF := hFe
      cardE := hEc
      cardF := hFc
      ne := fun h => ?_
      inf_eq := hinfZ.trans hZeq
      inf_eq_center := hinfZ.trans (congrArg centerIn hEF.symm)
      sylow := hEF ▸ hD }⟩
  have h1 : Nat.card ((H₁.map A.subtype ⊔ R) ⊓ (H₂.map A.subtype ⊔ R) : Subgroup G) = 64 := by
    rw [h, inf_idem, hFc]
  rw [hinfZ, hZeq] at h1
  omega

end CFSG.ComponentClassification.AS81
