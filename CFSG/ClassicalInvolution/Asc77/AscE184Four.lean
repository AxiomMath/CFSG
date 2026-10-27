module

public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.Asc77.AscE184SecE
public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt
public import CFSG.ClassicalInvolution.Asc77.AscE184SecC
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic AscE184Sect

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem commutator_le_oddCoreOf_of_le_centralizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K R A : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K)
    (hA : IsPGroup 2 ↥A) (hRA : R ≤ Subgroup.centralizer (A : Set G)) : ⁅A, K⁆ ≤ oddCoreOf K := by
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    have hRa : R ≤ conjSub a K := by
      intro r hr
      have h1 : a * r = r * a := Subgroup.mem_centralizer_iff.mp (hRA hr) a ha
      rw [mem_conjSub_iff]
      have : a⁻¹ * r * a = r := by rw [mul_assoc, ← h1]; group
      rw [this]
      exact hR.1 hr
    exact hΩ.eq_of_le_of_le (hΩ.conjInvariant a K hK) hK hR.2.1 (by omega) hRa hR.1
  have hAR : Commutes A R := fun a ha r hr => Subgroup.mem_centralizer_iff.mp (hRA hr) a ha
  exact lemma_3_3_member hp hq hΩ hK hR hA hAK hAR

variable (p f)

theorem e18_4C (h69 : L6_9 p f) (h611 : L6_11 p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) : E18_4C p f := by
  intro G _ _ Ω K S R W H c K' hK'tw hK'ne R' hR' hR'K' hR'S A hA2 hRA hX hS
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hRsyl : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hp hK hRR hRK
  have hR'syl : IsSylow2In R' K' := hΩ.isSylow2In_of_mem_RSet_of_le hp hK'Ω hR' hR'K'
  have hRC : R ≤ Subgroup.centralizer (A : Set G) := le_sup_left.trans hRA
  have hR'C : R' ≤ Subgroup.centralizer (A : Set G) := le_sup_right.trans hRA
  have hKm : K ∈ sectionMembers Ω A :=
    ⟨hK, commutator_le_oddCoreOf_of_le_centralizer hp hq hΩ hK hRsyl hA2 hRC⟩
  have hK'm : K' ∈ sectionMembers Ω A :=
    ⟨hK'Ω, commutator_le_oddCoreOf_of_le_centralizer hp hq hΩ hK'Ω hR'syl hA2 hR'C⟩
  have hRKA : R ∈ fixedSylows A K := ⟨hRsyl, hRC⟩
  have hR'KA : R' ∈ fixedSylows A K' := ⟨hR'syl, hR'C⟩
  have hYC : sectionHull Ω A ≤ Subgroup.centralizer (A : Set G) := sectionHull_le_centralizer Ω A
  have hYtop : sectionHull Ω A ≠ ⊤ := fun h => hX (top_le_iff.mp (h ▸ hYC))
  have hKY : secMember A K ≤ sectionHull Ω A := le_sectionHull hKm
  have hK'Y : secMember A K' ≤ sectionHull Ω A := le_sectionHull hK'm
  have hRY : R ≤ sectionHull Ω A := (le_secMember hRKA).trans hKY
  have hR'Y : R' ≤ sectionHull Ω A := (le_secMember hR'KA).trans hK'Y
  have hnorm : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (sectionHull Ω A : Set G) :=
    le_normalizer_sectionHull hΩ
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ sectionHull Ω A) (sectionHull Ω A) := by
    have := isSylow2In_inf_of_le_normalizer hS hYC hnorm
    rwa [inf_assoc, inf_eq_right.mpr hYC] at this
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hp hq hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hp hq hΩ
  have hNH : oddCoreOf (sectionHull Ω A) ≤ H :=
    c.oddCoreOf_le hEA hEM hK'tw hK'ne hR' hR'K' hR'S (sup_le hRY hR'Y)
  have hΛ := hypOmegaMod_sectionFamily hp hq hΩ hA2
  have hKA : ⁅A, K⁆ ≤ oddCoreOf K := hKm.2
  have hK'A : ⁅A, K'⁆ ≤ oddCoreOf K' := hK'm.2
  have hgen : sectionHull Ω A ≤ ⨆ L ∈ restrictFamily (sectionFamily Ω A) (sectionHull Ω A),
      L.map (sectionHull Ω A).subtype := by
    refine iSup₂_le fun L hL => ?_
    have hLY : L ≤ sectionHull Ω A := le_iSup₂_of_le L hL le_rfl
    refine le_iSup₂_of_le (L.subgroupOf (sectionHull Ω A))
      (subgroupOf_mem_restrictFamily hL hLY) ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hLY]
  have hK₁' : (secMember A K').subgroupOf (sectionHull Ω A) ∈
      twinSet (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        ((secMember A K).subgroupOf (sectionHull Ω A)) :=
    twinSet_subgroupOf hKY hK'Y (secMember_mem_twinSet hp hΩ hA2 hKm hK'm hK'tw)
  have hYH : sectionHull Ω A ≤ H :=
    c.section_le_H hYtop hΛ (AscQuot.sylowOfIsSylow2In' hSY) (subgroupOf_secMember_mem hKm) hK₁'
      (subgroupOf_ne_of_ne hKY hK'Y fun h => hK'ne (eq_of_secMember_eq hp hΩ hA2 hK'm hKm h))
      (mem_RSet_restrict (secMember_mem_sectionFamily hKm) hKY
        ((isSylow2In_secMember_iff hA2 hKA).mpr hRKA))
      (Subgroup.subgroupOf_mono _ (le_secMember hRKA))
      (Subgroup.subgroupOf_mono _ (le_inf hRS hRY))
      (mem_RSet_restrict (secMember_mem_sectionFamily hK'm) hK'Y
        ((isSylow2In_secMember_iff hA2 hK'A).mpr hR'KA))
      (Subgroup.subgroupOf_mono _ (le_secMember hR'KA))
      (Subgroup.subgroupOf_mono _ (le_inf hR'S hR'Y)) hNH hgen (c.trans_sectionFamily hA2 hKm)
      (c.cent_sectionFamily hA2 hKm) (sectionGood Ω A K) ⟨K, hKm, rfl, Relation.ReflTransGen.refl⟩
      (fun L _ L' hL' hg hadj => sectionGood_step hp hq hΩ hA2 hL' hg hadj)
      (fun L _ hg => c.sectionGood_le_H hg)
      (h3s _ c.stand.below hp hq _ (natCard_lt_of_ne_top hYtop) _ hΛ)
  exact fun x hx => c.normalizer_le_of_le hEA hEM hRY hYH (hnorm hx)

end CFSG.ClassicalInvolution.Asc77
