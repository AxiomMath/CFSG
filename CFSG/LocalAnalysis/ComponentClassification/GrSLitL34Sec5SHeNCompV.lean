module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURDiagR
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeThird
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeNT

variable {X : Type} [Group X] [Finite X]


theorem isPComponent_of_center (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hD : L34RankTwoCentralFixedInput) {L : Subgroup X} (hset : HeldEndSetting X L) {a u : X}
    {M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {v : X}
    (hv2 : orderOf v = 2) (hvM : v ∈ M) (hvZ : ∀ m ∈ M, v * m = m * v) :
    M ≤ centralizer ({v} : Set X) ∧ IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hsimp, hnab, hK, -⟩, -⟩ := id hset
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv2
    norm_num at hv2
  have hvtop := HeKC.centralizer_ne_top hsimp hnab hv1
  obtain ⟨htype, z₁, hz₁, z₂, hz₂, hs₁, hs₂, hn₁, hn₂, hz, hcz⟩ :=
    HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  obtain ⟨hMN, -, -, hMq, -⟩ := diag_data ha hLa hu hMu hMp hne hfix hc
  have hMv : M ≤ centralizer ({v} : Set X) := fun m hm =>
    mem_centralizer_singleton_iff.mpr (hvZ m hm).symm
  have hMuv : M ≤ centralizer ({u} : Set X) ⊓ centralizer ({v} : Set X) := le_inf hMu hMv
  have huv : u * v = v * u := (mem_centralizer_singleton_iff.mp (hMu hvM)).symm
  obtain ⟨N, hNv, hNp, hMNc, hMNcp, hle, -, heq⟩ := HeK.exists_pump hS hK hu.2.1 huv hvtop hMuv
    (UnbalancedCorr.isPComponent_subgroupOf_of_le hMuv inf_le_left hMp)
  by_cases hNc : conjugate N u = N
  · have hNN : N ⊔ conjugate N u = N := by rw [hNc, sup_idem]
    have hMNc' : M ≤ N ⊓ centralizer ({u} : Set X) := hNN ▸ hMNc
    have hMNcp' : IsPComponent 2 (M.subgroupOf (N ⊓ centralizer ({u} : Set X))) := hNN ▸ hMNcp
    rcases lt_or_eq_of_le hle with hlt | heqi
    ·
      exact (HeK.false_of_proper_fixed_l34 hD hK hu.2.1 hvtop hNv hNp hNc hMNc' hMNcp' hlt htype
        hz₁ hz₂ hs₁ hs₂ hn₁ hn₂ hz hcz hvM hv2).elim
    ·
      have hMO := heq heqi hNc.symm
      have hMN' : M ≤ N := hMNc'.trans inf_le_left
      obtain ⟨E, hEv, hEM, hEe, hE8, hWE⟩ :=
        HeKMU.exists_elem_eight_wGroup hset ha hLa hLc hu hMu hMp hne hfix hc hv2 hMv
      have hM2 : 2 ∣ Nat.card M := by
        have hcard := CatLeaf.card_of_isL34Type htype
        have hd := Subgroup.card_quotient_dvd_card (Open.fusionZStar ↥M)
        rw [hcard] at hd
        exact (show 2 ∣ 20160 by norm_num).trans hd
      have hNM := HeKMU.eq_of_sup_oddCore hS hUO hheld hsimp hnab hK hv2 hMq hM2 hNv hNp hMN'
        hMO hEv hEM hEe hE8 hWE
      rw [← hNM]
      exact ⟨hNv, hNp⟩
  ·
    have hMav : conjugate M a ≤ centralizer ({v} : Set X) := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hMN v hvM y hy).symm
    exact (HeKMUR.false_of_le_centralizer_conjugate hS hset hLa hu hMu hMp hfix hv2 huv hNv hNp
      (hMNc.trans inf_le_left) hNc hMav).elim

end HeNT

end CFSG.ComponentClassification.GrSLit
