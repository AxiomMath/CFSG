module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURPerfect
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPump

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Certified

namespace HeKMUR

variable {X : Type} [Group X] [Finite X]

theorem false_of_le_centralizer_conjugate (hS : SchreierFor Blueprint.Catalog)
    {L M N : Subgroup X} {a u w : X} (hset : HeldEndSetting X L)
    (hLa : L ≤ centralizer ({a} : Set X)) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hw2 : orderOf w = 2) (huw : u * w = w * u) (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))))
    (hMN : M ≤ N ⊔ conjugate N u) (hNu : conjugate N u ≠ N)
    (hMaw : conjugate M a ≤ centralizer ({w} : Set X)) : False := by
  obtain ⟨⟨hsimple, hnab, hK, -⟩, -, -, ⟨eL⟩, -⟩ := id hset
  have huMM : u ∈ M ⊔ conjugate M a := by
    have h1 := mem_gsFixedLayer_self ⟨eL⟩ hu
    rw [← hfix] at h1
    exact ((gsFixedLayer_le_inf _ a).trans inf_le_left) h1
  have haCu : a ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hMau : conjugate M a ≤ centralizer ({u} : Set X) :=
    UnbalancedCorr.conjugate_le_of_mem hMu haCu
  have hMap : IsPComponent 2 ((conjugate M a).subgroupOf (centralizer ({u} : Set X))) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf haCu hMp
  have hMa2 : IsPComponent 2 ((conjugate M a).subgroupOf
      (centralizer ({u} : Set X) ⊓ centralizer ({w} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le (le_inf hMau hMaw) inf_le_left hMap
  have hwZ : w ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnab hw2
  have htop : centralizer ({w} : Set X) ≠ ⊤ := fun h => hwZ (mem_center_iff.mpr fun g =>
    mem_centralizer_singleton_iff.mp (h ▸ mem_top g : g ∈ centralizer ({w} : Set X)))
  obtain ⟨P, hPw, hPp, hMaP, -⟩ := HeK.exists_pump hS hK hu.2.1 huw htop (le_inf hMau hMaw) hMa2
  have huCw : u ∈ centralizer ({w} : Set X) := mem_centralizer_singleton_iff.mpr huw
  have hnorm : ∀ Q : Subgroup X, Q ≤ centralizer ({w} : Set X) →
      IsPComponent 2 (Q.subgroupOf (centralizer ({w} : Set X))) →
      Q ≤ normalizer (N : Set X) := by
    intro Q hQw hQp
    by_cases hQN : N = Q
    · rw [← hQN]
      exact le_normalizer
    · exact (GrS5.commutator_le_of_ne hNw hQw hNp hQp hQN).2
  have hNuN := hnorm _ (UnbalancedCorr.conjugate_le_of_mem hNw huCw)
    (UnbalancedCorr.isPComponent_conjugate_subgroupOf huCw hNp)
  have hPN := hnorm P hPw hPp
  have hPuN := hnorm _ (UnbalancedCorr.conjugate_le_of_mem hPw huCw)
    (UnbalancedCorr.isPComponent_conjugate_subgroupOf huCw hPp)
  have hMN' : M ≤ normalizer (N : Set X) := hMN.trans (sup_le le_normalizer hNuN)
  have hMaN : conjugate M a ≤ normalizer (N : Set X) :=
    hMaP.trans (inf_le_left.trans (sup_le hPN hPuN))
  have huN : u ∈ normalizer (N : Set X) := sup_le hMN' hMaN huMM
  apply hNu
  ext y
  rw [UnbalancedLayer.mem_conjugate_iff]
  exact (mem_normalizer_iff.mp huN y).symm

end HeKMUR

end Certified

end CFSG.ComponentClassification.GrSLit
