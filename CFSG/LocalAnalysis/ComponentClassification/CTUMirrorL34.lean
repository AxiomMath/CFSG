module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMPHeld
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCyclic

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem gsMirrorMaximal_of_properFixed (hS : SchreierFor Blueprint.Catalog) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (τ : Subgroup G → Prop)
    (hτ : ∀ A B : Subgroup G, Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) →
      τ A → τ B)
    (hPF : ∀ (a b : G) (M T : Subgroup G), orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      M ≤ centralizer ({b} : Set G) → IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) →
      conjugate M a = M → T ≤ M ⊓ centralizer ({a} : Set G) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))) →
      (pPrimeCore 2 T).index < (pPrimeCore 2 M).index → τ T → False)
    {J : Subgroup G} (hJ : τ J) : GSMirrorMaximal J := by
  have hZ : ∀ s : G, orderOf s = 2 → s ∉ center G := fun s hs =>
    GSLit.not_mem_center_of_orderOf_eq_two hnonab hs
  intro M hR
  induction hR with
  | refl => exact ⟨MulEquiv.refl _⟩
  | @tail Y X _ hst ih =>
    obtain ⟨e⟩ := ih
    have hτY : τ Y := hτ J Y ⟨e⟩ hJ
    rcases hst with ⟨c, d, hW⟩ | hM | ⟨g, rfl⟩
    · rcases GrSLit.gsWeakCorr_type_dichotomy hS hK hW (hZ d hW.2.1) with he |
        ⟨hMa, hTM, hTp, hlt, ⟨eT⟩⟩
      · obtain ⟨e'⟩ := he
        exact ⟨e.trans e'⟩
      · exact (hPF c d X _ hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.2.2.1 hW.2.2.2.2.2.2.1 hMa hTM hTp hlt
          (hτ Y _ ⟨eT⟩ hτY)).elim
    · obtain ⟨z, s, D, hz, hs, hzs, hYz, hYs, hX, hD, hDY, hDX⟩ := hM
      by_cases hfree : conjugate X z ≠ X ∨ z ∈ coreActionKernel X
      · obtain ⟨e'⟩ := mirror_fusionZStar_equiv_of_free hz hs hzs hYz hYs hX hD hDY hDX hfree
        exact ⟨e.trans e'⟩
      · obtain ⟨hXz, hzX⟩ := not_or.mp hfree
        have hXz' : conjugate X z = X := not_not.mp hXz
        obtain ⟨hTM, hTpc, hlt⟩ := properFixed_of_badShape hz hzs hX hD hDX hXz' hzX
        obtain ⟨eDY⟩ := diagonal_fusionZStar_equiv hs hzs hYz hYs hD hDY
        exact (hPF z s X D hz hs hzs hX.1 hX.2 hXz' hTM hTpc hlt
          (hτ Y D ⟨eDY.symm⟩ hτY)).elim
    · obtain ⟨e'⟩ := GrSLit.nonempty_fusionZStar_equiv_conjugate Y g
      exact ⟨e.trans e'⟩

end CFSG.ComponentClassification.Foote5.SolMax

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem false_of_properFixed_l34 (hCT : L34ProperFixedCenterTrivial)
    (hPFS : L34ProperFixedSimpleRank) (hEx : L34CyclicPumpUpExclusion) {G : Type} [Group G]
    [Finite G] (hG : L34BaseSetting G) (a b : G) (M T : Subgroup G) (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index)
    (htype : IsL34Type (T ⧸ Open.fusionZStar T)) : False := by
  obtain ⟨hsimple, hna, hK, -, -, -, hHe, -⟩ := id hG
  have := hsimple
  by_cases hr : pRank 2 ↥(Open.fusionZStar ↥T) ≤ 1
  · exact hEx G hG a b M T ha hb hab hMb hMp hMa hTM hTp hlt htype hr
  · have hbtop : centralizer ({b} : Set G) ≠ ⊤ := fun htop =>
      GSLit.not_mem_center_of_orderOf_eq_two hna hb
        (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (htop ▸ mem_top g))
    exact false_of_proper_fixed_rank hCT hPFS hK ha hbtop hMb hMp
      ⟨fun eH => hHe ⟨b, M, hb, hMb, hMp, ⟨eH⟩⟩⟩ hMa hTM hTp hlt htype (by omega)

theorem gsMirrorMaximal_of_cyclicExclusion (hS : SchreierFor Blueprint.Catalog)
    (hCT : L34ProperFixedCenterTrivial) (hPFS : L34ProperFixedSimpleRank)
    (hEx : L34CyclicPumpUpExclusion) {G : Type} [Group G] [Finite G] (hG : L34BaseSetting G)
    {K : Subgroup G} (htype : IsL34Type (K ⧸ Open.fusionZStar K)) : GSMirrorMaximal K := by
  obtain ⟨hsimple, hna, hK, -⟩ := id hG
  have := hsimple
  exact Foote5.SolMax.gsMirrorMaximal_of_properFixed hS hna hK
    (fun A => IsL34Type (A ⧸ Open.fusionZStar A))
    (fun _ _ ⟨e⟩ h => LieType.CurtisTits.lieModel_of_mulEquiv e h)
    (fun a b M T ha hb hab hMb hMp hMa hTM hTp hlt hT =>
      false_of_properFixed_l34 hCT hPFS hEx hG a b M T ha hb hab hMb hMp hMa hTM hTp hlt hT)
    htype

end CFSG.ComponentClassification.GrSLit.L34Sec5S
