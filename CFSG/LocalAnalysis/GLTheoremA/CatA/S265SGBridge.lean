module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem SG.isComponentOf_fixSubgroup_chevAut {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) :
    (∀ J : Subgroup (PSimple p S), IsComponentOf J (fixSubgroup (chevAut p S ⟨d, hdN⟩)) →
      J ≤ (K.subgroupOf S).map (chevQuotHom p S)) ∧
      IsComponentOf ((K.subgroupOf S).map (chevQuotHom p S))
        (fixSubgroup (chevAut p S ⟨d, hdN⟩)) := by
  have hc := h.cfg
  obtain ⟨-, -, -, -, hKlay, hKcomp, -⟩ := hc.std
  have hcs := S171.L_cs_eq hc.prime hc.x1 hc.std hdD hdx
    fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (hc.xcen g)
  rw [hcs] at hKlay hKcomp
  have hπ := chevQuotHom_surjective p S
  have hker := (S171.ker_chevQuotHom_eq_center' hc.prime hc.comp hc.quasi).le
  have hαβ := chevAut_chevQuotHom p S ⟨d, hdN⟩
  have hfix := fixSubgroup_normalizerMonoidHom hdN
  have hg₁ : CFSG.StandardType.ggFix (chevAut p S ⟨d, hdN⟩) =
      fixSubgroup (chevAut p S ⟨d, hdN⟩) := Subgroup.ext fun _ => Iff.rfl
  have hg₂ : CFSG.StandardType.ggFix (S.normalizerMonoidHom ⟨d, hdN⟩) =
      fixSubgroup (S.normalizerMonoidHom ⟨d, hdN⟩) := Subgroup.ext fun _ => Iff.rfl
  refine ⟨fun J hJ => ?_, ?_⟩
  · rw [← hg₁, ← CFSG.Assembly.isComponentOf_iff_open] at hJ
    obtain ⟨hQ, hQJ⟩ := CFSG.StandardType.USixTwo.isComponentOf_lift_fix hπ hker hαβ hJ
    rw [hg₂, hfix, CFSG.Assembly.isComponentOf_iff_open] at hQ
    have hQΩ := I142N.isComponentOf_map S.subtype
      (fun g hg => by rw [S.subtype_injective (hg.trans (map_one S.subtype).symm)]; exact one_mem _)
      hQ
    have hSC : ((S ⊓ Subgroup.centralizer ({d} : Set Ω)).subgroupOf S).map S.subtype =
        S ⊓ Subgroup.centralizer ({d} : Set Ω) := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 inf_le_left
    rw [hSC] at hQΩ
    have hle : (⁅J.comap (chevQuotHom p S), J.comap (chevQuotHom p S)⁆).map S.subtype ≤ K := by
      rw [hKlay]
      exact le_sSup hQΩ
    rw [← hQJ]
    exact Subgroup.map_mono (Subgroup.map_le_iff_le_comap.1 hle)
  · have hK : IsComponentOf (K.subgroupOf S) (fixSubgroup (S.normalizerMonoidHom ⟨d, hdN⟩)) := by
      rw [hfix]
      exact ⟨Subgroup.subgroupOf_mono S hKcomp.1, hKcomp.2.1.comap S.subtype,
        hKcomp.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hKcomp.1.trans inf_le_left))⟩
    rw [← hg₂, ← CFSG.Assembly.isComponentOf_iff_open] at hK
    have h2 := CFSG.StandardType.USixTwo.isComponentOf_map_fix hπ hker hαβ hK
    rwa [hg₁, CFSG.Assembly.isComponentOf_iff_open] at h2

theorem SG.glaLayer_fixSubgroup_chevAut {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) :
    GLALayer (fixSubgroup (chevAut p S ⟨d, hdN⟩)) = (K.subgroupOf S).map (chevQuotHom p S) := by
  obtain ⟨h1, h2⟩ := SG.isComponentOf_fixSubgroup_chevAut h hdD hdx hdN
  exact le_antisymm (sSup_le fun J hJ => h1 J hJ) (le_sSup h2)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
