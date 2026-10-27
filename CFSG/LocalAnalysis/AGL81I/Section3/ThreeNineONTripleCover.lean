module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGen
public import CFSG.RankThree.Native.ONTripleCentGen
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree

open CFSG.Open Subgroup
open CFSG.RankThree.Native.ONTriple (GM zG)
open CFSG.RankThree.PartTwo

attribute [local irreducible] dotProduct

theorem onTripleCoverFacts_holds :
    ONTripleCoverFacts := by
  intro L _ _ hq hZ ⟨e⟩
  have hperf : Group.IsPerfect L := hq.1
  obtain ⟨eON⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf ⟨hZ, ⟨e.trans eON.symm⟩⟩
  refine ⟨fun x hx => Sec13.ON134.pow_three_eq_one ψ (k := 2) (by norm_num; exact hx), ?_, ?_⟩
  · obtain ⟨D, hDe, hDc⟩ := Sec4.Res417Five.exists_isE27_model
    refine ⟨D.map ψ.symm.toMonoidHom, hDe.map _, ?_⟩
    rw [card_map_of_injective ψ.symm.injective, hDc]
    norm_num
  · intro F hF hc hz
    set F' : Subgroup GM := F.map ψ.toMonoidHom with hF'
    have hz' : F' ⊓ zpowers zG = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨f, hf, rfl⟩, hfz⟩
      have hfc : f ∈ center L := (Sec13.ON134.mem_center_iff_model ψ).2 hfz
      have hfF : f ∈ F ⊓ center L := ⟨hf, hfc⟩
      rw [hz, mem_bot] at hfF
      rw [mem_bot, hfF, map_one]
    have htop := CFSG.RankThree.Native.ONTriple.iSup_centralizer_E9 (hF.map ψ.toMonoidHom)
      (by rw [card_map_of_injective ψ.injective, hc]; norm_num) hz'
    set T := ⨆ (f : L) (_ : f ∈ F) (_ : f ≠ 1), centralizer ({f} : Set L) with hT
    have hle : ⨆ (f : GM) (_ : f ∈ F') (_ : f ≠ 1), centralizer ({f} : Set GM) ≤
        T.map ψ.toMonoidHom := by
      refine iSup_le fun f => iSup_le fun hf => iSup_le fun hf1 => ?_
      obtain ⟨f₀, hf₀, rfl⟩ := hf
      have hf₀1 : f₀ ≠ 1 := by
        rintro rfl
        exact hf1 (map_one _)
      intro g hg
      refine ⟨ψ.symm g, mem_iSup_of_mem f₀ (mem_iSup_of_mem hf₀ (mem_iSup_of_mem hf₀1 ?_)), ?_⟩
      · rw [mem_centralizer_singleton_iff] at hg ⊢
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hg
      · simp
    rw [eq_top_iff]
    intro x _
    have hx : ψ x ∈ T.map ψ.toMonoidHom := hle (htop ▸ mem_top (ψ x))
    obtain ⟨y, hy, hyx⟩ := hx
    rw [show y = x from ψ.injective hyx] at hy
    exact hy

end CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree
