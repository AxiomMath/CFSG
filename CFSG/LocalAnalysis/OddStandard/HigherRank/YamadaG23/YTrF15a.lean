module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma closure_singleton_map {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    (f : Γ₁ →* Γ₂) (x : Γ₁) : closure {f x} = (closure {x}).map f := by
  rw [MonoidHom.map_closure, Set.image_singleton]

theorem f15a_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F15a ↔ gf.F15a := by
  have hSσ : (gf.map f).Sσ = gf.Sσ.map f := GFrame.map_Sσ f gf
  have hZ : (gf.map f).Z = gf.Z.map f := GFrame.map_Z f gf
  have hB : (gf.map f).B = gf.B.map f := GFrame.map_B f gf hf
  have hE : (gf.map f).E = gf.E.map f := GFrame.map_E f gf
  have hF : (gf.map f).F = gf.F.map f := GFrame.map_F f gf
  have hA : (gf.map f).A = gf.A.map f := GFrame.map_A f gf
  have hσ : (gf.map f).σ = f gf.σ := rfl
  have hBσ : ((gf.map f).B ⊔ closure {(gf.map f).σ}) =
      (gf.B ⊔ closure {gf.σ}).map f := by
    rw [hB, hσ, closure_singleton_map f gf.σ,
      ← Subgroup.map_sup gf.B (closure {gf.σ}) f]
  unfold GFrame.F15a
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    ·
      rw [hSσ, hZ, cen_map hf gf.Sσ]
      exact (Subgroup.map_injective hf).eq_iff
    ·
      rw [hSσ, hB, zSeries_map hf 2 gf.Sσ, cen_map hf gf.B]
      exact (Subgroup.map_injective hf).eq_iff
    ·
      rw [hSσ, hE, hF, zSeries_map hf 3 gf.Sσ,
        ← Subgroup.map_sup gf.E gf.F f]
      exact (Subgroup.map_injective hf).eq_iff
    ·
      rw [hSσ, hE, hF, ← Subgroup.map_sup gf.E gf.F f]
      exact secProp_map_type hf gf.Sσ (gf.E ⊔ gf.F) (fun Y => IsE 3 Y)
        (fun Y Y' _ _ e => isE_equiv e 3)
  · refine and_congr ?_ ?_
    ·
      rw [hBσ, hSσ, hB, hA, cen_map hf gf.B]
      exact secProp_maxElem_map hf gf.Sσ (cen gf.B) gf.A (gf.B ⊔ closure {gf.σ})
    ·
      rw [hBσ, hZ]
      exact secProp_map_type hf (gf.B ⊔ closure {gf.σ}) gf.Z
        (fun Y => IsQ8StarQ8 Y) (fun Y Y' _ _ e => isQ8StarQ8_equiv e)
  ·
    rw [hSσ, hZ, hA]
    exact secProp_thompsonRank_map hf gf.Sσ gf.Z gf.A

end CFSG.OddStandard.HigherRank.YamadaG23
