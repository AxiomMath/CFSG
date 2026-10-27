module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CharTwoOver
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_minParabolic_lift_of_le (hX : GNSetting X T) {R : Subgroup X} (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {Hs Ms : Subgroup (X ⧸ gnC T)}
    (hmin : MinParabolic Hs (R.map (QuotientGroup.mk' (gnC T))) Ms) :
    ∃ H M : Subgroup X, MinParabolic H R M ∧ CharTwo H ∧ R ≤ H ∧
      H.map (QuotientGroup.mk' (gnC T)) = Hs := by
  set π := QuotientGroup.mk' (gnC T)
  set H₀ : Subgroup X := Hs.comap π
  have hRH₀ : R ≤ H₀ := fun r hr => hmin.isSylow.1 ⟨r, hr, rfl⟩
  have hmapH₀ : H₀.map π = Hs :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hker : π.ker = gnC T := QuotientGroup.ker_mk' _
  have hCH : gnC T ≤ H₀ := fun x hx => by
    show π x ∈ Hs
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact Hs.one_mem
  have hRC : R ⊓ gnC T = T ⊓ gnC T :=
    le_antisymm (inf_le_inf_right _ hRT) (le_inf hCR inf_le_right)
  have hK : IsSylowTwoOf (R ⊓ π.ker) (H₀ ⊓ π.ker) := by
    rw [hker, hRC, inf_eq_right.mpr hCH]
    exact A4.isSylowTwoOf_inf_normal hX.sylow le_top
      (fun x _ => (Subgroup.normalizer_eq_top_iff.mpr (gnC_normal T)).symm ▸ Subgroup.mem_top x)
  have hRp : IsPGroup 2 R := hX.sylow.2.1.to_le hRT
  have hSyl : IsSylowTwoOf R H₀ :=
    CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_map_ker π hRH₀ hRp hK
      (hmapH₀ ▸ hmin.isSylow)
  obtain ⟨H₁, M₁, hRH₁, -, hmap, hmin₁⟩ :=
    exists_minParabolic_of_map_minParabolic (gnC T) hSyl (by rw [hmapH₀]; exact hmin)
  exact ⟨H₁, M₁, hmin₁, charTwo_of_pCoreOf_le hX (hQR.trans hRH₁), hRH₁, hmap.trans hmapH₀⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
