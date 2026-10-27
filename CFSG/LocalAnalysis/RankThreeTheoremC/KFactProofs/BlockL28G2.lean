module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28G2Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28G2Torus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28NormalSection
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem kFactCompParabL28RankOn_g2
    (hGA : GriessAllModelsStatement) : KFactCompParabL28RankOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG N hNP hPN d ψ hd hψ
  obtain ⟨f, π, hπs, hπi, hQ⟩ := gtwo_exists_cover hGA hCP hG
  have : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have h504 := card_mem_of_l28Section hCP.parab.1 π hπs hQ hNP hPN ψ hd hψ
  have h8 : 2 ^ f = 8 :=
    ((ordA_eq_504_iff rfl).1 (Set.mem_singleton_iff.1 h504).symm).2
  have hF : Nat.card (GaloisField 2 f) = 8 := by
    rw [GaloisField.card 2 f (by rintro rfl; norm_num at h8), h8]
  have hu : Nat.card (GaloisField 2 f)ˣ = 7 := by rw [Nat.card_units, hF]
  refine l28_E_of_torus hu (L.subtype.comp (π.comp (gtwoTorusHom (GaloisField 2 f))))
    ((Subgroup.subtype_injective L).comp (hπi.comp (gtwoTorusHom_injective hu))) ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact (π (gtwoTorusHom (GaloisField 2 f) a)).2
  · intro a ha
    have hc : gtwoTorusHom (GaloisField 2 f) a ∈
        Subgroup.center ↥(adjointGroup .G2 (GaloisField 2 f)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hπi
      rw [map_mul, map_mul]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 ha (π g) (π g).2)
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    exact gtwoTorusHom_injective hu (hc.trans (map_one _).symm)

theorem kFactCompParabL28TwoRankOn_g2
    (hGA : GriessAllModelsStatement) : KFactCompParabL28TwoRankOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  obtain ⟨K, _, _, ρ, G, _, _, S, β, f, hρ, hker, hpi, hcomm, hqs, -, -⟩ :=
    LeviBlock.exists_leviData_g2 hGA hCP hG
  obtain ⟨j₁, j₂, hne, -⟩ := two_blocks_of_l28Section hCP.parab.1 ρ hρ
    (G := fun _ : Fin 1 => G) (S := fun _ => S) β hker hpi hcomm (fun _ => Or.inl hqs) hNP hPN
    ψ hd₁ hd₂ hψ
  exact absurd (Subsingleton.elim j₁ j₂) hne

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
