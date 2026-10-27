module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalInSitu
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalOuter
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalModel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalAutCent
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalSolv
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalLevi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.AGLEmbedding.KlingenSpFour
  CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem exists_siegel_data {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (K : Subgroup Y) [K.Normal] (hC : Subgroup.centralizer (K : Set Y) = ⊥) (ψ : K ≃* PSp4 p)
    (T : Sylow p Y) :
    Nat.card (Y ⧸ K) ∣ 2 ∧ ∃ U : Subgroup Y, SiegelRadicalData p K (T : Subgroup Y) U ∧
      SiegelModuleData K U ∧
      (¬ Subgroup.normalizer (U : Set Y) ⊓ K ≤
        Subgroup.normalizer ((T : Subgroup Y) : Set Y)) ∧
      (p = 3 → Group.IsSolvable ↥(Subgroup.normalizer (U : Set Y) ⊓ K)) := by
  have hp : p.Prime := Fact.out
  have hqdvd : Nat.card (Y ⧸ K) ∣ 2 := card_quotient_dvd_two_of_psp4 hp2 K hC ψ
  refine ⟨hqdvd, ?_⟩
  have hTK : (T : Subgroup Y) ≤ K := by
    refine le_of_isPGroup_of_not_dvd_card_quotient K T.isPGroup' fun hdvd => hp2 ?_
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hdvd.trans hqdvd)
  obtain ⟨ι, hι, hrange, hTι⟩ := exists_embedding ψ T hTK
  subst hrange
  have hdata := (siegelRadicalData_psp4 p hp2).map ι hι
  rw [hTι] at hdata
  have hmod := SiegelModuleData.of_model (U := (xS p).U) ι hι hC (irred_xS p hp2 · · ·)
    (autCent_xS p hp2)
  refine ⟨(xS p).U.map ι, hdata, hmod, ?_, fun hp3 => ?_⟩
  · intro hle
    obtain ⟨x, hxN, hxT⟩ := SetLike.not_le_iff_exists.mp
      (not_normalizer_xS_le_normalizer_projUnipotent p hp2 (projUnipotent 2 (ZMod p)) rfl)
    refine hxT ?_
    have h1 : ι x ∈ Subgroup.normalizer (((xS p).U.map ι : Subgroup Y) : Set Y) ⊓ ι.range := by
      rw [normalizer_map_inf_range hι]
      exact ⟨x, hxN, rfl⟩
    have h2 := hle h1
    rw [← hTι] at h2
    exact (mem_normalizer_map_iff hι _ x).mp h2
  · subst hp3
    rw [normalizer_map_inf_range hι, normalizer_xS 3 hp2]
    have hsol := isSolvable_projStabilizer_two_three
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (projStabilizer 2 (ZMod 3) (flag 2 (ZMod 3) 2)) ι
        hι).toMonoidHom) (MulEquiv.surjective _)

theorem kFactKlingenFiveLocal_holds : KFactKlingenFiveLocal := by
  intro p _ hp5 d hd Y _ _ K hK he hC T B Y₀ hBT hB hBc hY₀ hne
  haveI := hK
  obtain ⟨e⟩ := he
  have hp2 : p ≠ 2 := by omega
  have hdSp : IsSpFourIndex p d := by
    rcases hd with hd | ⟨hp3, -⟩
    · exact hd
    · omega
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2 (statedClassicalModel_of_spFourIndex d hdSp e)
  obtain ⟨-, U, hdata, -⟩ := exists_siegel_data hp2 K hC ψ T
  have hBU : B = U := hdata.unique B hBT hB hBc
  refine ⟨?_, hdata.card_T, hdata.card_center⟩
  rw [hBU]
  exact (hdata.eq_normalizer T hY₀ hne).le

theorem kFactKlingenLocal_inSitu_spFour : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (d : TauCeti.ValidLieTypeIndex), IsSpFourIndex p d → ∀ (Y : Type) [Group Y] [Finite Y]
      (K : Subgroup Y), K.Normal → Nonempty (K ≃* CatGroup d) →
      Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y),
        B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
        GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀ := by
  intro p _ hp2 d hd Y _ _ K hK he hC T B Y₀ hBT hB hBc hY₀ hne
  haveI := hK
  obtain ⟨e⟩ := he
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2 (statedClassicalModel_of_spFourIndex d hd e)
  obtain ⟨-, U, hdata, hmod, -⟩ := exists_siegel_data hp2 K hC ψ T
  exact hdata.a3pInSitu T hmod hBT hB hBc hY₀ hne

theorem kFactKlingenThreeLocal_spFour : ∀ (d : TauCeti.ValidLieTypeIndex), IsSpFourIndex 3 d →
    ∀ (Y : Type) [Group Y] [Finite Y] [Fact (Nat.Prime 3)] (K : Subgroup Y), K.Normal →
      Nonempty (K ≃* CatGroup d) → Subgroup.centralizer (K : Set Y) = ⊥ →
      ∀ (T : Sylow 3 Y) (B Y₀ : Subgroup Y), B ≤ T → IsElemAbelian 3 B → Nat.card B = 3 ^ 3 →
        GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → HasKlingenData 3 T Y₀ →
        A9InSitu (T : Subgroup Y) B Y₀ ∧ Nat.card (T : Subgroup Y) = 3 ^ 4 ∧
          Nat.card (centerOf (T : Subgroup Y)) = 3 := by
  intro d hd Y _ _ _ K hK he hC T B Y₀ hBT hB hBc hY₀ hne _
  haveI := hK
  obtain ⟨e⟩ := he
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2 (statedClassicalModel_of_spFourIndex d hd e)
  obtain ⟨hq, U, hdata, hmod, hnn, hsol⟩ := exists_siegel_data hp2 K hC ψ T
  have hqsol : Group.IsSolvable (Y ⧸ K) := isSolvable_of_card_dvd_two hq
  exact ⟨hdata.a9InSitu T rfl hmod hnn (hsol rfl) hqsol hBT hB hBc hY₀ hne, hdata.card_T,
    hdata.card_center⟩

theorem kFactKlingenLocal_inSitu_of_sp62
    (h62 : ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (d : TauCeti.ValidLieTypeIndex),
      IsSpSixTwoIndex d → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
      Nonempty (K ≃* CatGroup d) → Subgroup.centralizer (K : Set Y) = ⊥ →
      ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y), B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
        GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀) :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex),
      IsKlingenIndex p d → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
      Nonempty (K ≃* CatGroup d) → Subgroup.centralizer (K : Set Y) = ⊥ →
      ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y), B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
        GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀ := by
  intro p _ hp2 d hd
  rcases hd with hd | ⟨hp3, hd⟩
  · exact kFactKlingenLocal_inSitu_spFour p hp2 d hd
  · exact h62 p hp3 d hd

theorem kFactKlingenThreeLocal_of_sp62
    (h62 : ∀ (d : TauCeti.ValidLieTypeIndex), IsSpSixTwoIndex d → ∀ (Y : Type) [Group Y]
      [Finite Y] [Fact (Nat.Prime 3)] (K : Subgroup Y), K.Normal → Nonempty (K ≃* CatGroup d) →
      Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (B Y₀ : Subgroup Y),
        B ≤ T → IsElemAbelian 3 B → Nat.card B = 3 ^ 3 → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ →
        Y₀ ≠ ⊤ → HasKlingenData 3 T Y₀ →
        A9InSitu (T : Subgroup Y) B Y₀ ∧ Nat.card (T : Subgroup Y) = 3 ^ 4 ∧
          Nat.card (centerOf (T : Subgroup Y)) = 3) :
    KFactKlingenThreeLocal := by
  intro d hd
  rcases hd with hd | ⟨-, hd⟩
  · exact kFactKlingenThreeLocal_spFour d hd
  · exact h62 d hd

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
