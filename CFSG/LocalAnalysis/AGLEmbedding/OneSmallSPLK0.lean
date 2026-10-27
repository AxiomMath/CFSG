module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem smallRankOneData_of_altSix {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K)
    (T : Sylow 3 K) : SmallRankOneData 3 K T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₁⟩ := hK
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  let e : K ≃* PSL2GF 3 2 := e₁.trans e₂.symm
  have hfs : Function.Surjective (e : K →* PSL2GF 3 2) := e.surjective
  exact SmallRankOneData.of_equiv e (Sylow.coe_mapSurjective hfs T).symm
    (smallRankOneData_psl2GF (by norm_num) (T.mapSurjective hfs))

theorem oneLieFacts_altSix {K : Type} [Group K] [Finite K] (hK : IsAltTwoP 3 K)
    (T : Sylow 3 K) : OneLieFacts 3 K T :=
  oneLieFacts_of_data Nat.prime_three (fun T' => smallRankOneData_of_altSix hK T') T

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.pair_oneLieFacts (hd : D1OneSmallData p P M H R Rbar K)
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧ OneLieFacts p K T₁ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  refine ⟨T₁, hT₁, ?_⟩
  rcases hLA with h | ⟨rfl, h⟩
  · exact oneLieFacts_of_data hp (smallRankOneData_of_isSmallLinTwo hd.cfg.red.ne_two h) T₁
  · exact oneLieFacts_altSix h T₁

end Config

end CFSG.AGLEmbedding
