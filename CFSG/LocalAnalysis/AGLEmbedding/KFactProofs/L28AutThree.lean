module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
import CFSG.Quasithin.Background.F6ResL28

public section

namespace CFSG.AGLEmbedding

theorem card_mulAut_of_isCaseTwoGroup_three {L : Type} [Group L] (hL : IsCaseTwoGroup 3 L) :
    Nat.card (MulAut L) = 1512 := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hK
    let e₃ : L ≃* CFSG.Quasithin.F6.L28Res.G8 :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂)
    rw [Nat.card_congr (MulAut.congr e₃).toEquiv, CFSG.Quasithin.F6.L28Res.card_mulAut]
  · omega

theorem kFactL28AutThree : KFactL28AutThree := by
  intro L _ _ hL A hA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hdvd : 3 ^ k ∣ 1512 :=
    hk ▸ card_mulAut_of_isCaseTwoGroup_three hL ▸ Subgroup.card_subgroup_dvd_card A
  have hk3 : k ≤ 3 := by
    by_contra h
    have h81 : 3 ^ 4 ∣ 1512 := (pow_dvd_pow 3 (not_le.mp h)).trans hdvd
    omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

end CFSG.AGLEmbedding
