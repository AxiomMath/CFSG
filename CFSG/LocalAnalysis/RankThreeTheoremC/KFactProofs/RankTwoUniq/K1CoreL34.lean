module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreAlmost
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

section L34


variable {X : Type} [Group X] [Finite X]

theorem k1Core_eq_bot_of_l34 {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) {W : Subgroup X}
    (hAW : A ≤ Subgroup.normalizer (W : Set X)) (hW : Nat.Coprime (Nat.card W) 6) : W = ⊥ := by
  have hAK : A ≤ K := h.le_of_l34 kFactL34Outer hd ⟨e⟩
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := Tits.S3AmalgamBound.exists_equiv_projectiveSL_of_l34Index hd e
  have := h.normal
  obtain ⟨ι, hι, -, hιk⟩ := k1Core_exists_action h.centralizer_eq_bot ψ
  have hE : Nat.card ((A.subgroupOf K).map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, h.card_A]
    norm_num
  have hW2 : Nat.Coprime (Nat.card W) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hW
  have hW3 : Nat.Coprime (Nat.card W) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hW
  have hN3 : ¬ 3 ∣ Nat.card (W.map ι) := by
    rw [Subgroup.card_map_of_injective hι]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hW3.symm
  have hEN : ∀ x ∈ (A.subgroupOf K).map ψ.toMonoidHom,
      MulAut.conj x ∈ Subgroup.normalizer ((W.map ι : Subgroup (MulAut (projectiveSL 3 F))) :
        Set (MulAut (projectiveSL 3 F))) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← hιk a]
    exact Subgroup.le_normalizer_map ι ⟨(a : X), hAW (Subgroup.mem_subgroupOf.mp ha), rfl⟩
  rcases CFSG.RankThree.PartTwo.KFacts.L34.eq_bot_or_eq_zpowers_graphField hF hE hN3 hEN with
    h0 | ⟨τ, hτ, hτ1, hτ2, -, -⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective W hι).mp h0
  · exfalso
    have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
    have h2 : Nat.card (W.map ι) = 2 := by rw [hτ, Nat.card_zpowers, hτo]
    rw [Subgroup.card_map_of_injective hι] at h2
    rw [h2] at hW2
    norm_num at hW2

end L34

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
