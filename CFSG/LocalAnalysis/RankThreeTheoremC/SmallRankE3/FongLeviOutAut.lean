module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

theorem exists_outer_aut {A : Type} [Group A] [Finite A] {K B : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hKr : CFSG.Open.pRank p K ≤ 1) (hZ : Subgroup.center ↥K = ⊥)
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBK : B ≤ Subgroup.normalizer (K : Set A))
    (hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) :
    ∃ α : MulAut ↥K, α ^ p = 1 ∧
      α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
  obtain ⟨b, hbB, hb⟩ := exists_outer_of_faithful hp hKr hZ hB hBc hBK hnb
  have hbK : b ∈ Subgroup.normalizer (K : Set A) := hBK hbB
  let α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbK⟩
  have hαp : α ^ p = 1 := by
    rw [← map_pow]
    have : (⟨b, hbK⟩ : Subgroup.normalizer (K : Set A)) ^ p = 1 :=
      Subtype.ext (by simpa using hB.2 b hbB)
    rw [this, map_one]
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
    rintro ⟨k, hk⟩
    apply hb
    refine ⟨(k : A), k.2, fun x hx => ?_⟩
    have h1 := congrArg (fun γ : MulAut ↥K => ((γ ⟨x, hx⟩ : ↥K) : A)) hk
    simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using h1.symm
  exact ⟨α, hαp, hαin⟩

theorem false_of_not_dvd_card_outer {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A}
    {z : A} {p : ℕ} (S : E3Setting K K₀ B z p) (hZ : Subgroup.center ↥K = ⊥)
    (hOut : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) : False := by
  obtain ⟨α, hαp, hαin⟩ := exists_outer_aut S.hp S.hKr hZ S.hB S.hBc S.hBK S.hnb
  exact hαin (CFSG.AGLEmbedding.OuterSylow.mem_inner_of_not_dvd_card_outer S.hp hOut hαp)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
