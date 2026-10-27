module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Cover4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Iso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial

section Certs


theorem twA5CoverModel : TwA5CoverModel :=
  twA5CoverModel_of_witness (fun n p F _ _ _ hodd hn hF =>
    twA5CoverWitness n p F hn hodd hF)

theorem concl166S_twA5Cover_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hK : HasLabel K (fun l : GLALabel => l = lab))
    (hfam : i166FamTwA5 lab p (Subgroup.center K = ⊥))
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 4 ≤ evenRank K)
    (hr : GLATwoLocalRank p K + 1 = evenRank K)
    (h3 : Nat.card (Subgroup.center K) = 3) :
    ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J := by
  obtain ⟨t, r, n⟩ := lab
  simp only [i166FamTwA5] at hfam
  obtain ⟨ht, hrk, hn2, hdvd⟩ := hfam
  subst ht
  subst hrk
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have h3dvd : 3 ∣ Nat.card (Subgroup.center K) := by rw [h3]
  have hodd : Odd n := (unitarySix_mult (n := n) hn2 hK hG h3dvd).1
  obtain ⟨F, hFld, hFin, hChar, hFcard, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSU_of_label_center_three hK
      (⟨rfl, rfl, hn2, hdvd⟩ : i166FamTwA5 ⟨.twA, 5, n⟩ p (Subgroup.center K = ⊥)) h3
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  have heR : 4 ≤ evenRank (StatedSU 6 (2 ^ n) F) := by
    rwa [evenRank_eq_of_mulEquiv e] at he
  have hrR : GLATwoLocalRank p (StatedSU 6 (2 ^ n) F) + 1 =
      evenRank (StatedSU 6 (2 ^ n) F) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt e,
      hr, evenRank_eq_of_mulEquiv e]
  exact htr e (twA5CoverModel n p F hFcard hodd hn2 hp hp2 hdvd heR hrR)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
