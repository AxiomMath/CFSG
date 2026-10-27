module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosGU
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem LeviBlock.eq_one_of_mem_uniBlockOrders_u38 {f s ε : ℕ} (hε : ε ≤ 1)
    (h : 5515776 ∈ uniBlockOrders f s ε) : s = 1 ∧ ε = 1 := by
  rcases h with ⟨k, hk⟩ | hk
  · exact absurd hk.symm (ordA_ne_u38 (n := k) (f := 2 * f) (by rw [← pow_mul, mul_comm]))
  · have := ((ordTwistedA_eq_u38_iff (f := f) rfl).mp hk.symm).1
    omega


theorem kFactCompParabSU38On_unitary_eight : KFactCompParabSU38On (IsLieOf (IdxTwistedAAt 8)) := by
  intro Y _ _ L P hCP hC O W hOP hPO hO3 hWP hPWO _ d' ψ hd' hψ
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d (LeviBlock.idxTwistedA_of_at hd) e
  have hf8 : 2 ^ f = 8 := LeviBlock.two_pow_eq_of_at hd fun r₀ q h₀ => (hq r₀ q h₀).1
  have : Finite K := h.finite
  have hmem : 5515776 ∈ uniBlockOrders f s ε := by
    obtain ⟨q, hqp, -, hdq⟩ := id hd'
    have : IsSimpleGroup (CatGroup d') := unitaryTarget_isSimpleGroup ⟨q, hqp, hdq⟩
    have : Finite (CatGroup d') := Finite.of_surjective ψ hψ
    have hcard := LeviBlock.card_catGroup_u38 hd'
    have hnc : ∃ a b : CatGroup d', a * b ≠ b * a :=
      ThreeFives.exists_noncomm_of_simple inferInstance (by rw [hcard]; norm_num)
    have := card_mem_of_section hCP.parab.1 ρ hρ (hasLeviBlocks_hypStab h hε hI g hJ) hOP hPO
      hO3 hWP hPWO hnc (by rw [hcard]; norm_num) ψ hψ
    rwa [hcard] at this
  obtain ⟨rfl, rfl⟩ := LeviBlock.eq_one_of_mem_uniBlockOrders_u38 hε hmem
  obtain rfl : f = 3 := Nat.pow_right_injective le_rfl (hf8.trans (by norm_num))
  have htn : 2 ≤ t ∨ Nat.Coprime (2 * (t + 1) + 1) (2 ^ 3 + 1) := by
    rcases Nat.lt_or_ge t 2 with ht | ht
    · right
      obtain rfl : t = 1 := by
        have := (hI.le t hI.mem).1
        omega
      norm_num
    · exact Or.inl ht
  exact (LeviBlock.three_pow_seven_dvd_card_hypUnitary_one_one h).trans
    (LeviBlock.card_hypUnitary_dvd_card_of_flag h hε hI ρ hZ g hJ htn)

theorem kFactCompParabSU38On_twistedA : KFactCompParabSU38On (IsLieOf IdxTwistedA) :=
  kFactCompParabSU38On_twistedA_of kFactCompParabSU38On_unitary_eight

end CFSG.AGLEmbedding
