module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open CFSG.Open CFSG.Blueprint Subgroup

set_option linter.unusedSectionVars false

theorem card_centralizer_mulEquiv_ex {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (τ : X) :
    Nat.card ↥(centralizer ({τ} : Set X)) = Nat.card ↥(centralizer ({φ τ} : Set Y)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun x => ?_)
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, ← map_mul, φ.injective.eq_iff]


theorem lie23To89At_twistedB2 : Lie23To89At .twistedB2 := by
  intro X _ _ n f _ hM τ hτ h23
  rcases hM with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  obtain ⟨-, a, ha, K, _, _, hf, hKcard, ⟨e⟩⟩ := h
  haveI : Finite (suzukiGroup a K) := Finite.of_equiv _ e.toEquiv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hKcard
  obtain ⟨P, -, hP, -⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1 (e τ)
      (by rw [MulEquiv.orderOf_eq]; exact hτ)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
  rw [card_centralizer_mulEquiv_ex e τ, hP, hm] at h23
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h23) (by norm_num)

end CFSG.ComponentClassification.CatFC.DS81.Ex
