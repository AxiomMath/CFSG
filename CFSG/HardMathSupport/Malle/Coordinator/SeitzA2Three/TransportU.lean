module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Transport

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

@[expose] def U3ThreeModelGen : Prop :=
  ∀ (ℓ f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F), 2 < ℓ ^ f → 3 ∣ ℓ ^ f + 1 →
    ℓ ^ f ≠ 8 → ∀ B : Subgroup (MulAut (unitaryPSU h 3)), IsElemAbelian 3 B →
      Nat.card B = 3 ^ 3 → ModelHyperGen 3 B

theorem kFactSeitzOuterCubeRankTwoAtPrime_U3_three_of_model {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (h3 : 3 ∣ q.card + 1)
    (hM : U3ThreeModelGen) :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.twistedA 2 q, hv⟩ 3 := by
  intro _ Y _ _ K hKn hC ⟨e₀⟩ _ hlist _ E hEa hEc
  obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFc, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
      (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩))
  have hU : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hFc, ← pow_mul, mul_comm]⟩
  have hq2 : 2 < q.p ^ q.exponent := by
    have h1 : 2 ≤ q.p ^ q.exponent :=
      (hℓ.two_le).trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 q.exponent_pos) _)
    refine lt_of_le_of_ne h1 fun h2 => hne ?_
    rw [← h2]
  have h3q : 3 ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact h3
  have h8' : q.p ^ q.exponent ≠ 8 := by
    intro h8e
    apply hlist
    have hp2 : q.p = 2 := by
      have hd : q.p ∣ 2 ^ 3 := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8e]
        exact dvd_pow_self _ q.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd)
    have he3 : q.exponent = 3 := by
      rw [hp2] at h8e
      have h8'' : (2 : ℕ) ^ q.exponent = 2 ^ 3 := by rw [h8e]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h8''
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, q, hp2, he3, Or.inr (Or.inr (Or.inr rfl))⟩)))))
  set e : K ≃* unitaryPSU hU 3 :=
    e₀.trans (e₁.trans (unitaryPSUEquiv hU (by norm_num)).symm) with he
  have hinj := conjModel_injective e hC
  refine hyperGen_of_modelHyperGen e hC (hM q.p q.exponent F hU hq2 h3q h8' _ ?_ ?_)
  · exact CFSG.SectionRank.isElemAbelian_map hEa _
  · rw [Subgroup.card_map_of_injective hinj, hEc]

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
