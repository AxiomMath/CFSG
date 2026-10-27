module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Spec
public import CFSG.HardMathSupport.Timmesfeld.LieRank.SylowTwoGen
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

theorem factorization_card_three :
    (4245696 : ℕ).factorization 3 = 6 := by
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (4245696 : ℕ) ≠ 0)).1
    (show 3 ^ 6 ∣ 4245696 by norm_num)
  have h2 : ¬ 7 ≤ (4245696 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (4245696 : ℕ) ≠ 0)).2 h)
      (by norm_num)
  omega

section Certificates


theorem card_RG : Nat.card RG = 4245696 := by
  have e : adjointGroup .G2 (ZMod 3) ≃* RG :=
    Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3))) (glHom_injective _)
  rw [← Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
    Nat.card_zmod]
  decide

theorem pRank_RG_le_four : CFSG.Open.pRank 3 (⊤ : Subgroup RG) ≤ 4 := by
  have hn : specA.n = 4 := rfl
  refine pRank_le_of_two_gens specA actsBy_gxa actsBy_gxb gxa_pow gxb_pow comm_xb_xa
    distinct_nine (z := 2) (r := 4) ?_ card_fixed ?_
  · rw [card_RG, factorization_card_three]
    omega
  · intro a j ha hj h1 h2
    omega

theorem pRank_quotient_le_of_cover_G2 {L : Type} [Group L] [Finite L]
    (e : L ⧸ Subgroup.center L ≃* adjointGroup .G2 (ZMod 3))
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e', -⟩ : ∃ e' : L ⧸ Subgroup.center L ≃* RG, True :=
    ⟨e.trans (Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3)))
      (glHom_injective _)), trivial⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
  have hzL : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : L →* RG := (e' : L ⧸ Subgroup.center L →* RG).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  have h4 := four_le_pRank_of_cover_RG φ hφ hker.le (z := (z : L))
    (by rw [hker]; exact z.2) hzL
  have h5 := pRank_RG_le_four
  have heq : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup RG) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e'
  omega

end Certificates

end CFSG.HardMathSupport.Timmesfeld.LieRank
