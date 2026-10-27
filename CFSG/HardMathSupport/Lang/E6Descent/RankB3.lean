module

public import CFSG.HardMathSupport.Lang.E6Descent.RankB3Group

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Open CFSG.HardMathSupport.Lang.E6Descent.RankB3

theorem exists_elemAbelian_card_of_equiv {F : Type} [Field F] (hF : Nat.card F = 3)
    {G : Type} [Group G] (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd 3 F))) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have h3 : (3 : F) = 0 := by
    have h := card_nsmul_eq_zero' (G := F) (x := 1)
    rw [hF] at h
    simpa using h
  let Φ : Multiplicative (WS F) →* StatedOmega (StatedQuadOdd 3 F) :=
    (psi F).codRestrict _ (psi_mem_omega h3)
  let Θ : Multiplicative (WS F) →* G :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp Φ)
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk' _ (Φ x) : StatedProj (StatedOmega (StatedQuadOdd 3 F))) = 1 :=
      (e.symm.map_eq_one_iff).1 hx
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact psi_scalar (Subgroup.mem_subgroupOf.1 h2)
  refine ⟨Θ.range, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hxa⟩ := a.2
    obtain ⟨y, hyb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      rw [pow_succ, pow_two]
      exact toAdd_cube h3 x
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_congr (Equiv.refl _), card_WS hF]

end CFSG.HardMathSupport.Lang.E6Descent
