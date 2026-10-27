module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCert

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup Blueprint HSFLit

abbrev ghGen (i : Fin 9) : GHGroup := PresentedGroup.of i

structure GHSylow (G : Type) [Group G] where
  S : Sylow 2 G
  equiv : GHGroup ≃* (S : Subgroup G)

namespace GHSylow

variable {G : Type} [Group G] (D : GHSylow G)

@[expose] def emb : GHGroup →* G := (D.S : Subgroup G).subtype.comp D.equiv.toMonoidHom

theorem emb_injective : Function.Injective D.emb :=
  (D.S : Subgroup G).subtype_injective.comp D.equiv.injective

theorem range_emb : D.emb.range = D.S := by
  rw [emb, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr D.equiv.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

end GHSylow

theorem exists_ghSylow {G : Type}
    [Group G] [Finite G] (h : IsTypeHS G) : Nonempty (GHSylow G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite NativeSporadic.HS := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  obtain ⟨P, Q, ⟨e⟩⟩ := h
  obtain ⟨z', l', α₁', α₂', α₃', α₄', x', y', a', h', hcard'⟩ := ghRelInHS
  obtain ⟨e'⟩ := nonempty_equiv_of_ghRel ghPresentationBound h' hcard'
  set Q₀ : Sylow 2 NativeSporadic.HS :=
    Sylow.ofCard (closure ({z', l', α₁', α₂', α₃', α₄', x', y', a'} : Set NativeSporadic.HS)) (by
      rw [hcard', CFSG.Sporadic.HS.card_HS, show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
      norm_num)
  exact ⟨⟨P, e'.trans ((MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _).symm).trans
    ((Sylow.equiv Q₀ Q).trans e.symm))⟩⟩

end CFSG.ComponentClassification.GHarris
