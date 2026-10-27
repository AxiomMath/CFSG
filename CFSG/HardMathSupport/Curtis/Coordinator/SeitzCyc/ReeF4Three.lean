module

public import CFSG.LieType.SeitzGeneration.ExcOuterReeF4

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

@[expose] def SubfieldPairReeF4Three : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ (β : K ≃+* K), orderOf β = 3 →
      ∀ g : F4.reeGamma K a,
        (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (F4.reeGammaFieldAut K a β) →
        Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
          ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
            Set (F4.reeGamma K a))) = ⊤

theorem subfieldPairReeF4Three_holds :
    SubfieldPairReeF4Three := by
  intro a ha K _ _ _ hK β hβ g hne
  by_cases hk : Nat.card (fixSubfield β) = 2
  · obtain ⟨hdvd, hcard⟩ :=
      CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK β
    rw [hβ] at hdvd hcard
    have h1 : (2 * a + 1) / 3 = 1 := by
      rw [hk] at hcard
      exact Nat.pow_right_injective (le_refl 2) (hcard.symm.trans (pow_one 2).symm)
    have h3 : 2 * a + 1 = 3 := by
      obtain ⟨d, hd⟩ := hdvd
      rw [hd, Nat.mul_div_cancel_left _ (by norm_num)] at h1
      omega
    exact closure_eq_top_of_maximal β g hne fun _ hHΓ hRH hHR =>
      reeGamma_le_of_overgroup_two_odd ha hK (by rw [h3]; norm_num) β (hβ.trans h3.symm) hHΓ hRH
        hHR
  · exact closure_eq_top_odd ha hK β Nat.prime_three (by norm_num) hβ hk g hne

theorem fieldAutData_reeF4_three (hpair : SubfieldPairReeF4Three) {p : ℕ} (hp : p.Prime)
    (hp3 : p = 3) (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FieldAutData (F4.reeGamma K a) p :=
  fieldAutData_reeF4_odd hp (by omega) ha hK fun β hβ g hne =>
    Or.inl (hpair a ha K hK β (hp3 ▸ hβ) g hne)

end CFSG.RankThree.PartOne.SEITZRF

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZRF CFSG.RankThree.PartOne.SEITZ2
  CFSG.RankThree.PartOne TauCeti

section Final


theorem seitzExcOuterNarrowReeF4Three_holds : SeitzExcOuterNarrowReeF4Three := by
  have hpair := subfieldPairReeF4Three_holds
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨m, hm⟩, hp3⟩
  subst hm
  obtain ⟨hfin, hsimple⟩ := finite_isSimpleGroup_cat_reeF4 hv
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  have hnab := exists_noncommuting_of_isElementaryAbelian_aut hel hc
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ := SEITZX.exists_reeGamma_model (K := Cat ⟨.reeF4 m, hv⟩)
    ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have hd : FieldAutData (Cat ⟨.reeF4 m, hv⟩) p :=
    (fieldAutData_reeF4_three hpair hp hp3 ha hX).of_mulEquiv e hp
  rw [planeGen_iff_closure_fixUnion]
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc
    (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩)

end Final

end CFSG.LieType.SeitzGeneration
