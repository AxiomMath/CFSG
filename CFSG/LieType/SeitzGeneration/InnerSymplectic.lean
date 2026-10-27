module

public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.RankThree.PartOne.CTP.SeitzSpIndex

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank

theorem planeGen_inner_sp_model {d : TauCeti.ValidLieTypeIndex} {r ℓ f p : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r)
    (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane d p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hKge : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega) (by
      by_cases h4 : 4 ≤ Nat.card K
      · exact Or.inl (Or.inr h4)
      · right
        have h2 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
        rcases h2 with h2 | h2
        · exact Or.inr ⟨h2, by
            by_contra hr3
            exact hrq ⟨by omega, by rw [← hK]; exact h2⟩⟩
        · exact Or.inl ⟨h2, hr⟩)
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner hp hc hinner)
  refine planeGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  exact CFSG.RankThree.PartOne.CTP.closure_centralizers_psp_elementary hℓ hf hK hp hp5 hpℓ hr hrq
    E₁ hcard₁

theorem card_fixedField_C (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) = q.p ^ q.exponent := by
  rw [TauCeti.ValidLieTypeIndex.card_fixedField,
    TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
    show TauCeti.ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩ = q.p from
      TauCeti.LieTypeIndex.characteristic_C r q,
    show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.C r q, hv⟩ = q.exponent from
      TauCeti.LieTypeIndex.fieldExponent_C r q]

theorem seitzInnerSymplectic :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, hsp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hsp with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    have hq : p ≠ q.p := by simpa using hpd
    exact planeGen_inner_sp_model (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp5 hq
      le_rfl
      (fun h => hrange.2 ⟨h.1, by simpa [TauCeti.PrimePower.card_def] using h.2⟩) hE hc hinner
  ·
    have hq : p ≠ q.p := by simpa using hpd
    exact planeGen_inner_sp_model
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hp hp5 hq
      (by omega) (fun h => by omega) hE hc hinner
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have hr3 : 3 ≤ r := hrange.1
    exact planeGen_inner_sp_model (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p q.exponent_pos (card_fixedField_C r q hv) hp hp5 hq (by omega)
      (fun h => by omega) hE hc hinner

end CFSG.LieType.SeitzGeneration
