module

public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.RankThree.PartOne.CTP.SeitzUIndex

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def UnitarySUNontoral : Prop :=
  ∀ (ℓ f p n : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → p.Prime → 5 ≤ p → p ≠ ℓ →
    ¬ p ∣ ℓ ^ f + 1 → 3 ≤ n → ∀ E : Subgroup (unitarySU ℓ f K n),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤

theorem unitarySU_planeGen_toral {ℓ f p n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (E : Subgroup (unitarySU ℓ f K (n + 1)))
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (he : ∀ x ∈ E, x ^ p = 1) (hcd : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    rw [h2] at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  exact CFSG.RankThree.PartOne.CTP.closure_centralizers_unitarySU_of_dvd_add_one h hp hpq hq E hc
    he hcd

theorem planeGen_inner_unitary {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hlift : ¬ (p ∣ q.card + 1 ∧ p ∣ m + 1))
    (hSU : ∀ E : Subgroup (unitarySU (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
        (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
        (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
          (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)) (m + 1)),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.twistedA m q, hv⟩ p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        have h3 := hrange.2 (by omega)
        rw [hqcard] at h2
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hc hinner)
  refine planeGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  exact CFSG.RankThree.PartOne.CTP.closure_centralizers_statedProj_unitary_of_lift hU hp
    (by omega) (fun hd => hlift ⟨by rw [← hqcard]; exact (hd.trans (Nat.gcd_dvd_right _ _)),
      hd.trans (Nat.gcd_dvd_left _ _)⟩) E₁ hcard₁ hSU

theorem seitzInnerUnitary_of_nontoral (h : UnitarySUNontoral) :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, ⟨m, q, hd⟩, hlift⟩
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  refine planeGen_inner_unitary hv hp hlift ?_ hE hc hinner
  intro E' hcomm hexp hcard
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  by_cases hpq : p ∣ TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ + 1
  · exact unitarySU_planeGen_toral hU hp hp5 hpq E' hcomm hexp hcard
  · exact h _ _ p (m + 1) _ hU hp hp5 hpd hpq (by omega) E' hcomm hexp hcard

end CFSG.LieType.SeitzGeneration
