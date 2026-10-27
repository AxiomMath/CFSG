module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def UnitaryToralNine : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ E : Subgroup (StatedProj (StatedSU 3 (ℓ ^ f) K)),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 3 = 1) → Nat.card E = 3 ^ 2 →
      (∀ x y : unitarySU ℓ f K 3, piSU ℓ f K x ∈ E → piSU ℓ f K y ∈ E → x * y = y * x) →
        Subgroup.closure {k : StatedProj (StatedSU 3 (ℓ ^ f) K) |
          ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤

theorem planeGen_inner_unitary_three (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (hq3 : 3 ∣ q.card + 1) {E : Subgroup (MulAut (Cat ⟨.twistedA 2 q, hv⟩))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hinner : InnerPlane ⟨.twistedA 2 q, hv⟩ 3 E) : PlaneGen E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 2 q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq3' : 3 ≤ q.card := hrange.2 rfl
  have hq2 : ℓ ^ f ≠ 2 := by omega
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (2 + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (2 + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        rw [hqcard] at h2
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA 2 q, hv⟩) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA 2 q, hv⟩)
    (range_conj_ne_bot_of_inner Nat.prime_three hc hinner)
  refine planeGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : 3 ∣ ℓ ^ f + 1 := by rw [hqcard]; exact hq3
  by_cases hnc : ∃ x y : unitarySU ℓ f (GaloisField ℓ (2 * f)) 3,
      piSU ℓ f (GaloisField ℓ (2 * f)) x ∈ E₁ ∧ piSU ℓ f (GaloisField ℓ (2 * f)) y ∈ E₁ ∧
        x * y ≠ y * x
  · exact closure_centralizers_statedProj_su_three_nonab hcore hU h3 hq2 E₁ hcomm hE₁.2 hnc
  · push Not at hnc
    exact htoral ℓ f _ hU h3 hq2 E₁ hcomm hE₁.2 hcard₁ fun x y hx hy => hnc x y hx hy

theorem seitzInnerUnitaryNonab (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine) :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ p = 3 ∧
        ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, q, hd, hq3⟩
  subst hd hp3
  exact planeGen_inner_unitary_three hcore htoral hv hq3 hE hc hinner

end CFSG.LieType.SeitzGeneration
