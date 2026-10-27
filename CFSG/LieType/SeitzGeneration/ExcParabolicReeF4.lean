module

public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Gen
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Simplicity.ReeLargeModel
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag TauCeti

section Model


theorem exists_reeGamma_equiv_cat {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (_ : CharP X F4.prime),
      1 ≤ m ∧ Nat.card X = 2 ^ (2 * m + 1) ∧ IsSimpleGroup (Cat ⟨.reeF4 m, hv⟩) ∧
        Nonempty (Cat ⟨.reeF4 m, hv⟩ ≃* F4.reeGamma X m) := by
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hmodel : ReeTitsModel (Cat ⟨.reeF4 m, hv⟩) .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  have hsimple := (CFSG.LieType.Simplicity.fam_2f4_simplicity _ 2 (2 * m + 1) hmodel).2
  obtain ⟨hFin, -, -, -, -, hmain⟩ := ReeTag.large_Ree_model_Schreier _ 2 (2 * m + 1) hmodel
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar' : CharP X F4.prime := by
    have : Fintype X := Fintype.ofFinite X
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * m + 1) (by
      rw [← Nat.card_eq_fintype_card, hXcard])
  have ham : a = m := by omega
  subst ham
  obtain ⟨E⟩ := hmain a X hfa hXcard ⟨e2⟩
  exact ⟨X, inferInstance, inferInstance, hchar', hm1, hXcard, hsimple, ⟨E⟩⟩

theorem seitzExcParabolicFor_reeF4 : SeitzExcParabolicFor IsReeF4Index := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, rfl⟩, R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup ↥(F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  exact planeGen_of_native e (large_Ree_fixed_group_center_trivial m X hX)
    (rootInvariantGeneration_reeGamma hX hp2) hE hc hin ⟨R, hR1, by simpa using hRp, hRn⟩

end Model

end CFSG.LieType.SeitzGeneration
