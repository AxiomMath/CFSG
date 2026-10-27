module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldRee
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldLargeRee
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Suzuki
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag TauCeti
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

section


theorem e27LieOuterAutAt_reeG2 : E27LieOuterAutAt (fun i => ∃ m, i = .reeG2 m) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨a, rfl⟩ := hd
  have ha : 1 ≤ a := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
  have hrel : ReeTitsRelationModel K .G2 reeG2Perm reeG2Long 3 (2 * a + 1) a :=
    ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ := (reeTitsRelationModel_iff .G2 K (2 * a + 1) a).1 hrel
  obtain ⟨e₂⟩ := CFSG.HardMathSupport.Lang.Coordinator.nonempty_derivedCentralQuotient_reeGamma_G2
    (K := F) ha hF
  let θ := e₁.trans e₂
  refine false_of_dvd_twentySeven u hQ ?_
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ u]
  refine twentySeven_dvd_fixedSubgroup_smallRee a ha F hF Nat.prime_three (by norm_num) _
    (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ u).1 hin
  exact hout k hk.symm

theorem e27LieOuterAutAt_reeF4 :
    E27LieOuterAutAt (fun i => ∃ m, i = .reeF4 m) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hR : ReeTitsModel K .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
      (ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩
  obtain ⟨a, F, _, _, _, hfa, hFcard, ⟨e'⟩⟩ :
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F F4.prime),
        2 * m + 1 = 2 * a + 1 ∧ Nat.card F = 2 ^ (2 * m + 1) ∧ Nonempty (K ≃* F4.reeGamma F a) := by
    obtain ⟨-, -, -, -, -, -, hmain⟩ :=
      large_Ree_model_field_outer_group_and_inner_involutions K 2 (2 * m + 1) hR
    obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
    have : CharP F F4.prime := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * m + 1) (by
        rw [← Nat.card_eq_fintype_card, hFcard])
    obtain ⟨⟨e'⟩, -⟩ := hmain a F hfa hFcard he
    exact ⟨a, F, inferInstance, inferInstance, this, hfa, hFcard, ⟨e'⟩⟩
  have ha : 1 ≤ a := by omega
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  refine false_of_dvd_twentySeven u hQ ?_
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e' u]
  refine twentySeven_dvd_fixedSubgroup_largeRee ha hF Nat.prime_three (by norm_num) _
    (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e' u).1 hin
  exact hout k hk.symm

end

theorem e27LieOuterAutAt_suzuki :
    E27LieOuterAutAt (fun i => ∃ m, i = .suzuki m) := by
  rintro K _ _ d hd ⟨e⟩ - u - - - - ⟨T, -, -, hT⟩
  obtain ⟨i, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : CFSG.Theory.Comparator.SzModel m = CFSG.Open.Sz m := CFSG.Models.benderSzModel_eq_sz m
  let toSz : K ≃* CFSG.Open.Sz m :=
    (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
      ((MulEquiv.subgroupCongr (hmodel.symm.trans
        (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm)
  have hcard : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  let toBP : K ≃* CFSG.Blueprint.suzukiGroup m (GaloisField 2 (2 * m + 1)) :=
    (toSz.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative m hm hcard).symm).trans
      (MulEquiv.subgroupCongr
        (CFSG.QuasithinUnique.B1.suzukiGroup_eq_glaSzGroup m (GaloisField 2 (2 * m + 1))).symm)
  have h9 : 9 ∣ Nat.card K := hT ▸ Subgroup.card_subgroup_dvd_card T
  rw [Nat.card_congr toBP.toEquiv, CFSG.LieType.Ree.suzuki_order hcard] at h9
  have h3 : 3 ∣ (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) :=
    (Dvd.intro_left 3 rfl : 3 ∣ 9).trans h9
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [Nat.pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = q at h3 hq
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · omega
  · omega

end CFSG.HardMathSupport.Malle.E27Lie
