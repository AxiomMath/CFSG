module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedRecipe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.RankTwoTwistedA
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOff
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransportE
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftedData
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlockCommute
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.LieType.SeitzGeneration.OuterLinearCat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem catalogIs_largeEvenProj_statedSL {a k : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ^ k) (ha : 2 ≤ a) (h4 : a = 2 → 3 ≤ k)
    (h2 : a = 3 → 2 ≤ k) (h2' : a = 4 → 2 ≤ k) :
    catalogIs (LargeEvenProj (StatedSL a E)) (onLie isLinearCharTwoIdx) := by
  classical
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, pow_zero] at hE
      have h2c := Finite.one_lt_card (α := E)
      omega
    · exact h
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk⟩
  have hqcard : q.card = Nat.card E := by
    rw [TauCeti.PrimePower.card_def, hE]
  have hpow_mono : ∀ j : ℕ, j ≤ k → 2 ^ j ≤ 2 ^ k := fun j hj =>
    Nat.pow_le_pow_right (by norm_num) hj
  have hvalid : (TauCeti.LieTypeIndex.A (a - 1) q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    constructor
    · refine ⟨by omega, ?_⟩
      intro hr
      have ha2 : a = 2 := by omega
      subst ha2
      have h3 : 3 ≤ k := h4 rfl
      have h8 : 8 ≤ 2 ^ k := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := hpow_mono 3 h3
      rw [hqcard, hE]
      omega
    · intro hdup
      rcases hdup with ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩
      · have ha2 : a = 2 := by omega
        subst ha2
        have h3 : 3 ≤ k := h4 rfl
        have h8 : 8 ≤ 2 ^ k := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k := hpow_mono 3 h3
        rw [hqcard, hE] at hc
        have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
        rcases hc with h | h | h
        · rw [h] at h8; norm_num at h8
        · rw [h] at h2dvd; norm_num at h2dvd
        · rw [h] at h2dvd; norm_num at h2dvd
      · have ha3 : a = 3 := by omega
        subst ha3
        have h2k : 2 ≤ k := h2 rfl
        have h4le : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := hpow_mono 2 h2k
        rw [hqcard, hE] at hc
        rw [hc] at h4le
        norm_num at h4le
      · have ha4 : a = 4 := by omega
        subst ha4
        have h2k : 2 ≤ k := h2' rfl
        have h4le : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := hpow_mono 2 h2k
        rw [hqcard, hE] at hc
        rw [hc] at h4le
        norm_num at h4le
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := a - 1) (k := E) q hvalid hqcard.symm
  have hsub : a - 1 + 1 = a := by omega
  rw [hsub] at e
  exact ⟨.lie ⟨.A (a - 1) q, hvalid⟩, ⟨a - 1, q, rfl, rfl⟩,
    ⟨(statedRecipeEquiv a E).symm.trans e⟩⟩

theorem catalogIs_largeEvenProj_statedSU {a n : ℕ} {E : Type} [Field E] [Finite E]
    (hE : UnitaryFieldData 2 n E) (ha : 3 ≤ a) (hne : (a, 2 ^ n) ≠ (3, 2)) :
    catalogIs (LargeEvenProj (unitarySU 2 n E a)) (onLie isUnitaryCharTwoIdx) := by
  classical
  haveI hFintype : Fintype E := Fintype.ofFinite E
  have hcardNat : Nat.card E = (2 ^ n) ^ 2 := by
    rw [hE.card, show 2 * n = n * 2 by omega, pow_mul]
  have hcard : Fintype.card E = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardNat
  obtain ⟨q', hv, hqp, hqc, ⟨e⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := a) (q := 2 ^ n) hcard ha hne
  haveI : CharP E 2 := hE.charP
  have hrc : ringChar E = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (CharP.cast_eq_zero E 2)
  have hcenter : Subgroup.center (StatedSU a (2 ^ n) E) =
      (StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ n) E) :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.center_statedSU_eq_scalars_of_ne
      (K := E) (f := n) hcardNat ha hne
  exact ⟨.lie ⟨.twistedA (a - 1) q', hv⟩, ⟨a - 1, q', rfl, by rw [hqp, hrc]⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).symm.trans e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
