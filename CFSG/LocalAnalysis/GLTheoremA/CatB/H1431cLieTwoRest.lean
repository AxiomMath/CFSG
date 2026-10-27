module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cInspF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (glaPComponent_isComponent_of_le_layer
  LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType isoInvariant_f42CompType
  compShape_F4_two)
open CFSG.Blueprint.Chevalley

section F4


theorem lieSTwoAt_F4 (hLO : LieOrderBridge) : LieSTwoAt fun d => ∃ q, d = .F4 q := by
  rintro Y _ _ _ _ _ ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α _ hα3 hα1
  have hq2 : q.card = 2 := hf
  refine ⟨fun _ => Or.inr hq2, ?_⟩
  rintro ⟨J, hJ, hT⟩
  have hp : q.p = 2 := by simpa using hc
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (GaloisField 2 1)
    (by rw [hK, hq2])
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e' : (Y ⧸ Subgroup.center Y) ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
    e.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hpow : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hne : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hsh : CompShape F42CompType α :=
    CompShape.of_congr isoInvariant_f42CompType e' (compShape_F4_two hK _ hpow hne)
  have hlay := hsh.layer _ hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hlay).1
  have h48 := lieSTwo_card_sp48 hLO hT
  haveI : Nontrivial (PSimple 3 J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h48]
    norm_num
  obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hJc.2.2 inferInstance
  have h6 := card_of_f42CompType (hsh.type J hJc)
  rw [Nat.card_congr φ.toEquiv, h48] at h6
  norm_num at h6

end F4

@[expose] def LieSTwoOther (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ n q, d = .C n q) ∨ (∃ q, d = .G2 q) ∨ (∃ q, d = .trialityD4 q) ∨ (∃ m, d = .suzuki m) ∨
    (∃ m, d = .reeG2 m) ∨ (∃ m, d = .reeF4 m) ∨ d = .tits

theorem lieSTwoAt_other (hLO : LieOrderBridge) : LieSTwoAt LieSTwoOther := by
  rintro Y _ _ _ _ _ ⟨d, hv⟩ hd hc hf ⟨e⟩ α _ _ _
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  have hcard := hLO ⟨d, hv⟩ (Y ⧸ Subgroup.center Y) ⟨e⟩
  rcases hd with ⟨n, q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hs
    simp only [] at hr
    exact absurd ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hc) hr.2
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    omega
  · have hq : q.card = 2 := hf
    have hS : Nat.card (Y ⧸ Subgroup.center Y) = 211341312 := by
      rw [hcard]
      show orderTrialityD4 q.card = 211341312
      rw [hq]
      decide +kernel
    exact lieSTwo_concl_of_not
      (lieSTwo_not_sp6two_of_not_dvd hLO (by rw [hS]; norm_num))
      (lieSTwo_not_sp48_of_not_dvd hLO (by rw [hS]; norm_num))
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hc
    omega
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hS : Nat.card (Y ⧸ Subgroup.center Y) = 17971200 := by
      rw [hcard]
      show orderTits = 17971200
      decide +kernel
    exact lieSTwo_concl_of_not
      (lieSTwo_not_sp6two_of_not_dvd hLO (by rw [hS]; norm_num))
      (lieSTwo_not_sp48_of_not_dvd hLO (by rw [hS]; norm_num))

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
