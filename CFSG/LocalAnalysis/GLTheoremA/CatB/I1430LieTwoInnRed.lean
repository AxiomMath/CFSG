module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cInspF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.LocalAnalysis.GLTheoremA.H1431c
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType isoInvariant_f42CompType
  compShape_F4_two)
open CFSG.Blueprint.Chevalley

theorem i1430_fieldSize (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (i : TauCeti.CFSGIndex)
    (hrel : compRelC d.1 i) (φ : T ≃* i.Group) (hT : Nat.card T = 360) :
    fieldSize d.1 = 2 := by
  obtain ⟨k0, hk0, hkd⟩ := I1431C2.exists_fieldSize_two_pow hd
  have hodd : ∀ m : ℕ, m % 2 = 1 → fieldSize d.1 ≠ m := fun m hm h => by
    have h2 : 2 ∣ 2 ^ k0 := dvd_pow_self 2 (by omega)
    rw [← hkd, h] at h2
    omega
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn =>
    have hc : Nat.card (alternatingGroup (Fin n)) = 360 := by
      rw [← hT]
      exact (Nat.card_congr φ.toEquiv).symm
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    rcases hrel with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨rfl, -⟩
    · norm_num [Nat.factorial] at hc
    · rcases h with h | h | h
      · exact h
      · exact absurd h (hodd 3 rfl)
      · exact absurd h (hodd 9 rfl)
    · norm_num [Nat.factorial] at hc
  | lie e =>
    have hcard : Nat.card T = lieOrderFormula e.1 := hB e T ⟨φ⟩
    rcases hrel with ⟨hch, -⟩ | ⟨hf2, -⟩ | ⟨hf3, -⟩
    · exact (false_of_lieOrderFormula_360 e.2 (hch.trans hd) (hcard.symm.trans hT)).elim
    · exact hf2
    · exact absurd hf3 (hodd 3 rfl)

theorem i1430LieTwoInn_of_no (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group)
    (hNo : I1430LieTwoInnNo fun d => ¬ ∃ n q, d = .B n q) : I1430LieTwoInn := by
  intro S _ _ hS hnc d hd hSd α hα hα3 hα1 hC
  obtain ⟨e⟩ := hSd
  obtain ⟨i, J, hrel, ⟨φ⟩, hT⟩ :=
    lieSInn_component_index hL hS hnc d hd e (hI d hd) hα hα3 hα1 hC
  have hf : fieldSize d.1 = 2 := i1430_fieldSize hB d hd i hrel φ (card_a6 hB hT)
  by_cases hBn : ∃ n q, d.1 = .B n q
  · obtain ⟨n, q, hnq⟩ := hBn
    obtain ⟨d, hv⟩ := d
    change d = .B n q at hnq
    subst hnq
    have hq : q.card = 2 := hf
    have hs := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    have h3 : 3 ≤ n := by
      by_contra hlt
      exact hs.2 ⟨by have := hs.1; omega, hq⟩
    exact ⟨n, h3, (⟨rfl, hq⟩ : n = n ∧ q.card = 2)⟩
  · exact (hNo S hS hnc d hBn hd hf ⟨e⟩ α hα hα3 hα1 hC).elim

theorem i1430InnNoF4_proved
    (hB : LieOrderBridge) : I1430InnNoF4 := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α hα hα3 hα1 ⟨J, hJ, hT⟩
  have hq2 : q.card = 2 := hf
  have hp : q.p = 2 := by simpa using hc
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (GaloisField 2 1)
    (by rw [hK, hq2])
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e' : S ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
    e.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hpow : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hne : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hsh : CompShape F42CompType α :=
    CompShape.of_congr isoInvariant_f42CompType e' (compShape_F4_two hK _ hpow hne)
  have hlay := hsh.layer _ hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hlay).1
  have h360 : Nat.card (PSimple 3 J) = 360 := card_a6 hB hT
  haveI : Nontrivial (PSimple 3 J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, h360]
    norm_num
  obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hJc.2.2 inferInstance
  have h6 := card_of_f42CompType (hsh.type J hJc)
  rw [Nat.card_congr φ.toEquiv, h360] at h6
  norm_num at h6

theorem i1430InnNoOther_proved
    (hB : LieOrderBridge) : I1430InnNoOther := by
  rintro S _ _ hS hnc ⟨d, hv⟩ hd hc hf ⟨e⟩ α hα hα3 hα1 ⟨J, hJ, hT⟩
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  have h360 : Nat.card (PSimple 3 J) = 360 := card_a6 hB hT
  have hcard := hB ⟨d, hv⟩ S ⟨e⟩
  rcases hd with ⟨n, q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hs
    simp only [] at hr
    exact absurd ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hc) hr.2
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    omega
  · have hq : q.card = 2 := hf
    have hS : Nat.card S = 211341312 := by
      rw [hcard]
      show orderTrialityD4 q.card = 211341312
      rw [hq]
      decide +kernel
    have hdvd : 360 ∣ Nat.card S := by
      rw [← h360]
      exact lieSTwo_card_pSimple_dvd J
    rw [hS] at hdvd
    exact absurd hdvd (by norm_num)
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
  · haveI := hS
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c.false_of_glaPComponent_of_isSolvable
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_tits hv hnc ⟨e⟩
        Nat.prime_three (by norm_num) hα3 hα1) hJ

theorem i1430LieTwoInn_of_families
    (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group)
    (hA : I1430InnNoA) (htA : I1430InnNoTwistedA) (hD : I1430InnNoD)
    (htD : I1430InnNoTwistedD) (hE : I1430InnNoE) (htE6 : I1430InnNoTwistedE6) :
    I1430LieTwoInn :=
  i1430LieTwoInn_of_no hL hB hI
    (i1430LieTwoInnNo_notB hA htA hD htD hE htE6 (i1430InnNoF4_proved hB)
      (i1430InnNoOther_proved hB))

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
