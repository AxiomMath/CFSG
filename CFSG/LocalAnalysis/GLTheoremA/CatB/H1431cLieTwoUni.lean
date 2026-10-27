module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClUni
public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge
  glaPComponent_isComponent_of_le_layer)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape ExcU62Type excU62Type_isoInvariant
  excU62_compShape_of_data)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem lieSTwo_compShape_u62 {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hp : q.p = 2) (hf : q.exponent = 1)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) {β : MulAut S}
    (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) : CompShape ExcU62Type β := by
  obtain ⟨⟨hℓ, hfe, hn3, hq'⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hfe, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := 5 + 1) (K := F))
  let e' : S ≃* primeFormP h (idGram F 6) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  refine CompShape.of_congr excU62Type_isoInvariant e' ?_
  exact excU62_compShape_of_data hp hf h _ (by rw [← map_pow, hβ, map_one])
    (fun h1 => hβ1 ((MulAut.congr e').injective (h1.trans (map_one _).symm)))

theorem lieSTwo_u62_card (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) {α : MulAut S}
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (hn : Nontrivial (PSimple 3 J)) :
    Nat.card (PSimple 3 J) = 25920 ∨ Nat.card (PSimple 3 J) = 13685760 ∨
      Nat.card (PSimple 3 J) = 504 := by
  obtain ⟨hp, hf⟩ := I1431C2.cl_primePower_card_two hq
  have hsh := lieSTwo_compShape_u62 hv hp hf e hα3 hα1
  have hlay := hsh.layer _ hJ.1 (glaPComponent_perfect hJ)
  have hJc := (glaPComponent_isComponent_of_le_layer hJ hlay).1
  obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hJc.2.2 hn
  obtain ⟨d, hd, ⟨eQ⟩⟩ := hsh.type J hJc
  have hc : Nat.card (PSimple 3 J) = lieOrderFormula d.1 := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hLO d _ ⟨eQ⟩
  obtain ⟨d, hdv⟩ := d
  cases d with
  | twistedA r q' =>
    obtain ⟨hr, hq'⟩ := hd
    have hcard' : q'.card = 2 := by
      rw [TauCeti.PrimePower.card_def, hq'.1, hq'.2]
      norm_num
    change Nat.card (PSimple 3 J) = orderTwistedA r q'.card at hc
    rw [hcard'] at hc
    rcases hr with rfl | rfl
    · left
      rw [hc]
      decide +kernel
    · right
      left
      rw [hc]
      decide +kernel
  | A r q' =>
    obtain ⟨rfl, hq'⟩ := hd
    have hcard' : q'.card = 8 := by
      rw [TauCeti.PrimePower.card_def, hq'.1, hq'.2]
      norm_num
    change Nat.card (PSimple 3 J) = orderA 1 q'.card at hc
    rw [hcard'] at hc
    right
    right
    rw [hc]
    decide +kernel
  | _ => exact hd.elim

theorem lieSTwo_u62_noSp (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) {α : MulAut S}
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) :
    ¬ CompOfType S α S9.isSp6two ∧ ¬ CompOfType S α S8.L84.isSp48 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨J, hJ, hT⟩
    have hc := lieSTwo_card_sp6two hLO hT
    haveI : Nontrivial (PSimple 3 J) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc]
      norm_num
    rcases lieSTwo_u62_card hLO hv hq e hα3 hα1 hJ inferInstance with h | h | h <;> omega
  · rintro ⟨J, hJ, hT⟩
    have hc := lieSTwo_card_sp48 hLO hT
    haveI : Nontrivial (PSimple 3 J) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc]
      norm_num
    rcases lieSTwo_u62_card hLO hv hq e hα3 hα1 hJ inferInstance with h | h | h <;> omega

theorem lieSTwoAt_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge) :
    LieSTwoAt fun d => ∃ n q, d = .twistedA n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α - hα3 hα1
  have hq : q.card = 2 := hf
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
  simp only [] at hr
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h6
  · have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 25920 := by
      rw [hLO ⟨_, hv⟩ _ ⟨e⟩]
      show orderTwistedA 3 q.card = 25920
      rw [hq]
      decide +kernel
    exact lieSTwo_concl_of_not
      (lieSTwo_not_sp6two_of_not_dvd hLO (by rw [hcard]; norm_num))
      (lieSTwo_not_sp48_of_not_dvd hLO (by rw [hcard]; norm_num))
  · have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 13685760 := by
      rw [hLO ⟨_, hv⟩ _ ⟨e⟩]
      show orderTwistedA 4 q.card = 13685760
      rw [hq]
      decide +kernel
    exact lieSTwo_concl_of_not
      (lieSTwo_not_sp6two_of_not_dvd hLO (by rw [hcard]; norm_num))
      (lieSTwo_not_sp48_of_not_dvd hLO (by rw [hcard]; norm_num))
  · obtain ⟨h6, h48⟩ := lieSTwo_u62_noSp hLO hv hq e hα3 hα1
    exact lieSTwo_concl_of_not h6 h48
  · exact (I1431C2.false_of_twistedA_high hGA hRk hv hq h6 e).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
