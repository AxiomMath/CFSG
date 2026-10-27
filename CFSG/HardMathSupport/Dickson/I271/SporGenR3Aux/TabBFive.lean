module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveHS
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StrongHSHe
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveACover

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B.Pinned CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.Yardstones.Md0ec50421ce4

section HSShape

theorem shapeRkAt'_hs_five (hOut : SporadicOuterLeTwo) {Q : Type} [Group Q] [Finite Q] {t : Q}
    (ht5 : orderOf t = 5) (hO : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({t} : Set Q)) = ⊥)
    {E : Subgroup Q} (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (eE : ↥E ≃* NativeSporadic.HS)
    (hC : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 665280000) :
    ShapeRkAt' 5 (GoodSpor 5 [.HS]) (RkSpor 5 [.HS]) t := by
  have hsimple : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  haveI : IsSimpleGroup ↥E := @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hsimple eE
  have hcard : Nat.card ↥E = 44352000 := by
    rw [Nat.card_congr eE.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hnab : ∃ a b : ↥E, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := ↥E)
    rw [hcard] at hp
    norm_num at hp
  have hZ : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple_nonab hnab
  have h5 : 5 ∣ Nat.card ↥E := by rw [hcard]; norm_num
  have hcore : GLAPPrimeCore 5 ↥E = ⊥ := glaPPrimeCore_eq_bot_of_simple Nat.prime_five h5
  have hnd : ∀ n ≤ 14, ¬ Nat.card ↥E ∣ n.factorial := by
    intro n hn
    rw [hcard]
    interval_cases n <;> norm_num [Nat.factorial]
  have hC' : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 15 * Nat.card ↥E := by
    rw [hcard]
    omega
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* (TauCeti.CFSGIndex.sporadic .HS).Group := b
  have hG : GoodSpor 5 [.HS] (PSimple 5 E) :=
    Or.inr (Or.inr ⟨.HS, List.mem_singleton_self _,
      ⟨(pSimpleEquivSelf E hcore hZ).trans (eE.trans b₀)⟩⟩)
  have hR : RkSpor 5 [.HS] (PQuot 5 E) :=
    RkSpor.of_equiv (pQuotEquivSelf E hcore).symm (rkSpor_HS_five hOut hZ)
  exact shapeRkAt'_of_simple_small_index_five ht5 hO E hEC inferInstance hnab h5 hnd hC' hG hR

end HSShape

section Residuals

@[expose] def TabBFiveACard : Prop :=
  Nat.card ↥(Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B)) < 665280000

@[expose] def TabBFiveAHS : Prop :=
  ∃ E : Subgroup NativeSporadic.B,
    E ≤ Subgroup.centralizer ({sFiveA} : Set NativeSporadic.B) ∧
      Nonempty (↥E ≃* NativeSporadic.HS)

@[expose] def TabBFiveBNoComp : Prop :=
  ∀ J : Subgroup NativeSporadic.B,
    ¬ GLAPComponent 5 (Subgroup.centralizer ({zFive} : Set NativeSporadic.B)) J

end Residuals

section HSCopy

theorem tabBFiveAHS_of_cert : TabBFiveAHS := by
  obtain ⟨-, ha1, -, has, hbs, hrel⟩ := bFiveHS_parts
  refine ⟨Subgroup.closure ({hsAFive, hsBFive} : Set NativeSporadic.B), ?_,
    nonempty_mulEquiv_HS_of_relators hsAFive hsBFive hrel ha1⟩
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.mem_centralizer_singleton_iff.2 has
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_centralizer_singleton_iff.2 hbs

end HSCopy

section Table

theorem tabBFive_hconj : ∀ y : NativeSporadic.B, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧
    ∃ g : NativeSporadic.B, g * zFive ^ c * g⁻¹ = y ∨ g * sFiveA ^ c * g⁻¹ = y := by
  intro y hy
  obtain ⟨t, ht, hty⟩ := bFiveTwoBCover_holds y hy
  exact exists_conj_pow_zFive_or_sFiveA hy ht hty

theorem bFiveShape_of_tab (hOut : SporadicOuterLeTwo)
    (hA : TabBFiveACard) (hB : TabBFiveBNoComp) : BFiveShape := by
  have hfin : Finite NativeSporadic.B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  obtain ⟨E, hEC, ⟨eE⟩⟩ := tabBFiveAHS_of_cert
  have h : CentShapeRk' 5 (GoodSpor 5 [.HS]) (RkSpor 5 [.HS]) NativeSporadic.B :=
    centShapeRk'_of_two_classes (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h) bFiveRel.orderOf_z orderOf_sFiveA tabBFive_hconj
      (Or.inl hB) (shapeRkAt'_hs_five hOut orderOf_sFiveA
        gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot hEC eE hA)
  exact h

theorem sporPair_B_five_of_tab
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .B 5) (hChev : ChevStrong 5) (hHS : SporStrong .HS 5)
    (hA : TabBFiveACard) (hB : TabBFiveBNoComp) : SporPair .B 5 :=
  sporPair_B_five_of_shape hOut hSpM hBr hP hChev hHS (bFiveShape_of_tab hOut hA hB)

end Table

end CFSG.HardMathSupport.Dickson.I271
