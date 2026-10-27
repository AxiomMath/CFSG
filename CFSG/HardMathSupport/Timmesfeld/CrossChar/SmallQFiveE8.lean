module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Leaf
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

theorem gLAPPrimeCoreOf_centralizer_eq_bot_iff5 {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (t : A) : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({t} : Set A)) = ⊥ ↔
      GLAPPrimeCoreOf 5 (Subgroup.centralizer ({φ t} : Set B)) = ⊥ := by
  rw [← map_centralizer_mulEquiv φ t,
    gLAPPrimeCoreOf_map_of_injective 5 φ.toMonoidHom φ.injective]
  constructor
  · intro h
    rw [h, Subgroup.map_bot]
  · exact eq_bot_of_map_eq_bot φ.injective

section Main


theorem gLAPPrimeCoreOf_centralizer_eq_bot_E8_five_two {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] [IsAlgClosure K L] (hK : Nat.card K = 2) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL Tag.E8 L} (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    {d : adjointGroup Tag.E8 K} (hd1 : d ≠ 1)
    (hdT : baseChangeGL (algebraMap K L) (d : ModGL Tag.E8 K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
        (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({d} : Set (adjointGroup Tag.E8 K))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKchar : CharP K 2 := charP_two_of_card_two hK
  have hLchar : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hLac : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr2 : Fr = iterateFrobenius L 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  obtain ⟨ζ, hζ⟩ := exists_zeta5 (L := L)
  have hMW := langModel_le_twModel Tag.E8 K L hFr hg0C hg0
  have hfinW : Finite (twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
      (iterateFrobenius L 2 1)) := finite_twModel hg0C hg0
  have hWM := le_langModel_E8_of_le_twModel K L hFr hg0C hg0
    (P := twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
      (iterateFrobenius L 2 1)) le_rfl
  have hMeq : langModel Tag.E8 K L g0 = Wm L := le_antisymm hMW hWM
  let ε : adjointGroup Tag.E8 K ≃* Wm L :=
    (((adjointGroup Tag.E8 K).equivMapOfInjective _
      (baseChangeGL_injective (algebraMap K L))).trans
      ((MulAut.conj g0⁻¹).subgroupMap _)).trans (MulEquiv.subgroupCongr hMeq)
  have hεapp : ∀ x : adjointGroup Tag.E8 K, ((ε x : Wm L) : ModGL Tag.E8 L) =
      g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) * g0 := fun x => by
    have h : ((ε x : Wm L) : ModGL Tag.E8 L) =
        (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K)) := rfl
    rw [h, MulAut.conj_apply, inv_inv]
  obtain ⟨t, htT, hte⟩ := hdT
  have hεt : ((ε d : Wm L) : ModGL Tag.E8 L) = t := by
    rw [hεapp, ← hte]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have htW : t ∈ twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
      (iterateFrobenius L 2 1) := twistedTorus_le_twModel _ _ htT
  have htTor : t ∈ torusGroup Tag.E8 L := (mem_twistedTorusOf.1 htT).1
  obtain ⟨c, hc⟩ := exists_phi5_of_mem_twModel hζ iterateFrobenius_two_one htW htTor
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hd1
    have h1 : ((ε d : Wm L) : ModGL Tag.E8 L) = 1 := by
      rw [hεt, hc, xc_zero, d5_zero]
    have h2 : ε d = 1 := Subtype.ext h1
    exact ε.injective (h2.trans ε.map_one.symm)
  have hεd : ε d = phiAdd (phiW ζ hζ) c := Subtype.ext (hεt.trans hc)
  have hcore := gLAPPrimeCoreOf_centralizer_phiW (L := L) hζ hc0
  rw [← hεd] at hcore
  exact (gLAPPrimeCoreOf_centralizer_eq_bot_iff5 ε d).2 hcore

theorem langTorusPlaneBalance_E8_four_five_two :
    LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => q = 2 := by
  intro K _ _ hK Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  have hK' : Nat.card K = 2 := hK
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D₀, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hall
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)) :=
    mulAut_conj_injective_adjointGroup
  have hbot := gLAPPrimeCoreOf_centralizer_eq_bot_E8_five_two hK' hFr hg0C hg0 (d := d) hd1
    (htor d hdD)
  have hHeq : H ⊓ Subgroup.centralizer {(MulAut.conj d : MulAut (adjointGroup Tag.E8 K))} =
      innerAut (adjointGroup Tag.E8 K) ⊓
        Subgroup.centralizer {(MulAut.conj d : MulAut (adjointGroup Tag.E8 K))} := by
    ext φ
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨mem_innerAut_of_card_two hK' (Or.inr rfl) φ, h.2⟩, fun h => ⟨hH h.1, h.2⟩⟩
  refine localDeltaIn_eq_bot_of_core_eq_bot (d := (MulAut.conj d : MulAut (adjointGroup Tag.E8 K)))
    (Subgroup.mem_map_of_mem _ hdD) (fun h => hd1 (hinj (h.trans (map_one _).symm))) ?_
  rw [hHeq, inner_inf_centralizer_conj hinj, gLAPPrimeCoreOf_map_of_injective 5 _ hinj, hbot,
    Subgroup.map_bot]

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
