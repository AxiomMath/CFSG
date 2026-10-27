module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeRk
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Rank
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PairCover

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

@[expose] def SporStrong (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X), CompHyp p K B → I271Norm p K B →
    I271SporType K name → IsStronglyBalancedIn p B K

theorem sporPair_of_sporStrong {name : TauCeti.SporadicName} {p : ℕ} (h : SporStrong name p) :
    SporPair name p :=
  fun X _ _ _ K B hH hN hS _ _ => Or.inr (h X K B (CompHyp.of_i271Hyp hH hN.1) hN hS)

@[expose] def IsA6At (p : ℕ) (T : Type) [Group T] : Prop :=
  p = 3 ∧ Nonempty (T ≃* ↥(alternatingGroup (Fin 6)))

@[expose] def GoodSpor (p : ℕ) (names : List TauCeti.SporadicName) (T : Type) [Group T] : Prop :=
  LeafType p T ∨ IsA6At p T ∨ ∃ S ∈ names, Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic S).Group)

theorem GoodSpor.of_equiv {p : ℕ} {names : List TauCeti.SporadicName} {T T' : Type} [Group T]
    [Group T'] (e : T ≃* T') (h : GoodSpor p names T) : GoodSpor p names T' := by
  rcases h with h | ⟨hp3, ⟨f⟩⟩ | ⟨S, hS, ⟨f⟩⟩
  · exact Or.inl (LeafType.of_equiv e h)
  · exact Or.inr (Or.inl ⟨hp3, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨S, hS, ⟨e.symm.trans f⟩⟩)

theorem rkAut_of_equiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : RkAut p T) :
    RkAut p T' := by
  intro β hβ
  have hβ' : (MulAut.congr e.symm β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  obtain ⟨E, hE, hEc, hEf⟩ := h _ hβ'
  have hZ : Nat.card (Subgroup.center T') = Nat.card (Subgroup.center T) := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  refine ⟨E.map e.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _, ?_, ?_⟩
  · rw [hZ, Subgroup.card_map_of_injective e.injective]; exact hEc
  · rintro _ ⟨x, hx, rfl⟩
    have := hEf x hx
    simp only [MulAut.congr_apply, MulEquiv.coe_toMonoidHom] at this ⊢
    have h2 := congrArg e this
    simpa using h2

@[expose] def RkSpor (p : ℕ) (names : List TauCeti.SporadicName) (T : Type) [Group T] : Prop :=
  ((p = 3 ∧ Nonempty ((T ⧸ Subgroup.center T) ≃* ↥(alternatingGroup (Fin 6)))) ∨
    ∃ S ∈ names, Nonempty ((T ⧸ Subgroup.center T) ≃* (TauCeti.CFSGIndex.sporadic S).Group)) →
    RkAut p T

theorem RkSpor.of_equiv {p : ℕ} {names : List TauCeti.SporadicName} {T T' : Type} [Group T]
    [Group T'] (e : T ≃* T') (h : RkSpor p names T) : RkSpor p names T' := by
  have eq : (T ⧸ Subgroup.center T) ≃* (T' ⧸ Subgroup.center T') :=
    QuotientGroup.congr (Subgroup.center T) (Subgroup.center T') e (Subgroup.map_center_eq e)
  rintro (⟨hp3, ⟨f⟩⟩ | ⟨S, hS, ⟨f⟩⟩)
  · exact rkAut_of_equiv e (h (Or.inl ⟨hp3, ⟨eq.trans f⟩⟩))
  · exact rkAut_of_equiv e (h (Or.inr ⟨S, hS, ⟨eq.trans f⟩⟩))

theorem strong_a6 {Y : Type} [Group Y] [Finite Y] {J B : Subgroup Y} (h : CompHyp 3 J B)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* ↥(alternatingGroup (Fin 6)))
    (hn : 3 ^ 2 ≤ autOrderIn B J) : IsStronglyBalancedIn 3 B J :=
  isStronglyBalancedIn_of_autBalanced h.elem h.quasi.1 e hn i271AutBalanceAltSix_holds

theorem strong_goodSpor {p : ℕ} {names : List TauCeti.SporadicName}
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p) {Y : Type} [Group Y] [Finite Y]
    {J B : Subgroup Y} (h : CompHyp p J B) (hG : GoodSpor p names (↥J ⧸ Subgroup.center ↥J))
    (hR : RkSpor p names ↥J) : IsStronglyBalancedIn p B J := by
  rcases hG with hL | ⟨hp3, ⟨e⟩⟩ | ⟨S, hS, ⟨e⟩⟩
  · exact strong_leaf hChev h hL
  · subst hp3
    exact strong_a6 h e
      (sq_le_autOrderIn_of_rkAut h.prime h.scp h.norm (hR (Or.inl ⟨rfl, ⟨e⟩⟩)))
  · exact hSp S hS Y J B h
      ⟨h.norm, sq_le_autOrderIn_of_rkAut h.prime h.scp h.norm (hR (Or.inr ⟨S, hS, ⟨e⟩⟩))⟩ ⟨e⟩

theorem strong_of_centShapeRk {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeRk p Good Rk (NativeSporadic.Carrier name)) {X : Type} [Group X] [Finite X]
    {K B : Subgroup X} (hC : CompHyp p K B) (hN : I271Norm p K B) (hS : I271SporType K name)
    (hZ : Subgroup.center ↥K = ⊥) : IsStronglyBalancedIn p B K := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eK : ↥K ≃* NativeSporadic.Carrier name :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e.trans (hBr name).some.symm)
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv ↥K eK.toEquiv
  have hshape : CentShapeRk p Good Rk ↥K := CentShapeRk.of_equiv hC.prime hGood hRk eK.symm hD
  refine strong_of_dichotomy_rk hGood hRk hOut hC hN ⟨e⟩ hloc hIH ?_
  intro a k hk haB hc haC
  obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hC.elem.2 a haB) haC hk hc
  have hk1 : (⟨k, hk⟩ : ↥K) ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
  have hkp1 : (⟨k, hk⟩ : ↥K) ^ p = 1 := by
    rw [hZ] at hkp
    exact Subgroup.mem_bot.1 hkp
  exact comp_dichotomy_rk hC.prime hq hk hc (hshape _ hk1 hkp1)

theorem sporStrong_of_centShapeRk {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeRk p Good Rk (NativeSporadic.Carrier name)) : SporStrong name p := by
  intro X _ _ K B hC hN hS
  exact strong_of_centShapeRk hGood hRk hOut hBr hP hIH hD hC hN hS
    (center_eq_bot_of_mult hSpM hC hS hm)

theorem sporStrong_of_goodSporShape {name : TauCeti.SporadicName}
    {p : ℕ} {names : List TauCeti.SporadicName} (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hm : ¬ p ∣ sporadicMultiplierOrder name) (hChev : ChevStrong p)
    (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : CentShapeRk p (GoodSpor p names) (RkSpor p names) (NativeSporadic.Carrier name)) :
    SporStrong name p :=
  sporStrong_of_centShapeRk (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) hOut hSpM hBr hP hm
    (fun _ _ _ _ _ h hG hR => strong_goodSpor hChev hSp h hG hR) hD

theorem sporStrong_of_centShape_cover {name : TauCeti.SporadicName} {p : ℕ}
    {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → IsStronglyBalancedIn p B' J)
    (hD : CentShape p Good (NativeSporadic.Carrier name)) : SporStrong name p := by
  intro X _ _ K B hC hN hS
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eS : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.Carrier name := e.trans (hBr name).some.symm
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv _ eS.toEquiv
  have hOall : OPrimeCoreTrivialAt p (↥K ⧸ Subgroup.center ↥K) := hP.1 _ ⟨eS⟩
  have hshape : CentShape p Good (↥K ⧸ Subgroup.center ↥K) :=
    CentShape.of_equiv hC.prime hGood eS.symm hD
  exact strong_of_centShape_cover hGood hOut hC hN ⟨e⟩ hloc hOall hIH hshape

theorem sporStrong_of_constrainedShape {name : TauCeti.SporadicName} {p : ℕ}
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hD : ConstrainedShape name p) : SporStrong name p :=
  sporStrong_of_centShape_cover (Good := fun _ _ => False) (fun _ _ _ _ _ h => h) hOut hBr hP
    (fun _ _ _ _ _ _ hG => hG.elim) (fun k hk1 hkp => Or.inl (hD k hk1 hkp))

theorem sporStrong_of_leafShape_cover
    {name : TauCeti.SporadicName} {p : ℕ} (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hChev : ChevStrong p) (hD : LeafShape name p) :
    SporStrong name p :=
  sporStrong_of_centShape_cover (fun _ _ _ _ e h => LeafType.of_equiv e h) hOut hBr hP
    (fun _ _ _ _ _ h hG => strong_leaf hChev h hG) hD

end CFSG.HardMathSupport.Dickson.I271
