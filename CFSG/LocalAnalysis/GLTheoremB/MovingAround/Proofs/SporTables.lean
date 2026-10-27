module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1419b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSeven
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterFiveBGood
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB7
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporHN3
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)

section Framework

@[expose] def CentTypes (p : ℕ) (Good : ∀ (T : Type) [Group T], Prop) (Q : Type) [Group Q] : Prop :=
  ∀ s : Q, orderOf s = p → ∀ I : Subgroup Q,
    GLAPComponent p (Subgroup.centralizer ({s} : Set Q)) I → Good (PSimple p I)

@[expose] def SporTypes (p : ℕ) (Good : ∀ (T : Type) [Group T], Prop) (name : TauCeti.SporadicName) :
    Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    CentTypes p Good T

@[expose] def TypeInv (Good : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T'

theorem typeInv_card (R : ℕ → Prop) : TypeInv fun T _ => R (Nat.card T) := by
  intro T T' _ _ e h
  rwa [← Nat.card_congr e.toEquiv]

theorem CentTypes.of_equiv {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (hG : TypeInv Good) {Q T : Type} [Group Q] [Group T] [Finite T] (e : T ≃* Q)
    (h : CentTypes p Good Q) : CentTypes p Good T := by
  intro s hs I hI
  have hs' : orderOf (e s) = p := by rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨hI', ⟨f⟩⟩ := comp_transport hp e hI
  exact hG _ _ f.symm (h (e s) hs' _ hI')

theorem CentTypes.mono {p : ℕ} {Good Good' : ∀ (T : Type) [Group T], Prop}
    (hG : ∀ (T : Type) [Group T], Good T → Good' T) {Q : Type} [Group Q] (h : CentTypes p Good Q) :
    CentTypes p Good' Q :=
  fun s hs I hI => hG _ (h s hs I hI)

theorem CentTypes.and {p : ℕ} {Good Good' : ∀ (T : Type) [Group T], Prop} {Q : Type} [Group Q]
    (h : CentTypes p Good Q) (h' : CentTypes p Good' Q) :
    CentTypes p (fun T _ => Good T ∧ Good' T) Q :=
  fun s hs I hI => ⟨h s hs I hI, h' s hs I hI⟩

theorem sporTypes_of_model {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (hG : TypeInv Good) {name : TauCeti.SporadicName} {Q : Type} [Group Q]
    (e : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (h : CentTypes p Good Q) :
    SporTypes p Good name := by
  intro T _ _ ⟨f⟩
  exact h.of_equiv hp hG (f.trans e.symm)

theorem sporTypes_of_subgroup_model {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (hG : TypeInv Good) {name : TauCeti.SporadicName} {G₀ : Type} [Group G₀] {H : Subgroup G₀}
    (e : (TauCeti.CFSGIndex.sporadic name).Group ≃* ↥H) (h : CentTypes p Good ↥H) :
    SporTypes p Good name := by
  intro T _ _ ⟨f⟩
  exact h.of_equiv hp hG (f.trans e)

theorem SporTypes.mono {p : ℕ} {Good Good' : ∀ (T : Type) [Group T], Prop}
    (hG : ∀ (T : Type) [Group T], Good T → Good' T) {name : TauCeti.SporadicName}
    (h : SporTypes p Good name) : SporTypes p Good' name :=
  fun T _ _ hT => (h T hT).mono hG

theorem sporNoAltDown_of_types {p m : ℕ} {Good : ∀ (T : Type) [Group T], Prop}
    {name : TauCeti.SporadicName} (h : SporTypes p Good name)
    (hG : ∀ (T : Type) [Group T], Good T → IsEmpty (T ≃* alternatingGroup (Fin m))) :
    SporNoAltDown p m name :=
  fun T _ _ hT s hs I hI => hG _ (h T hT s hs I hI)

theorem sporNoAltDown_of_card {p m : ℕ} (hm : 2 ≤ m) {R : ℕ → Prop} {name : TauCeti.SporadicName}
    (h : SporTypes p (fun T _ => R (Nat.card T)) name) (hR : ¬ R (m.factorial / 2)) :
    SporNoAltDown p m name :=
  sporNoAltDown_of_types h fun T _ hT => ⟨fun e => hR (by
    rwa [Nat.card_congr e.toEquiv, card_alt m hm] at hT)⟩

theorem sporNoOmegaDown_of_types {p : ℕ} {ε : Bool} {n : ℕ} {Good : ∀ (T : Type) [Group T], Prop}
    {name : TauCeti.SporadicName} (h : SporTypes p Good name)
    (hG : ∀ (T : Type) [Group T] [Finite T], Good T → ¬ IsOmegaTwo ε (n + 1) T) :
    Inputs1419b.SporNoOmegaDown p ε n name :=
  fun T _ _ hT s hs I hI => hG _ (h T hT s hs I hI)

theorem card_of_isOmegaTwo {ε : Bool} {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsOmegaTwo ε (n + 1) X) : Nat.card X = OmegaFacts.omegaOrd ε (n + 1) := by
  rcases OmegaFacts.omega_data hX with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h, -⟩
  · omega
  · omega
  · omega
  · omega
  · exact h

theorem sporNoOmegaDown_of_card {p : ℕ} {ε : Bool} {n : ℕ} (hn : 2 ≤ n) {R : ℕ → Prop}
    {name : TauCeti.SporadicName} (h : SporTypes p (fun T _ => R (Nat.card T)) name)
    (hR : ¬ R (OmegaFacts.omegaOrd ε (n + 1))) : Inputs1419b.SporNoOmegaDown p ε n name :=
  sporNoOmegaDown_of_types h fun T _ _ hT hΩ => hR (by rwa [card_of_isOmegaTwo hn hΩ] at hT)

theorem centTypes_of_card {p : ℕ} (hp : p.Prime) {P : ℕ → Prop}
    (hP : ∀ a b : ℕ, 0 < b → a ∣ b → P b → P a) {Q : Type} [Group Q] [Finite Q]
    (h : ∀ s : Q, orderOf s = p → P (Nat.card (Subgroup.centralizer ({s} : Set Q)))) :
    CentTypes p (fun T _ => P (p * Nat.card T)) Q :=
  fun s hs _ hI => hP _ _ Nat.card_pos (Inputs1419b.mul_card_pSimple_dvd hp hs hI) (h s hs)

theorem centTypes_of_card_le {p : ℕ} (hp : p.Prime) {B : ℕ} {Q : Type} [Group Q] [Finite Q]
    (h : ∀ s : Q, orderOf s = p → Nat.card (Subgroup.centralizer ({s} : Set Q)) ≤ B) :
    CentTypes p (fun T _ => p * Nat.card T ≤ B) Q :=
  centTypes_of_card (P := fun b => b ≤ B) hp (fun _ _ hb hab h => (Nat.le_of_dvd hb hab).trans h) h

theorem centTypes_of_not_dvd {p : ℕ} (hp : p.Prime) {d : ℕ} {Q : Type} [Group Q] [Finite Q]
    (h : ∀ s : Q, orderOf s = p → ¬ d ∣ Nat.card (Subgroup.centralizer ({s} : Set Q))) :
    CentTypes p (fun T _ => ¬ d ∣ p * Nat.card T) Q :=
  centTypes_of_card (P := fun b => ¬ d ∣ b) hp (fun _ _ _ hab h hd => h (hd.trans hab)) h

theorem centTypes_of_centShapeRk' {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {Q : Type} [Group Q] (h : CFSG.HardMathSupport.Dickson.I271.CentShapeRk' p Good Rk Q) : CentTypes p Good Q := by
  intro s hs I hI
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; exact hp.one_lt.ne' hs.symm
  have hsp : s ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  rcases h s hs1 hsp with hc | ⟨J, -, hu, hg, -⟩
  · exact (hc I hI).elim
  · rw [hu I hI]
    exact hg

theorem centTypes_of_centShapeRk {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeRk p Good Rk Q) : CentTypes p Good Q :=
  centTypes_of_centShapeRk' hp (CFSG.HardMathSupport.Dickson.I271.CentShapeRk.toWeak hp h)

theorem centTypes_of_centShape {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    {Q : Type} [Group Q] [Finite Q] (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q) :
    CentTypes p Good Q := by
  intro s hs I hI
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; exact hp.one_lt.ne' hs.symm
  have hsp : s ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  rcases h s hs1 hsp with hc | ⟨J, -, hu, hg⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · rw [hu I hI]
    exact hg

theorem centTypes_of_centShapeMulti {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeMulti p Good Rk Q) : CentTypes p Good Q := by
  intro s hs I hI
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs; exact hp.one_lt.ne' hs.symm
  have hsp : s ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  rcases h.1 s hs1 hsp with hc | ⟨L, -, -, hgood⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · exact (hgood I hI).1

theorem typeInv_goodSpor (p : ℕ) (names : List TauCeti.SporadicName) :
    TypeInv (CFSG.HardMathSupport.Dickson.I271.GoodSpor p names) :=
  fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.I271.GoodSpor.of_equiv e h

theorem typeInv_catalogIs (P : TauCeti.CFSGIndex → Prop) : TypeInv fun T _ => catalogIs T P := by
  rintro T T' _ _ e ⟨i, hi, ⟨f⟩⟩
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem card_of_catalogIs_sporadic (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    {s : TauCeti.SporadicName} (h : catalogIs T (· = .sporadic s)) : Nat.card T = sporOrd s := by
  obtain ⟨i, rfl, ⟨f⟩⟩ := h
  exact (Nat.card_congr f.toEquiv).trans (hOrd s)

theorem card_of_catalogIs_sporadic_or (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    {s t : TauCeti.SporadicName} (h : catalogIs T (fun i => i = .sporadic s ∨ i = .sporadic t)) :
    Nat.card T = sporOrd s ∨ Nat.card T = sporOrd t := by
  obtain ⟨i, rfl | rfl, ⟨f⟩⟩ := h
  · exact Or.inl ((Nat.card_congr f.toEquiv).trans (hOrd s))
  · exact Or.inr ((Nat.card_congr f.toEquiv).trans (hOrd t))

theorem sporTypes_of_census {p : ℕ} (hp : p.Prime) (hBr : SporadicBridges) {s : TauCeti.SporadicName}
    {P : TauCeti.CFSGIndex → Prop}
    (h : CFSG.HardMathSupport.Dickson.BMRows.PCompCensus p (CFSG.Blueprint.NativeSporadic.Carrier s) P) :
    SporTypes p (fun T _ => catalogIs T P) s :=
  sporTypes_of_model hp (typeInv_catalogIs P) (hBr s).some h
end Framework

section Level

theorem sporTypes_of_downLe {p j : ℕ} (hp : p.Prime) {name : TauCeti.SporadicName}
    (hD : CFSG.LocalAnalysis.GLTheoremA.DownLe p j (TauCeti.CFSGIndex.sporadic name).Group) :
    SporTypes p (fun T _ => kLevel p T ≤ j) name := by
  intro T _ _ ⟨f⟩ s hs I hI
  obtain ⟨hI', ⟨g⟩⟩ := comp_transport hp f hI
  have hs' : f s ^ p = 1 := by rw [← map_pow, ← hs, pow_orderOf_eq_one, map_one]
  have hα : MulAut.conj (f s) ^ p = 1 := by rw [← map_pow, hs', map_one]
  have h := hD (MulAut.conj (f s)) hα (I.map f.toMonoidHom) (by rw [fixSubgroup_conj]; exact hI')
  rwa [CFSG.LocalAnalysis.GLTheoremA.KDSpor.kLevel_congr g.symm p] at h

theorem k2Lie_five {d : TauCeti.LieTypeIndex} (h : k2Lie 5 d) :
    d = .tits ∨ d = .reeF4 2 ∨ d = .suzuki 2 := by
  unfold k2Lie at h
  split at h <;> simp_all

theorem two_lt_kLevel_five_of_card (hb : LieOrderBridge) (hOrd : SporadicOrdersTable) {T : Type}
    [Group T] [Finite T] (hT : Nat.card T = 25920) : 2 < kLevel 5 T := by
  have hC : ¬ IsChevSimple 5 T :=
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb (q := 5) (a := 1) (m := 5184)
      Nat.prime_five (by norm_num) (by rw [hT]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK2 : ¬ catalogIs T (k2 5) := by
    rintro ⟨i, hi, ⟨g⟩⟩
    cases i with
    | cyclic q hq => exact hi.elim
    | alternating n hn => simp [k2] at hi
    | lie idx =>
      have h := hb idx T ⟨g⟩
      rw [hT] at h
      obtain ⟨d, hd⟩ := idx
      simp only [k2] at hi
      rcases k2Lie_five hi with rfl | rfl | rfl <;>
        simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula] at h <;>
        revert h <;> decide +kernel
    | sporadic s =>
      have h1 := Nat.card_congr g.toEquiv
      rw [hT, hOrd s] at h1
      revert h1
      cases s <;> simp only [k2, k2Spor] at hi <;> first | (exfalso; omega) | decide +kernel
  have hK3 : ¬ catalogIs T (k3 5) := by
    rintro ⟨i, hi, -⟩
    cases i <;> simp [k3] at hi
  unfold kLevel
  rw [if_neg hC, if_neg hK2, if_neg hK3]
  norm_num

end Level

section Fi22Five

set_option linter.unusedSectionVars false

section S_sporTypes_Fi22_five


theorem sporTypes_Fi22_five : SporTypes 5 (fun T _ => Nat.card T ∣ 60) .Fi22 := by
  intro T _ _ hT s hs I hI
  obtain ⟨eL⟩ := SporFacts.input14_21_holds T hT s hs
  have hIL : I ≤ GLAPLayer 5 (Subgroup.centralizer ({s} : Set T)) := le_sSup hI
  have hL : Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({s} : Set T))) = 60 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hdvd : Nat.card (PSimple 5 I) ∣ Nat.card I :=
    (Subgroup.card_quotient_dvd_card (Subgroup.center (PQuot 5 I))).trans
      (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 5 ↥I))
  exact hdvd.trans (hL ▸ Subgroup.card_dvd_of_le hIL)


theorem sporNoAltDown_Fi22_five_seven : SporNoAltDown 5 7 .Fi22 :=
  sporNoAltDown_of_card (R := fun N => N ∣ 60) (by norm_num) sporTypes_Fi22_five (by decide)

end S_sporTypes_Fi22_five

end Fi22Five

section Co1Seven

set_option linter.unusedSectionVars false

section S_sporTypes_Co1_seven


theorem sporTypes_Co1_seven (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporTypes 7 (fun T _ => 7 * Nat.card T ≤ 17640) .Co1 := by
  have : Finite ↥CFSG.Sporadic.Co1Schreier.GA :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1Schreier.card_GA_eq]; norm_num)
  exact sporTypes_of_subgroup_model (p := 7) (by norm_num) (typeInv_card fun N => 7 * N ≤ 17640)
    ((hBr .Co1).some.symm.trans CFSG.Sporadic.Co1Block.co1MatEquiv)
    (centTypes_of_card_le (by norm_num) Inputs1415b.card_centralizer_seven_GA_le)

end S_sporTypes_Co1_seven

end Co1Seven

section Fi24Seven

set_option linter.unusedSectionVars false

section S_sporTypes_Fi24_seven


theorem sporTypes_Fi24_seven (hOrd : SporadicOrdersTable)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporTypes 7 (fun T _ => 7 * Nat.card T ≤ 17640) .Fi24Prime := by
  have e : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group ≃* ↥CFSG.Sporadic.Fi24.J :=
    (hBr .Fi24Prime).some.symm.trans CFSG.Sporadic.Fi24.fi24EquivJ
  haveI := Inputs1415b.finite_spor hOrd .Fi24Prime
  haveI : Finite ↥CFSG.Sporadic.Fi24.J := Finite.of_equiv _ e.toEquiv
  refine sporTypes_of_subgroup_model (p := 7) (by norm_num) (typeInv_card fun N => 7 * N ≤ 17640) e
    (centTypes_of_card_le (by norm_num) fun s hs => ?_)
  obtain ⟨g, hg | hg⟩ := CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_conj_class s hs
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq g s, hg,
      CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_Y7]
    norm_num
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq g s, hg,
      CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_C7]
    norm_num

end S_sporTypes_Fi24_seven

end Fi24Seven

section ThSeven

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

local notation "z7" => slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6

section S_card_centralizer_seven_Th_le


theorem card_centralizer_seven_Th_le (s : ↥J) (hs : orderOf s = 7) :
    Nat.card (Subgroup.centralizer ({s} : Set ↥J)) ≤ 1176 := by
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hz := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven.card_centralizer_z7_le
  have hcen : ∀ s : ↥J, orderOf s = 7 → ∃ c : ↥J, c * s * c⁻¹ = z7 := by
    refine Inputs1415b.exists_conj_of_pair (z := z7) (matJ_injective ?_) h7x h7y hx1 hpow ?_
      (fun i j hi hj hij => ?_)
    · simp only [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.matJ_mul]
      exact hcomm
    · rw [CFSG.Sporadic.Th.Max3.natCard_J,
        show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
        factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)]
    · obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
      refine ⟨m, matJ_injective ?_⟩
      simp only [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.matJ_mul,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.matJ_pow] at hm ⊢
      exact hm
  obtain ⟨c, hc⟩ := hcen s hs
  rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq c s, hc]
  exact hz


theorem sporTypes_Th_seven (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SporTypes 7 (fun T _ => 7 * Nat.card T ≤ 1176) .Th := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  exact sporTypes_of_subgroup_model (p := 7) (by norm_num) (typeInv_card fun N => 7 * N ≤ 1176)
    ((hBr .Th).some.symm.trans thEquivJ)
    (centTypes_of_card_le (by norm_num) card_centralizer_seven_Th_le)

end S_card_centralizer_seven_Th_le

end ThSeven

section BSeven

set_option linter.unusedSectionVars false

section S_sporTypes_B_seven


theorem sporTypes_B_seven
    (hBr : SporadicBridges) : SporTypes 7 (fun T _ => Nat.card T ∣ 80640) .B := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  exact sporTypes_of_model (p := 7) (by norm_num) (typeInv_card fun N => N ∣ 80640) (hBr .B).some
    CFSG.HardMathSupport.Dickson.BMRows.census_B_seven

end S_sporTypes_B_seven

end BSeven

section OmegaSeven

set_option linter.unusedSectionVars false

theorem sporNoOmegaDown_Co1_seven
    (hBr : SporadicBridges) : Inputs1419b.SporNoOmegaDown 7 true 3 .Co1 :=
  sporNoOmegaDown_of_card (R := fun N => 7 * N ≤ 17640) (by norm_num) (sporTypes_Co1_seven hBr)
    (by decide +kernel)

theorem sporNoOmegaDown_Fi24_seven
    (hOrd : SporadicOrdersTable) (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 7 true 3 .Fi24Prime :=
  sporNoOmegaDown_of_card (R := fun N => 7 * N ≤ 17640) (by norm_num) (sporTypes_Fi24_seven hOrd hBr)
    (by decide +kernel)

theorem sporNoOmegaDown_Th_seven
    (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 7 true 3 .Th :=
  sporNoOmegaDown_of_card (R := fun N => 7 * N ≤ 1176) (by norm_num) (sporTypes_Th_seven hBr)
    (by decide +kernel)

end OmegaSeven

section LevelFive

theorem sporNoOmegaDown_five_of_row (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    {name : TauCeti.SporadicName} (hrow : CFSG.LocalAnalysis.GLTheoremA.KDSporRow name 5)
    (hk2 : k2 5 (TauCeti.CFSGIndex.sporadic name)) : Inputs1419b.SporNoOmegaDown 5 false 2 name :=
  sporNoOmegaDown_of_types (sporTypes_of_downLe Nat.prime_five (hrow.1 hk2)) fun T _ _ hT hΩ => by
    have hc : Nat.card T = 25920 := by
      rw [card_of_isOmegaTwo (le_refl 2) hΩ]
      exact OmegaFacts.omegaOrd_three_minus
    have := two_lt_kLevel_five_of_card hb hOrd hc
    omega

theorem sporNoOmegaDown_HN_five
    (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .HN :=
  sporNoOmegaDown_five_of_row hb hOrd (CFSG.LocalAnalysis.GLTheoremA.KDSpor.kdSporRow_HN_five hOut hBr)
    (by simp [k2, k2Spor])

theorem sporNoOmegaDown_Ly_five
    (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .Ly :=
  sporNoOmegaDown_five_of_row hb hOrd (CFSG.LocalAnalysis.GLTheoremA.KDSpor.kdSporRow_Ly_five hOut hBr)
    (by simp [k2, k2Spor])

theorem sporNoOmegaDown_Th_five
    (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .Th :=
  sporNoOmegaDown_five_of_row hb hOrd (CFSG.LocalAnalysis.GLTheoremA.KDSpor.kdSporRow_Th_five hOut hBr)
    (by simp [k2, k2Spor])

end LevelFive

section Fi23Five

set_option linter.unusedSectionVars false

section S_centTypes_Fi23J_five


set_option maxRecDepth 100000 in
theorem centTypes_Fi23J_five :
    CentTypes 5 (fun T _ => Nat.card T ≤ 5040) CFSG.Sporadic.Fi23.J := by
  intro s hs I hI
  exact (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.card_pSimple_five s hs hI).2


set_option maxRecDepth 100000 in
theorem sporTypes_Fi23_five (hBr : SporadicBridges) :
    SporTypes 5 (fun T _ => Nat.card T ≤ 5040) .Fi23 := by
  haveI hJ : Finite CFSG.Sporadic.Fi23.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  haveI hf : Finite CFSG.Blueprint.NativeSporadic.Fi23 :=
    Finite.of_equiv CFSG.Sporadic.Fi23.J
      (CFSG.Sporadic.Fi23.fi23EquivJ : CFSG.Blueprint.NativeSporadic.Fi23 ≃* CFSG.Sporadic.Fi23.J).symm.toEquiv
  have hC : CentTypes 5 (fun T _ => Nat.card T ≤ 5040) CFSG.Blueprint.NativeSporadic.Fi23 :=
    @CentTypes.of_equiv 5 Nat.prime_five (fun T _ => Nat.card T ≤ 5040) (typeInv_card fun N => N ≤ 5040)
      CFSG.Sporadic.Fi23.J CFSG.Blueprint.NativeSporadic.Fi23 (inferInstance : Group CFSG.Sporadic.Fi23.J)
      (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi23) hf CFSG.Sporadic.Fi23.fi23EquivJ
      centTypes_Fi23J_five
  exact sporTypes_of_model Nat.prime_five (typeInv_card fun N => N ≤ 5040) (hBr .Fi23).some hC


theorem sporNoOmegaDown_Fi23_five (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .Fi23 :=
  sporNoOmegaDown_of_card (R := fun N => N ≤ 5040) (le_refl 2) (sporTypes_Fi23_five hBr) (by decide +kernel)

end S_centTypes_Fi23J_five

end Fi23Five

section Helpers

theorem factorial_half_ne_of_lt {k N : ℕ} (h1 : k.factorial / 2 < N) (h2 : N < (k + 1).factorial / 2)
    (n : ℕ) : n.factorial / 2 ≠ N := by
  intro h
  rcases Nat.lt_or_ge k n with hkn | hkn
  · have := Inputs1415b.half_factorial_le (show k + 1 ≤ n by omega)
    omega
  · have := Inputs1415b.half_factorial_le hkn
    omega

end Helpers

section MSeven

set_option linter.unusedSectionVars false

section S_sporTypes_M_seven


theorem sporTypes_M_seven
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) :
    SporTypes 7 (fun T _ => Nat.card T = 4030387200) .M :=
  (sporTypes_of_census (by norm_num) hBr CFSG.HardMathSupport.Dickson.BMRows.census_M_seven).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h


theorem sporNoAltDown_M_seven
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) (m : ℕ) (hm : 2 ≤ m) :
    SporNoAltDown 7 m .M :=
  sporNoAltDown_of_card (R := fun N => N = 4030387200) hm (sporTypes_M_seven hBr hOrd)
    (factorial_half_ne_of_lt (k := 13) (by decide) (by decide) m)


theorem sporNoOmegaDown_M_seven
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) :
    Inputs1419b.SporNoOmegaDown 7 true 3 .M :=
  sporNoOmegaDown_of_card (R := fun N => N = 4030387200) (by norm_num) (sporTypes_M_seven hBr hOrd)
    (by decide +kernel)

end S_sporTypes_M_seven

end MSeven

section BFive

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_sFiveA
  gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot sFiveA)
open CFSG.Monster.B.Pinned (zFive)

section S_centTypes_B_five


theorem centTypes_B_five
    (hOrd : SporadicOrdersTable) :
    CentTypes 5 (fun T _ => Nat.card T = 44352000 ∨ ¬ 7 ∣ 5 * Nat.card T) CFSG.Blueprint.NativeSporadic.B := by
  haveI hfin : Finite CFSG.Blueprint.NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hGood : TypeInv CFSG.HardMathSupport.Dickson.BMRows.CensusB5.IsHS :=
    fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.BMRows.CensusB5.IsHS.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨E, hEC, ⟨eE⟩⟩ := tabBFiveAHS_of_cert
  have hA : ShapeRkAt' 5 CFSG.HardMathSupport.Dickson.BMRows.CensusB5.IsHS (fun _ _ => True) sFiveA :=
    CFSG.HardMathSupport.Dickson.BMRows.CensusB5.shapeRkAt'_isHS_five orderOf_sFiveA
      gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot hEC eE TabBFiveCent.tabBFiveACard_holds
  intro y hy I hI
  obtain ⟨c, hc, g, hg | hg⟩ := tabBFive_hconj y hy
  · right
    intro h7
    have h1 := Inputs1419b.mul_card_pSimple_dvd Nat.prime_five hy hI
    have h2 : Nat.card ↥(Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) =
        Nat.card ↥(Subgroup.centralizer ({zFive} : Set CFSG.Blueprint.NativeSporadic.B)) := by
      rw [← hg, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq,
        centralizer_singleton_eq_of_zpowers_eq
          (zpowers_pow_eq_of_orderOf_five CFSG.RankThree.Native.bFiveRel.orderOf_z hc)]
    exact TabMFive.not_seven_dvd_card_centralizer_zFive (h2 ▸ h7.trans h1)
  · left
    have hS : ShapeRkAt' 5 CFSG.HardMathSupport.Dickson.BMRows.CensusB5.IsHS (fun _ _ => True) y := by
      subst hg
      exact shapeRkAt'_conj Nat.prime_five hGood hRk g _
        (shapeRkAt'_of_zpowers_eq (zpowers_pow_eq_of_orderOf_five orderOf_sFiveA hc).symm hA)
    rcases hS with hno | ⟨J, -, hu, hgd, -⟩
    · exact (hno I hI).elim
    · rw [hu I hI]
      obtain ⟨f⟩ := hgd
      exact (Nat.card_congr f.toEquiv).trans (hOrd .HS)


theorem sporTypes_B_five
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) :
    SporTypes 5 (fun T _ => Nat.card T = 44352000 ∨ ¬ 7 ∣ 5 * Nat.card T) .B := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  exact sporTypes_of_model (p := 5) Nat.prime_five
    (typeInv_card fun N => N = 44352000 ∨ ¬ 7 ∣ 5 * N) (hBr .B).some (centTypes_B_five hOrd)


theorem sporNoAltDown_B_five
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) (m : ℕ) (hm : 7 ≤ m) :
    SporNoAltDown 5 m .B := by
  refine sporNoAltDown_of_card (R := fun N => N = 44352000 ∨ ¬ 7 ∣ 5 * N) (by omega)
    (sporTypes_B_five hBr hOrd) ?_
  rintro (h | h)
  · exact factorial_half_ne_of_lt (k := 11) (by decide) (by decide) m h
  · exact h (Dvd.dvd.mul_left (Inputs1415b.prime_dvd_half_factorial (by norm_num) (by norm_num) hm) 5)


theorem sporNoOmegaDown_B_five_ten
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) :
    Inputs1419b.SporNoOmegaDown 5 true 4 .B :=
  sporNoOmegaDown_of_card (R := fun N => N = 44352000 ∨ ¬ 7 ∣ 5 * N) (by norm_num) (sporTypes_B_five hBr hOrd)
    (by decide +kernel)

end S_centTypes_B_five

end BFive

section MFive

set_option linter.unusedSectionVars false

section S_sporTypes_M_five


theorem sporTypes_M_five
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M :=
  (sporTypes_of_census Nat.prime_five hBr
    (CFSG.HardMathSupport.Dickson.BMRows.census_M_five_of_noComp hB)).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_M_five

section S_sporTypes_M_five_of_kGroup


theorem sporTypes_M_five_of_kGroup
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M :=
  (sporTypes_of_census Nat.prime_five hBr (CFSG.HardMathSupport.Dickson.BMRows.census_M_five
      (hK.of_surjective (hBr .M).some.symm.toMonoidHom (hBr .M).some.symm.surjective))).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_M_five_of_kGroup

section S_sporNoAltDown_M_five_of


theorem sporNoAltDown_M_five_of
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M))
    (m : ℕ) (hm : 2 ≤ m) : SporNoAltDown 5 m .M :=
  sporNoAltDown_of_card (R := fun N => N = 273030912000000) hm (sporTypes_M_five hBr hOrd hB)
    (factorial_half_ne_of_lt (k := 17) (by decide) (by decide) m)

end S_sporNoAltDown_M_five_of

section S_sporNoAltDown_M_five_of_kGroup


theorem sporNoAltDown_M_five_of_kGroup
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) (m : ℕ)
    (hm : 2 ≤ m) (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) : SporNoAltDown 5 m .M :=
  sporNoAltDown_of_card (R := fun N => N = 273030912000000) hm (sporTypes_M_five_of_kGroup hBr hOrd hK)
    (factorial_half_ne_of_lt (k := 17) (by decide) (by decide) m)

end S_sporNoAltDown_M_five_of_kGroup

section S_sporNoOmegaDown_M_five_of


theorem sporNoOmegaDown_M_five_of
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .M :=
  sporNoOmegaDown_of_card (R := fun N => N = 273030912000000) (le_refl 2) (sporTypes_M_five hBr hOrd hB)
    (by decide +kernel)


theorem sporNoOmegaDown_M_five_ten_of
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    Inputs1419b.SporNoOmegaDown 5 true 4 .M :=
  sporNoOmegaDown_of_card (R := fun N => N = 273030912000000) (by norm_num) (sporTypes_M_five hBr hOrd hB)
    (by decide +kernel)

end S_sporNoOmegaDown_M_five_of

end MFive

section MThree

set_option linter.unusedSectionVars false

section S_sporTypes_M_three


theorem sporTypes_M_three (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp) :
    SporTypes 3 (fun T _ => Nat.card T = 1255205709190661721292800 ∨ Nat.card T = 90745943887872000) .M :=
  (sporTypes_of_census Nat.prime_three hBr
    (CFSG.HardMathSupport.Dickson.BMRows.census_M_three_of_noComp hB)).mono
    fun _ _ h => card_of_catalogIs_sporadic_or hOrd h

end S_sporTypes_M_three

section S_sporTypes_M_three_of_kGroup


theorem sporTypes_M_three_of_kGroup (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    SporTypes 3 (fun T _ => Nat.card T = 1255205709190661721292800 ∨ Nat.card T = 90745943887872000) .M :=
  (sporTypes_of_census Nat.prime_three hBr (CFSG.HardMathSupport.Dickson.BMRows.census_M_three
      (hK.of_surjective (hBr .M).some.symm.toMonoidHom (hBr .M).some.symm.surjective))).mono
    fun _ _ h => card_of_catalogIs_sporadic_or hOrd h

end S_sporTypes_M_three_of_kGroup

section S_factorial_half_ne_fi24_th

theorem factorial_half_ne_fi24_th (m : ℕ) :
    ¬ (m.factorial / 2 = 1255205709190661721292800 ∨ m.factorial / 2 = 90745943887872000) := by
  rintro (h | h)
  · exact factorial_half_ne_of_lt (k := 24) (by decide) (by decide) m h
  · exact factorial_half_ne_of_lt (k := 19) (by decide) (by decide) m h

end S_factorial_half_ne_fi24_th

section S_sporNoAltDown_M_three_of


theorem sporNoAltDown_M_three_of (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp) (m : ℕ) (hm : 2 ≤ m) : SporNoAltDown 3 m .M :=
  sporNoAltDown_of_card (R := fun N => N = 1255205709190661721292800 ∨ N = 90745943887872000) hm
    (sporTypes_M_three hBr hOrd hB) (factorial_half_ne_fi24_th m)

end S_sporNoAltDown_M_three_of

section S_sporNoAltDown_M_three_of_kGroup


theorem sporNoAltDown_M_three_of_kGroup (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) (m : ℕ)
    (hm : 2 ≤ m) (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) : SporNoAltDown 3 m .M :=
  sporNoAltDown_of_card (R := fun N => N = 1255205709190661721292800 ∨ N = 90745943887872000) hm
    (sporTypes_M_three_of_kGroup hBr hOrd hK) (factorial_half_ne_fi24_th m)

end S_sporNoAltDown_M_three_of_kGroup

end MThree

section BThree

set_option linter.unusedSectionVars false

section S_sporTypes_B_three


theorem sporTypes_B_three (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB3 : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp) :
    SporTypes 3 (fun T _ => Nat.card T = 64561751654400) .B :=
  (sporTypes_of_census Nat.prime_three hBr
    (CFSG.HardMathSupport.Dickson.BMRows.census_B_three_of_noComp hB3)).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_B_three

section S_sporTypes_B_three_of_kGroup


theorem sporTypes_B_three_of_kGroup
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    SporTypes 3 (fun T _ => Nat.card T = 64561751654400) .B :=
  (sporTypes_of_census Nat.prime_three hBr (CFSG.HardMathSupport.Dickson.BMRows.census_B_three
      (hK.of_surjective (hBr .B).some.symm.toMonoidHom (hBr .B).some.symm.surjective))).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_B_three_of_kGroup

section S_sporNoAltDown_B_three_of


theorem sporNoAltDown_B_three_of (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB3 : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp) (m : ℕ) (hm : 2 ≤ m) : SporNoAltDown 3 m .B :=
  sporNoAltDown_of_card (R := fun N => N = 64561751654400) hm (sporTypes_B_three hBr hOrd hB3)
    (factorial_half_ne_of_lt (k := 16) (by decide) (by decide) m)

end S_sporNoAltDown_B_three_of

section S_sporNoAltDown_B_three_of_kGroup


theorem sporNoAltDown_B_three_of_kGroup
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable) (m : ℕ)
    (hm : 2 ≤ m) (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) : SporNoAltDown 3 m .B :=
  sporNoAltDown_of_card (R := fun N => N = 64561751654400) hm (sporTypes_B_three_of_kGroup hBr hOrd hK)
    (factorial_half_ne_of_lt (k := 16) (by decide) (by decide) m)

end S_sporNoAltDown_B_three_of_kGroup

end BThree

section Co1Five

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabCo1
open CFSG.Sporadic.Co1Schreier (GA)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (GOK)

section S_card_centralizer_five_GA_le


theorem card_centralizer_five_GA_le (s : ↥GA) (hs : orderOf s = 5) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set ↥GA)) ≤ 3024000 := by
  have hG : GOK := Certificates.certificate13670
  obtain ⟨c, h0 | h1 | h5⟩ := tabCo1_census hG s hs
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq c s]
    exact card_cent_fiveA_le _ h0
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq c s]
    exact (card_cent_fiveB_le _ h1).trans (by norm_num)
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq c s]
    exact (card_cent_fiveC_le _ h5).trans (by norm_num)

end S_card_centralizer_five_GA_le

section S_sporTypes_Co1_five


theorem sporTypes_Co1_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) :
    SporTypes 5 (fun T _ => 5 * Nat.card T ≤ 3024000 ∧ GoodSpor 5 [.J2] T) .Co1 := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  have hG : GOK := Certificates.certificate13670
  have hC : CentTypes 5 (fun T _ => 5 * Nat.card T ≤ 3024000 ∧ GoodSpor 5 [.J2] T) ↥GA :=
    (centTypes_of_card_le Nat.prime_five card_centralizer_five_GA_le).and
      (centTypes_of_centShapeMulti Nat.prime_five (tabCo1_centShapeMulti hOut hG))
  exact sporTypes_of_subgroup_model (p := 5) Nat.prime_five
    (fun T T' _ _ e h => ⟨(Nat.card_congr e.toEquiv) ▸ h.1, GoodSpor.of_equiv e h.2⟩)
    ((hBr .Co1).some.symm.trans CFSG.Sporadic.Co1Block.co1MatEquiv) hC

end S_sporTypes_Co1_five

section S_sporNoOmegaDown_Co1_five


theorem sporNoOmegaDown_Co1_five (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hBr : SporadicBridges) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .Co1 := by
  refine sporNoOmegaDown_of_types (sporTypes_Co1_five hOut hBr) fun T _ _ hT hΩ => ?_
  have hc : Nat.card T = 25920 := by
    rw [card_of_isOmegaTwo (le_refl 2) hΩ]
    exact OmegaFacts.omegaOrd_three_minus
  rcases hT.2 with (⟨hC, -, -⟩ | ⟨n, hn5, -, -, ⟨f⟩⟩) | ⟨h3, -⟩ | ⟨S, hS, ⟨f⟩⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb (q := 5) (a := 1)
      (m := 5184) Nat.prime_five (by norm_num) (by rw [hc]; norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hC
  · have h1 := Nat.card_congr f.toEquiv
    rw [hc, card_alt n (by omega)] at h1
    exact factorial_half_ne_of_lt (k := 8) (by decide) (by decide) n h1.symm
  · omega
  · simp only [List.mem_singleton] at hS
    subst hS
    have h1 := Nat.card_congr f.toEquiv
    rw [hc, hOrd] at h1
    simp [sporOrd] at h1

end S_sporNoOmegaDown_Co1_five

end Co1Five

section ARow

theorem sporNoAltDown_of_arow {s : TauCeti.SporadicName} {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 10 ≤ m)
    {Q : Type} [Group Q] (hQ : IsSimpleGroup Q) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : CFSG.LocalAnalysis.GLTheoremA.I1415Rows.I1415Row s p) : SporNoAltDown p m s := by
  intro T _ _ hT x hx I hI
  obtain ⟨e⟩ := hT
  refine ⟨fun f => h T ⟨e⟩ hp hp2 (MulAut.conj x) ?_ ?_ I ?_ m hm ⟨f⟩⟩
  · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  · intro h1
    let φ : T ≃* Q := e.trans b.symm
    have hZ : Subgroup.center Q = ⊥ := by
      haveI := hQ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hc | hc
      · exact hc
      · exfalso
        obtain ⟨a, c, hac⟩ := hnc
        exact hac ((Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top c) a))
    have hcent : φ x ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun α : MulAut T => α (φ.symm g)) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      have h3 : φ.symm g * x = x * φ.symm g := by
        calc φ.symm g * x = (x * φ.symm g * x⁻¹) * x := by rw [h2]
          _ = x * φ.symm g := by group
      have h4 := congrArg φ h3
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h4
      exact h4
    rw [hZ, Subgroup.mem_bot] at hcent
    have hx1 : x = 1 := φ.injective (by rw [hcent, map_one])
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  · rwa [CFSG.LocalAnalysis.GLTheoremA.KDSpor.fixSubgroup_conj_eq]

end ARow

section ARowCo1

set_option linter.unusedSectionVars false

section S_sporNoAltDown_Co1_three


theorem sporNoAltDown_Co1_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) (m : ℕ) (hm : 10 ≤ m) : SporNoAltDown 3 m .Co1 := by
  obtain ⟨-, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hBr
  exact sporNoAltDown_of_arow Nat.prime_three (by norm_num) hm hs hnc b
    (CFSG.HardMathSupport.Dickson.I271.TabCo1.arow_Co1_three hOut hBr)

end S_sporNoAltDown_Co1_three

section S_sporNoAltDown_Co1_five


theorem sporNoAltDown_Co1_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) (m : ℕ) (hm : 10 ≤ m) : SporNoAltDown 5 m .Co1 := by
  obtain ⟨-, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hBr
  exact sporNoAltDown_of_arow Nat.prime_five (by norm_num) hm hs hnc b
    (CFSG.HardMathSupport.Dickson.I271.TabCo1.arow_Co1_five hOut hBr)

end S_sporNoAltDown_Co1_five

end ARowCo1

section ARowHN

set_option linter.unusedSectionVars false

section S_sporNoAltDown_HN_three


set_option maxRecDepth 100000 in
theorem sporNoAltDown_HN_three (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) (hb : LieOrderBridge) (m : ℕ) (hm : 10 ≤ m) : SporNoAltDown 3 m .HN := by
  have hfin : Finite ↥CFSG.Sporadic.HNSchreier.JH := by
    have : Nat.card ↥CFSG.Sporadic.HNSchreier.JH ≠ 0 := by rw [CFSG.Sporadic.HNSchreier.card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  have e : CFSG.Blueprint.NativeSporadic.HN ≃* ↥CFSG.Sporadic.HNSchreier.JH := CFSG.Sporadic.HNSchreier.hnEquivJ
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HNSchreier.JH :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HNSchreier.fam_hn_certified_simplicity.2 e.symm
  have hpr : ¬ (Nat.card ↥CFSG.Sporadic.HNSchreier.JH).Prime := by
    rw [CFSG.Sporadic.HNSchreier.card_JH]; norm_num
  have hnc : ∃ a c : ↥CFSG.Sporadic.HNSchreier.JH, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥CFSG.Sporadic.HNSchreier.JH _ hfin hs hpr
  have b : ↥CFSG.Sporadic.HNSchreier.JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := e.symm.trans (hBr .HN).some
  exact sporNoAltDown_of_arow Nat.prime_three (by norm_num) hm hs hnc b
    (CFSG.HardMathSupport.Dickson.I271.I1415AHN3.arow_HN_three hOut hBr hb)

end S_sporNoAltDown_HN_three

end ARowHN

section Residuals

@[expose] def MElevenNoSeven : Prop :=
  ¬ 7 ∣ Nat.card ↥(Subgroup.centralizer
    ({CFSG.AGLEmbedding.Norton.MON5_7.gw CFSG.AGLEmbedding.Norton.Gen11.gen11W0} :
      Set CFSG.Monster.Generated.Gmat))

@[expose] def MFiveBNoComp : Prop :=
  ∀ J : Subgroup CFSG.Monster.Generated.Gmat,
    ¬ GLAPComponent 5 (Subgroup.centralizer
      ({CFSG.HardMathSupport.Dickson.I271.xFiveB} : Set CFSG.Monster.Generated.Gmat)) J

@[expose] def Fi24FiveA9 : Prop :=
  ∀ x : CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime, orderOf x = 5 →
    ∀ I : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime),
      GLAPComponent 5 (Subgroup.centralizer
        ({x} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime))) I →
      Nat.card (PSimple 5 I) = 181440

end Residuals

section MEleven

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.AGLEmbedding.Norton.MON5_7 (gw)
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0 gen11W1 gen11W2 gen11W3)
open CFSG.Monster.Generated (Gmat)

section S_centTypes_Gmat_eleven


theorem centTypes_Gmat_eleven (h : MElevenNoSeven) :
    CentTypes 11 (fun T _ => ¬ 7 ∣ 11 * Nat.card T) Gmat := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  refine centTypes_of_not_dvd (by norm_num) fun s hs => ?_
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hx, hy, hxy, hx1, h3, h4, -, -⟩ := CFSG.AGLEmbedding.Norton.MON11_13.eleven_gw_facts
  have hy3 := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven.eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  obtain ⟨g, k, hgk⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_conj_pow_of_eleven_lines
    (x₃ := gw gen11W2) (x₄ := gw gen11W3) hx hy hxy
    (by rw [h3, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq])
    (by rw [hy3, mul_inv_cancel_right]) (by rw [h4, mul_inv_cancel_right])
    (by rw [hrot, mul_inv_cancel_right]) hx1
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal.factorization_Gmat_eleven hs
  have hk1 : gw gen11W0 ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hgk
    rw [hgk, orderOf_one] at hs
    norm_num at hs
  rw [hgk, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal.orderOf_x11 hk1]
  exact h

end S_centTypes_Gmat_eleven

section S_sporTypes_M_eleven


theorem sporTypes_M_eleven (h : MElevenNoSeven) : SporTypes 11 (fun T _ => ¬ 7 ∣ 11 * Nat.card T) .M := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨e1⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact sporTypes_of_subgroup_model (p := 11) (by norm_num) (typeInv_card fun N => ¬ 7 ∣ 11 * N) e1.symm
    (centTypes_Gmat_eleven h)

end S_sporTypes_M_eleven

section S_sporNoAltDown_M_eleven_of


theorem sporNoAltDown_M_eleven_of (h : MElevenNoSeven) (m : ℕ) (hm : 7 ≤ m) : SporNoAltDown 11 m .M :=
  sporNoAltDown_of_card (R := fun N => ¬ 7 ∣ 11 * N) (by omega) (sporTypes_M_eleven h)
    (fun h7 => h7 (Dvd.dvd.mul_left (Inputs1415b.prime_dvd_half_factorial (by norm_num) (by norm_num) hm) 11))


theorem sporNoOmegaDown_M_eleven_of (h : MElevenNoSeven) : Inputs1419b.SporNoOmegaDown 11 false 5 .M :=
  sporNoOmegaDown_of_card (R := fun N => ¬ 7 ∣ 11 * N) (by norm_num) (sporTypes_M_eleven h)
    (by decide +kernel)

end S_sporNoAltDown_M_eleven_of

end MEleven

section MFiveB

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Monster.Generated (Gmat)
open CFSG.Monster.Existence (MGriess)

section S_centFiveBNoComp_M_of_xFiveB


theorem centFiveBNoComp_M_of_xFiveB (h5B : MFiveBNoComp) :
    CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* CFSG.Blueprint.NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  haveI : Finite MGriess :=
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.twoA_data_of_existence
      CFSG.Milestones.cl_lit_monster_existence_griess_conway).1
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) := Finite.of_equiv MGriess e.toEquiv
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hG : CentFiveBNoComp Gmat := by
    intro x hx hinv J hJ
    obtain ⟨j, hj, hxj⟩ := MonsterFiveB.m5bClass_of_certs x hx hinv
    obtain ⟨c, hc⟩ := isConj_iff.1 hxj
    have h1 := glaPComponent_map_equiv Nat.prime_five (MulAut.conj c) hJ
    rw [map_centralizer_singleton (MulAut.conj c) x] at h1
    have h4 : (MulAut.conj c) x = xFiveB ^ j := by simpa [MulAut.conj_apply] using hc
    rw [h4] at h1
    obtain ⟨P, -, hord, -⟩ := sylowData_xFiveB
    have hx5 : xFiveB ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_coprime Nat.prime_five hx5 hj]
      at h1
    exact h5B _ h1
  exact CentFiveBNoComp.of_equiv e.symm (CentFiveBNoComp.of_equiv φ hG)

end S_centFiveBNoComp_M_of_xFiveB

end MFiveB

section BFiveB

set_option linter.unusedSectionVars false

section S_sporTypes_B_five_of_noComp


theorem sporTypes_B_five_of_noComp
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp) :
    SporTypes 5 (fun T _ => Nat.card T = 44352000) .B :=
  (sporTypes_of_census Nat.prime_five hBr (CFSG.HardMathSupport.Dickson.BMRows.census_B_five_of_noComp hB)).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_B_five_of_noComp

section S_sporTypes_B_five_of_kGroup


theorem sporTypes_B_five_of_kGroup
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    SporTypes 5 (fun T _ => Nat.card T = 44352000) .B :=
  (sporTypes_of_census Nat.prime_five hBr (CFSG.HardMathSupport.Dickson.BMRows.census_B_five
      (hK.of_surjective (hBr .B).some.symm.toMonoidHom (hBr .B).some.symm.surjective))).mono
    fun _ _ h => card_of_catalogIs_sporadic hOrd h

end S_sporTypes_B_five_of_kGroup

section S_sporNoOmegaDown_B_five_of


theorem sporNoOmegaDown_B_five_of
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (hB : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp) :
    Inputs1419b.SporNoOmegaDown 5 false 2 .B :=
  sporNoOmegaDown_of_card (R := fun N => N = 44352000) (le_refl 2) (sporTypes_B_five_of_noComp hBr hOrd hB)
    (by decide +kernel)

end S_sporNoOmegaDown_B_five_of

end BFiveB

section Fi24Five

theorem sporTypes_Fi24_five (hOrd : SporadicOrdersTable) (hBr : SporadicBridges) (h : Fi24FiveA9) :
    SporTypes 5 (fun T _ => Nat.card T = 181440) .Fi24Prime := by
  haveI := Inputs1415b.finite_carrier hOrd hBr .Fi24Prime
  exact sporTypes_of_model (p := 5) Nat.prime_five (typeInv_card fun N => N = 181440) (hBr .Fi24Prime).some h

theorem sporNoAltDown_Fi24_five_seven (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (h : Fi24FiveA9) : SporNoAltDown 5 7 .Fi24Prime :=
  sporNoAltDown_of_card (R := fun N => N = 181440) (by norm_num) (sporTypes_Fi24_five hOrd hBr h) (by decide)

theorem sporNoOmegaDown_Fi24_five (hOrd : SporadicOrdersTable) (hBr : SporadicBridges)
    (h : Fi24FiveA9) : Inputs1419b.SporNoOmegaDown 5 false 2 .Fi24Prime :=
  sporNoOmegaDown_of_card (R := fun N => N = 181440) (le_refl 2) (sporTypes_Fi24_five hOrd hBr h)
    (by decide +kernel)

end Fi24Five

structure OpenAtRest2 : Prop where
  m_11 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group → MElevenNoSeven

structure Open1314Rest : Prop where
  fi24_5 : Fi24FiveA9
  m_5 : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)
  m_11 : MElevenNoSeven

structure SporOmegaRest : Prop where
  fi24_5 : Fi24FiveA9
  b_5 : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp
  m_5 : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)
  m_11 : MElevenNoSeven

section Assembly

set_option linter.unusedSectionVars false

section S_sporNoOmegaDown_B_seven


theorem sporNoOmegaDown_B_seven
    : Inputs1419b.SporNoOmegaDown 7 true 3 .B :=
  sporNoOmegaDown_of_card (R := fun N => N ∣ 80640) (by norm_num)
    (sporTypes_B_seven CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group) (by decide +kernel)

end S_sporNoOmegaDown_B_seven

section S_openAtRest_of_rest2


theorem openAtRest_of_rest2
    (h : OpenAtRest2) : Inputs1415c.OpenAtRest where
  co1_3 := ⟨sporNoAltDown_Co1_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group 12 (by norm_num),
    sporNoAltDown_Co1_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group 15 (by norm_num)⟩
  co1_5 := ⟨sporNoAltDown_Co1_five CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group 10 le_rfl,
    sporNoAltDown_Co1_five CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group 15 (by norm_num)⟩
  hn_3 := sporNoAltDown_HN_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    12 (by norm_num)
  b_3 := fun hK => ⟨sporNoAltDown_B_three_of_kGroup CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds 12 (by norm_num) hK,
    sporNoAltDown_B_three_of_kGroup CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds 15 (by norm_num) hK⟩
  b_5 := fun m hm _ _ => sporNoAltDown_B_five CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds m (by omega)
  m_3 := fun m hm _ hK =>
    sporNoAltDown_M_three_of_kGroup CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds m (by omega) hK
  m_5 := fun m hm _ hK =>
    sporNoAltDown_M_five_of_kGroup CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds m (by omega) hK
  m_7 := fun m _ hm _ _ => sporNoAltDown_M_seven CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds m (by omega)
  m_11 := fun m hm _ hK => sporNoAltDown_M_eleven_of (h.m_11 hK) m (by omega)

end S_openAtRest_of_rest2

section S_open1314_of_rest


theorem open1314_of_rest
    (h : Open1314Rest) : Inputs1415b.Open1314 where
  fi22_5 := sporNoAltDown_Fi22_five_seven
  fi24_5 := sporNoAltDown_Fi24_five_seven CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group h.fi24_5
  b_5 := sporNoAltDown_B_five CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds 7 le_rfl
  m_5 := sporNoAltDown_M_five_of CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds h.m_5 7 (by norm_num)
  m_11 := sporNoAltDown_M_eleven_of h.m_11 13 (by norm_num)

end S_open1314_of_rest

section S_sporOmegaTableOpen_of_rest


theorem sporOmegaTableOpen_of_rest
    (h : SporOmegaRest) : Inputs1419b.SporOmegaTableOpen := by
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hBr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  intro name ε n p hmem
  simp only [Inputs1419b.sporOmegaCasesOpen, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact sporNoOmegaDown_HN_five hb hOrd hOut hBr
  · exact sporNoOmegaDown_Ly_five hb hOrd hOut hBr
  · exact sporNoOmegaDown_Th_five hb hOrd hOut hBr
  · exact sporNoOmegaDown_Fi23_five hBr
  · exact sporNoOmegaDown_Co1_five hb hOrd hOut hBr
  · exact sporNoOmegaDown_Fi24_five hOrd hBr h.fi24_5
  · exact sporNoOmegaDown_B_five_of hBr hOrd h.b_5
  · exact sporNoOmegaDown_M_five_of hBr hOrd h.m_5
  · exact sporNoOmegaDown_Th_seven hBr
  · exact sporNoOmegaDown_Co1_seven hBr
  · exact sporNoOmegaDown_Fi24_seven hOrd hBr
  · exact sporNoOmegaDown_B_seven
  · exact sporNoOmegaDown_M_seven hBr hOrd
  · exact sporNoOmegaDown_B_five_ten hBr hOrd
  · exact sporNoOmegaDown_M_five_ten_of hBr hOrd h.m_5
  · exact sporNoOmegaDown_M_eleven_of h.m_11

end S_sporOmegaTableOpen_of_rest

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables

end
