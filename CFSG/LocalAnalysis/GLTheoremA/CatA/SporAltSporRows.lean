module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Spor
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1411
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporNoComp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Milestones.CAT_native_realization
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def STypeOK (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ m : ℕ, 7 ≤ m → Nonempty (T ≃* alternatingGroup (Fin m)) → False

theorem STypeOK.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : STypeOK p T) : STypeOK p T' := fun m hm ⟨f⟩ => h m hm ⟨e.trans f⟩

abbrev STypeThree (T : Type) [Group T] : Prop := STypeOK 3 T

theorem stypeThree_of_equiv : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → STypeThree T →
    STypeThree T' := fun _ _ _ _ e h => STypeOK.of_mulEquiv e h

@[expose] def SCompOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    STypeOK p (PSimple p I)

theorem SCompOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : SCompOK p k) : SCompOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact (h _ hI').of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm

theorem SCompOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : SCompOK p k) : SCompOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem scompOK_of_no_comp {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    SCompOK p k := fun I hI => (h I hI).elim

theorem scompOK_of_pConstrained {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p
      (Subgroup.centralizer ({k} : Set Q))) : SCompOK p k :=
  scompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_pConstrained hp h hI

theorem scompOK_of_solvable {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({k} : Set Q))) : SCompOK p k :=
  scompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_solvable hp h hI

theorem scompOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → STypeOK p T) : SCompOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem scompOK_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → STypeOK p T) {k : Q} (hk : orderOf k = p) :
    SCompOK p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

@[expose] def SRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → STypeOK p (PSimple p J)

theorem srow_of_model {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → SCompOK p k) : SRow s p := by
  intro S _ _ ⟨e⟩ hp hp2 β hβ hβ1 K hK
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hK
  have hk : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq, hxo]
  have := SCompOK.of_mulEquiv hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem srow_of_model_not_sq_dvd {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p ^ 2 ∣ Nat.card Q) : SRow s p :=
  srow_of_model hOut b hnc fun k hk => scompOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hk hd hI

theorem dvd_card_alt {m : ℕ} (hm : 7 ≤ m) : 2520 ∣ m.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hm
  rw [hk, show Nat.factorial 7 = 2 * 2520 by decide, mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact dvd_mul_right _ _

theorem stypeOK_of_card_lt {p : ℕ} {T : Type} [Group T] (h : Nat.card T < 2520) :
    STypeOK p T := fun m hm ⟨e⟩ => by
  have hc := (Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega))
  have h2 : 2 ≤ m.factorial := le_trans (by omega) (Nat.self_le_factorial m)
  have := Nat.le_of_dvd (Nat.div_pos h2 (by norm_num)) (dvd_card_alt hm)
  omega

theorem stypeOK_of_card_ne {p : ℕ} {T : Type} [Group T]
    (h : ∀ m, 7 ≤ m → m.factorial / 2 ≠ Nat.card T) : STypeOK p T := fun m hm ⟨e⟩ =>
  h m hm ((Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega))).symm

theorem stypeOK_of_card_eq {p : ℕ} {T : Type} [Group T] {N : ℕ} (hT : Nat.card T = N)
    (hNlt : N < 2 ^ 200 := by norm_num)
    (hA : ∀ m < 60, 7 ≤ m → m.factorial / 2 ≠ N := by decide +kernel) : STypeOK p T := by
  refine stypeOK_of_card_ne fun m hm => ?_
  rw [hT]
  by_cases h60 : m < 60
  · exact hA m h60 hm
  · have h1 : Nat.factorial 60 / 2 ≤ m.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le (by omega))
    have h2 : 2 ^ 200 < Nat.factorial 60 / 2 := by decide +kernel
    omega

theorem stypeOK_of_card (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {p : ℕ}
    {T : Type} [Group T] [Finite T] {N : ℕ} (hT : Nat.card T = N) (_hN0 : 0 < N)
    (hNlt : N < 2 ^ 200)
    (_hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ p → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (_h3 : p ≠ 3 → N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (_h5 : p ≠ 5 → N ≠ 60)
    (hA : ∀ m < 60, 7 ≤ m → m.factorial / 2 ≠ N := by decide +kernel) : STypeOK p T :=
  stypeOK_of_card_eq hT hNlt hA

theorem stypeOK_A5 {p : ℕ} (_hp : p = 3 ∨ p = 5) {T : Type} [Group T]
    (e : T ≃* ↥(alternatingGroup (Fin 5))) : STypeOK p T :=
  stypeOK_of_card_lt (by
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 5 (by norm_num)]
    decide)

theorem stypeOK_A6 (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type}
    [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) : STypeOK 3 T :=
  stypeOK_of_card_lt (by
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 6 (by norm_num)]
    decide)

theorem stypeOK_three_of_card_dvd_360
    (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (_hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 360) :
    STypeOK 3 T :=
  stypeOK_of_card_lt ((Nat.le_of_dvd (by norm_num) hd).trans_lt (by norm_num))

theorem stypeOK_three_of_card_dvd_720
    (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (_hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 720) :
    STypeOK 3 T :=
  stypeOK_of_card_lt ((Nat.le_of_dvd (by norm_num) hd).trans_lt (by norm_num))

theorem stypeOK_three_of_card_168 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (_hnab : ∃ a b : T, a * b ≠ b * a) (hc : Nat.card T = 168) : STypeOK 3 T :=
  stypeOK_of_card_lt (by rw [hc]; norm_num)

theorem pSimple_equiv_of_isAltPType {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {m : ℕ}
    (hm : 5 ≤ m) (h : IsAltPType p J m) :
    Nonempty (PSimple p J ≃* ↥(alternatingGroup (Fin m))) := by
  obtain ⟨e⟩ := h
  have hcA : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hc : Nat.card (Subgroup.center (PQuot p J)) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcA, Subgroup.card_bot]
  obtain ⟨f⟩ := nonempty_pQuot_equiv_pSimple hc
  exact ⟨f.symm.trans e⟩

@[expose] def AltRow (m : ℕ) (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → IsAltPType 3 J m → False

theorem sporAltNoComp_iff (m : ℕ) : SporAltNoComp m ↔ ∀ s, AltRow m s := by
  constructor
  · intro h s S _ _ he β hβ hβ1 J hJ hA
    exact h S s he β hβ hβ1 J hJ hA
  · intro h S _ _ s he β hβ hβ1 J hJ hA
    exact h s S he β hβ hβ1 J hJ hA

theorem altRow_of_srow {m : ℕ} (hm : 7 ≤ m) {s : TauCeti.SporadicName} (h : SRow s 3) :
    AltRow m s := fun S _ _ he β hβ hβ1 J hJ hA =>
  h S he Nat.prime_three (by norm_num) β hβ hβ1 J hJ m hm (pSimple_equiv_of_isAltPType (by omega) hA)

@[expose] def NineRow (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 9)) → False

theorem nineRow_of_srow {s : TauCeti.SporadicName} (h : SRow s 3) : NineRow s :=
  fun S _ _ he β hβ hβ1 J hJ hA => h S he Nat.prime_three (by norm_num) β hβ hβ1 J hJ 9 (by norm_num) hA

section NotSq

theorem srow_of_not_sq_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : SRow s p := by
  obtain ⟨hfin, -, hsimp⟩ := CFSG.Milestones.native_carrier_finite_simple_of_ne_B s hsB
  have b : CFSG.Blueprint.NativeSporadic.nativeCarrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group := by
    cases s
    case B => exact absurd rfl hsB
    case M => exact absurd rfl hsM
    case M11 => exact (hbr .M11).some
    case M12 => exact (hbr .M12).some
    case M22 => exact (hbr .M22).some
    case M23 => exact (hbr .M23).some
    case M24 => exact (hbr .M24).some
    case J1 => exact (hbr .J1).some
    case J2 => exact (hbr .J2).some
    case J3 => exact (hbr .J3).some
    case J4 => exact (hbr .J4).some
    case HS => exact (hbr .HS).some
    case McL => exact (hbr .McL).some
    case He => exact (hbr .He).some
    case Ru => exact (hbr .Ru).some
    case Suz => exact (hbr .Suz).some
    case ONan => exact (hbr .ONan).some
    case Co1 => exact (hbr .Co1).some
    case Co2 => exact (hbr .Co2).some
    case Co3 => exact (hbr .Co3).some
    case Fi22 => exact (hbr .Fi22).some
    case Fi23 => exact (hbr .Fi23).some
    case Fi24Prime => exact (hbr .Fi24Prime).some
    case HN => exact (hbr .HN).some
    case Ly => exact (hbr .Ly).some
    case Th => exact (hbr .Th).some
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.nativeCarrier s) =
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr b.toEquiv).trans (hOrd s)
  have hnp : ¬ (CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s).Prime := by
    cases s <;> norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderJ3,
      CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1,
      CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy,
      CFSG.Open.orderTh, CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster]
  exact @srow_of_model_not_sq_dvd s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)

end NotSq

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
