module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1415Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def ATypeOK (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ m : ℕ, 10 ≤ m → Nonempty (T ≃* alternatingGroup (Fin m)) → False

theorem ATypeOK.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ATypeOK p T) : ATypeOK p T' := fun m hm ⟨f⟩ => h m hm ⟨e.trans f⟩

abbrev ATypeThree (T : Type) [Group T] : Prop := ATypeOK 3 T

theorem atypeThree_of_equiv : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → ATypeThree T →
    ATypeThree T' := fun _ _ _ _ e h => ATypeOK.of_mulEquiv e h

@[expose] def ACompOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    ATypeOK p (PSimple p I)

theorem ACompOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : ACompOK p k) : ACompOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact (h _ hI').of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm

theorem ACompOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : ACompOK p k) : ACompOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem acompOK_of_no_comp {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    ACompOK p k := fun I hI => (h I hI).elim

theorem acompOK_of_pConstrained {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p
      (Subgroup.centralizer ({k} : Set Q))) : ACompOK p k :=
  acompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_pConstrained hp h hI

theorem acompOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → ATypeOK p T) : ACompOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem acompOK_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → ATypeOK p T) {k : Q} (hk : orderOf k = p) :
    ACompOK p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

@[expose] def I1415Row (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → ATypeOK p (PSimple p J)

theorem arow_of_model {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → ACompOK p k) : I1415Row s p := by
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
  have := ACompOK.of_mulEquiv hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem arow_of_model_not_sq_dvd {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p ^ 2 ∣ Nat.card Q) : I1415Row s p :=
  arow_of_model hOut b hnc fun k hk => acompOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hk hd hI

theorem dvd_card_alt {m : ℕ} (hm : 10 ≤ m) : 1814400 ∣ m.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hm
  rw [hk, show Nat.factorial 10 = 2 * 1814400 by decide, mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact dvd_mul_right _ _

theorem atypeOK_of_not_dvd_card {p : ℕ} {T : Type} [Group T] (h : ¬ 1814400 ∣ Nat.card T) :
    ATypeOK p T := fun m hm ⟨e⟩ => h (by
  rw [Nat.card_congr e.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega)]
  exact dvd_card_alt hm)

theorem atypeOK_of_card_lt {p : ℕ} {T : Type} [Group T] (h : Nat.card T < 1814400) :
    ATypeOK p T := fun m hm ⟨e⟩ => by
  have hc := (Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega))
  have h2 : 2 ≤ m.factorial := le_trans (by omega) (Nat.self_le_factorial m)
  have := Nat.le_of_dvd (Nat.div_pos h2 (by norm_num)) (dvd_card_alt hm)
  omega

theorem atypeOK_of_card_ne {p : ℕ} {T : Type} [Group T]
    (h : ∀ m, 10 ≤ m → m.factorial / 2 ≠ Nat.card T) : ATypeOK p T := fun m hm ⟨e⟩ =>
  h m hm ((Nat.card_congr e.toEquiv).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega))).symm

theorem atypeOK_of_card_eq {p : ℕ} {T : Type} [Group T] {N : ℕ} (hT : Nat.card T = N)
    (hNlt : N < 2 ^ 200 := by norm_num)
    (hA : ∀ m < 60, 10 ≤ m → m.factorial / 2 ≠ N := by decide +kernel) : ATypeOK p T := by
  refine atypeOK_of_card_ne fun m hm => ?_
  rw [hT]
  by_cases h60 : m < 60
  · exact hA m h60 hm
  · have h1 : Nat.factorial 60 / 2 ≤ m.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le (by omega))
    have h2 : 2 ^ 200 < Nat.factorial 60 / 2 := by decide +kernel
    omega

theorem atypeOK_of_card (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {p : ℕ}
    {T : Type} [Group T] [Finite T] {N : ℕ} (hT : Nat.card T = N) (_hN0 : 0 < N)
    (hNlt : N < 2 ^ 200)
    (_hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ p → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (_h3 : p ≠ 3 → N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (_h5 : p ≠ 5 → N ≠ 60)
    (hA : ∀ m < 60, 10 ≤ m → m.factorial / 2 ≠ N := by decide +kernel) : ATypeOK p T :=
  atypeOK_of_card_eq hT hNlt hA

theorem atypeOK_A5 {p : ℕ} (_hp : p = 3 ∨ p = 5) {T : Type} [Group T]
    (e : T ≃* ↥(alternatingGroup (Fin 5))) : ATypeOK p T :=
  atypeOK_of_card_lt (by
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 5 (by norm_num)]
    decide)

theorem atypeOK_A6 (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type}
    [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) : ATypeOK 3 T :=
  atypeOK_of_card_lt (by
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 6 (by norm_num)]
    decide)

theorem acompOK_of_not_dvd_card {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (hk : orderOf k = p)
    (h : ¬ p * 1814400 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q))) : ACompOK p k :=
  fun I hI => atypeOK_of_not_dvd_card fun hd => h ((Nat.mul_dvd_mul_left p hd).trans
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.prime_mul_card_pSimple_dvd_cent hp hk hI.1))

theorem arow_of_model_card {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p * 1814400 ∣ Nat.card Q) : I1415Row s p :=
  arow_of_model hOut b hnc fun k hk => acompOK_of_not_dvd_card hp hk fun h =>
    hd (h.trans (Subgroup.card_subgroup_dvd_card _))

section NotSq

theorem arow_of_card
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p * 1814400 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : I1415Row s p := by
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
  exact @arow_of_model_card s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)

theorem arow_of_not_sq_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : I1415Row s p := by
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
  exact @arow_of_model_not_sq_dvd s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)

end NotSq

end CFSG.LocalAnalysis.GLTheoremA.I1415Rows
