module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2Grid
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporNoComp
public import CFSG.Milestones.CAT_native_realization
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def CTypeOK (p : ℕ) (T : Type) [Group T] : Prop :=
  IsChevSimple 2 T → catalogIs T chev2Spor

theorem CTypeOK.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : CTypeOK p T) : CTypeOK p T' := fun hc => by
  obtain ⟨i, hi, ⟨f⟩⟩ := h (CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm hc)
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

abbrev CTypeThree (T : Type) [Group T] : Prop := CTypeOK 3 T

theorem ctypeThree_of_equiv : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → CTypeThree T →
    CTypeThree T' := fun _ _ _ _ e h => CTypeOK.of_mulEquiv e h

@[expose] def CCompOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    CTypeOK p (PSimple p I)

theorem CCompOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : CCompOK p k) : CCompOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact (h _ hI').of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm

theorem CCompOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : CCompOK p k) : CCompOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem ccompOK_of_no_comp {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    CCompOK p k := fun I hI => (h I hI).elim

theorem ccompOK_of_pConstrained {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p
      (Subgroup.centralizer ({k} : Set Q))) : CCompOK p k :=
  ccompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_pConstrained hp h hI

theorem ccompOK_of_solvable {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({k} : Set Q))) : CCompOK p k :=
  ccompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_solvable hp h hI

theorem ccompOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → CTypeOK p T) : CCompOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem ccompOK_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → CTypeOK p T) {k : Q} (hk : orderOf k = p) :
    CCompOK p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

@[expose] def CRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → CTypeOK p (PSimple p J)

theorem crow_of_model {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → CCompOK p k) : CRow s p := by
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
  have := CCompOK.of_mulEquiv hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem crow_of_model_not_sq_dvd {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p ^ 2 ∣ Nat.card Q) : CRow s p :=
  crow_of_model hOut b hnc fun k hk => ccompOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hk hd hI

open CFSG.LocalAnalysis.GLTheoremA.LieGrid in
theorem ctypeOK_of_card_grid (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {p : ℕ} {T : Type} [Group T] [Finite T] {N : ℕ} {ps : List ℕ} (hT : Nat.card T = N)
    (hN0 : 0 < N) (hNlt : N < 2 ^ 60) (hps : N.primeFactorsList ⊆ ps) (hG : Chev2GridAt ps N) :
    CTypeOK p T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d =>
      exact ⟨.lie d, chev2Spor_of_lie (hps_of_subset (by omega) hps) hN0 hNlt hG d hi
        ((hb d T ⟨e⟩).symm.trans hT), ⟨e⟩⟩
    | _ => exact hi.elim
  · exact ⟨i, Or.inl (chev2Small_of_ambiguous hi), ⟨e⟩⟩

open CFSG.LocalAnalysis.GLTheoremA.LieGrid in
theorem ctypeOK_of_card_dvd (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {p : ℕ} {T : Type} [Group T] [Finite T] {N : ℕ} (hd : Nat.card T ∣ N) (hN0 : 0 < N)
    (hNlt : N < 2 ^ 60) (hG : ∀ M ∈ N.divisors, Chev2GridAt N.primeFactorsList M) :
    CTypeOK p T :=
  ctypeOK_of_card_grid hb rfl Nat.card_pos (lt_of_le_of_lt (Nat.le_of_dvd hN0 hd) hNlt)
    (Nat.primeFactorsList_subset_of_dvd hd (by omega))
    (hG _ (Nat.mem_divisors.2 ⟨hd, by omega⟩))

open CFSG.LocalAnalysis.GLTheoremA.LieGrid in
theorem ctypeOK_of_card (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {p : ℕ}
    {T : Type} [Group T] [Finite T] {N : ℕ} (hT : Nat.card T = N) (hN0 : 0 < N)
    (_hNlt : N < 2 ^ 200)
    (_hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ p → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (_h3 : p ≠ 3 → N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (_h5 : p ≠ 5 → N ≠ 60)
    (hNlt : N < 2 ^ 60 := by norm_num)
    (hG : Chev2GridAt N.primeFactorsList N := by
      simp only [Nat.primeFactorsList_ofNat]; decide +kernel) : CTypeOK p T :=
  ctypeOK_of_card_grid hb hT hN0 hNlt (List.Subset.refl _) hG

open CFSG.LocalAnalysis.GLTheoremA.LieGrid in
theorem ctypeOK_of_card_eq (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {p : ℕ} {T : Type} [Group T] [Finite T] {N : ℕ} (hT : Nat.card T = N)
    (hN0 : 0 < N := by norm_num) (hNlt : N < 2 ^ 60 := by norm_num)
    (hG : Chev2GridAt N.primeFactorsList N := by
      simp only [Nat.primeFactorsList_ofNat]; decide +kernel) : CTypeOK p T :=
  ctypeOK_of_card_grid hb hT hN0 hNlt (List.Subset.refl _) hG

theorem ctypeOK_A5 {p : ℕ} (_hp : p = 3 ∨ p = 5) {T : Type} [Group T]
    (e : T ≃* ↥(alternatingGroup (Fin 5))) : CTypeOK p T :=
  fun _ => ⟨.alternating 5 le_rfl, Or.inl (Or.inl rfl), ⟨e⟩⟩

theorem ctypeOK_A6 (_hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type}
    [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) : CTypeOK 3 T :=
  fun _ => ⟨.alternating 6 (Nat.le_succ 5), Or.inl (Or.inr (Or.inl rfl)), ⟨e⟩⟩

theorem ctypeOK_three_of_card_dvd_360
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (_hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 360) :
    CTypeOK 3 T :=
  ctypeOK_of_card_dvd hb hd (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)

theorem ctypeOK_three_of_card_dvd_720
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (_hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 720) :
    CTypeOK 3 T :=
  ctypeOK_of_card_dvd hb hd (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)

theorem ctypeOK_three_of_card_dvd_2520
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (_hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 2520) :
    CTypeOK 3 T :=
  ctypeOK_of_card_dvd hb hd (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)

theorem ctypeOK_of_card_168 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {p : ℕ} {T : Type} [Group T] [Finite T] (hc : Nat.card T = 168) : CTypeOK p T :=
  ctypeOK_of_card_grid hb hc (by norm_num) (by norm_num) (ps := [2, 3, 7])
    (by simp only [Nat.primeFactorsList_ofNat]; decide) (by decide +kernel)

theorem ctypeOK_five_of_card_360 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (hc : Nat.card T = 360) : CTypeOK 5 T :=
  ctypeOK_of_card_grid hb hc (by norm_num) (by norm_num) (ps := [2, 3, 5])
    (by simp only [Nat.primeFactorsList_ofNat]; decide) (by decide +kernel)

section NotSq

theorem crow_of_not_sq_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : CRow s p := by
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
  exact @crow_of_model_not_sq_dvd s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)

end NotSq

end CFSG.LocalAnalysis.GLTheoremA.Chev2Rows
