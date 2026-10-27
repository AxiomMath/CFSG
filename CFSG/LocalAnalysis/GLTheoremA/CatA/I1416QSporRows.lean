module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Spor
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GH74.KGroups.A5
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporNoComp
public import CFSG.Milestones.CAT_native_realization
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416QRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def QTypeOK (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → IsChevSimple q T →
    (∃ A : Subgroup (MulAut T), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) → False

theorem QTypeOK.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : QTypeOK p T) : QTypeOK p T' := fun q hq hq2 hqp hc hA =>
  h q hq hq2 hqp (CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm hc)
    (i1416_elemAb_transfer e.symm hA)

abbrev QTypeThree (T : Type) [Group T] : Prop := QTypeOK 3 T

theorem qtypeThree_of_equiv : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → QTypeThree T →
    QTypeThree T' := fun _ _ _ _ e h => QTypeOK.of_mulEquiv e h

@[expose] def QCompOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    QTypeOK p (PSimple p I)

theorem QCompOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : QCompOK p k) : QCompOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact (h _ hI').of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm

theorem QCompOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : QCompOK p k) : QCompOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem qcompOK_of_no_comp {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    QCompOK p k := fun I hI => (h I hI).elim

theorem qcompOK_of_pConstrained {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p
      (Subgroup.centralizer ({k} : Set Q))) : QCompOK p k :=
  qcompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_pConstrained hp h hI

theorem qcompOK_of_solvable {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({k} : Set Q))) : QCompOK p k :=
  qcompOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_solvable hp h hI

theorem qcompOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → QTypeOK p T) : QCompOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem qcompOK_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → QTypeOK p T) {k : Q} (hk : orderOf k = p) :
    QCompOK p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

@[expose] def I1416QRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → QTypeOK p (PSimple p J)

theorem i1416QSporS_iff : I1416QSporS ↔ ∀ s p, I1416QRow s p := by
  constructor
  · intro h s p S _ _ he hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
    exact h S s he p hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
  · intro h S _ _ s he p hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA
    exact h s p S he hp hp2 β hβ hβ1 J hJ q hq hq2 hqp hc hA

theorem qrow_of_model {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → QCompOK p k) : I1416QRow s p := by
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
  have := QCompOK.of_mulEquiv hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem qrow_of_model_not_sq_dvd {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p ^ 2 ∣ Nat.card Q) : I1416QRow s p :=
  qrow_of_model hOut b hnc fun k hk => qcompOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hk hd hI

theorem sq_dvd_card_mulAut_of_elemAb {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    (h : ∃ A : Subgroup (MulAut T), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    p ^ 2 ∣ Nat.card (MulAut T) := by
  obtain ⟨A, ⟨-, hA⟩, hle⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut T) := Finite.of_injective _ DFunLike.coe_injective
  have hpg : IsPGroup p ↥A := fun g => ⟨1, Subtype.ext (by simpa using hA g g.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : p ^ n < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt hlt
    omega
  exact (pow_dvd_pow p hn2).trans (hn ▸ Subgroup.card_subgroup_dvd_card A)

theorem qtypeOK_of_not_sq_dvd_aut {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    (h : ¬ p ^ 2 ∣ Nat.card (MulAut T)) : QTypeOK p T :=
  fun _ _ _ _ _ hA => h (sq_dvd_card_mulAut_of_elemAb hp hA)

theorem prime_part_bound {q a m v M : ℕ} (hq : q.Prime) (hm : ¬ q ∣ m) (h4 : q ^ (2 * a) ≤ m)
    (h : q ^ a * m = q ^ v * M) : q ^ (2 * v) ≤ M := by
  have hq0 : 0 < q := hq.pos
  have hva : v ≤ a := by
    by_contra hva
    push Not at hva
    have h1 : q ^ (a + 1) ∣ q ^ a * m :=
      h ▸ (Nat.pow_dvd_pow q hva).mul_right M
    rw [pow_succ] at h1
    exact hm (Nat.dvd_of_mul_dvd_mul_left (by positivity) h1)
  have hM : M = q ^ (a - v) * m := by
    have h2 : q ^ a = q ^ v * q ^ (a - v) := by rw [← pow_add]; congr 1; omega
    rw [h2, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
  rw [hM]
  calc q ^ (2 * v) ≤ q ^ (2 * a) := Nat.pow_le_pow_right hq0 (by omega)
    _ ≤ m := h4
    _ ≤ q ^ (a - v) * m := Nat.le_mul_of_pos_left _ (by positivity)

theorem not_lie_char_of_card
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T] [Finite T]
    {q a m : ℕ} (hq : q.Prime) (hT : Nat.card T = q ^ a * m) (hm : ¬ q ∣ m)
    (h4 : q ^ (2 * a) ≤ m) :
    ¬ catalogIs T (onLie fun d => d.characteristic = q) := by
  rintro ⟨i, hi, ⟨e⟩⟩
  cases i with
  | lie d =>
    have hd : d.1.characteristic = q := hi
    have hn : Nat.card T = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
      hb d T ⟨e⟩
    obtain ⟨v, M, hv, hM⟩ := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part d.1 d.2
    rw [hd] at hv hM
    have := prime_part_bound hq hm h4 (hT.symm.trans (hn.trans hv))
    omega
  | _ => exact hi.elim

theorem amb_lie_order_odd {q : ℕ} (hq2 : q ≠ 2) (ld : TauCeti.LieTypeIndex) (hv : ld.Valid)
    (hi : ambiguousChev q (TauCeti.CFSGIndex.lie ⟨ld, hv⟩)) :
    q = 3 ∧ (CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula ld = 504 ∨
      CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula ld = 25920) := by
  open CFSG.HardMathSupport.Solomon.Coordinator.I1420 in
  cases ld with
  | A r k =>
    rcases r with _ | _ | r
    · simp [ambiguousChev] at hi
    · simp only [ambiguousChev] at hi
      rcases hi with ⟨-, h2⟩ | ⟨h8, h3⟩
      · exact (hq2 h2).elim
      · exact ⟨h3, Or.inl (by simp only [lieOrderFormula]; rw [h8]; norm_num [orderA])⟩
    · simp [ambiguousChev] at hi
  | twistedA r k =>
    rcases r with _ | _ | _ | _ | r
    · simp [ambiguousChev] at hi
    · simp [ambiguousChev] at hi
    · simp only [ambiguousChev] at hi
      exact (hq2 hi.2).elim
    · simp only [ambiguousChev] at hi
      obtain ⟨h2, h3⟩ := hi
      exact ⟨h3, Or.inr (by simp only [lieOrderFormula]; rw [h2]; decide)⟩
    · simp [ambiguousChev] at hi
  | _ => simp [ambiguousChev] at hi

theorem not_isChevSimple_of_card
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T] [Finite T]
    {q a m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hT : Nat.card T = q ^ a * m) (hm : ¬ q ∣ m)
    (h4 : q ^ (2 * a) ≤ m)
    (h3 : q = 3 → q ^ a * m ≠ 360 ∧ q ^ a * m ≠ 504 ∧ q ^ a * m ≠ 25920)
    (h5 : q = 5 → q ^ a * m ≠ 60) :
    ¬ IsChevSimple q T := by
  rintro (h | ⟨i, hi, ⟨e⟩⟩)
  · exact not_lie_char_of_card hb hq hT hm h4 h
  · cases i with
    | lie d =>
      obtain ⟨ld, hvld⟩ := d
      have hn : Nat.card T = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula ld :=
        hb ⟨ld, hvld⟩ T ⟨e⟩
      obtain ⟨rfl, hval⟩ := amb_lie_order_odd hq2 ld hvld hi
      have := h3 rfl
      rw [hT] at hn
      rcases hval with h | h <;> omega
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hc : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hT] at hc
      rcases hi with ⟨rfl, h2 | rfl⟩ | ⟨rfl, h2 | rfl⟩ | ⟨rfl, h2⟩
      · exact hq2 h2
      · exact h5 rfl (by rw [hc]; decide)
      · exact hq2 h2
      · exact (h3 rfl).1 (by rw [hc]; decide)
      · exact hq2 h2
    | _ => exact hi.elim

theorem qtypeOK_of_not_chev {p : ℕ} {T : Type} [Group T]
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ¬ IsChevSimple q T) : QTypeOK p T :=
  fun q hq hq2 hqp hc _ => h q hq hq2 hqp hc

theorem qtypeOK_of_card (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {p : ℕ}
    {T : Type} [Group T] [Finite T] {N : ℕ} (hT : Nat.card T = N) (hN0 : 0 < N)
    (hNlt : N < 2 ^ 200)
    (hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ p → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (h3 : p ≠ 3 → N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (h5 : p ≠ 5 → N ≠ 60) : QTypeOK p T := by
  refine qtypeOK_of_not_chev fun q hq hq2 hqp => ?_
  have h3' : q = 3 → q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 360 ∧
      q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 504 ∧
      q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 25920 := by
    rintro rfl
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact h3 (fun h => hqp h.symm)
  have h5' : q = 5 → q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 60 := by
    rintro rfl
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact h5 (fun h => hqp h.symm)
  refine not_isChevSimple_of_card hb hq hq2 (hT.trans (Nat.ordProj_mul_ordCompl_eq_self N q).symm)
    (Nat.not_dvd_ordCompl hq hN0.ne') ?_ h3' h5'
  set a := N.factorization q
  have hqa : q ^ a ∣ N := Nat.ordProj_dvd N q
  have hpos : 0 < q ^ a := pow_pos hq.pos a
  have hm : q ^ a * (N / q ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N q
  by_cases hqN : q ∣ N
  · have hmem : q ∈ N.primeFactorsList := (Nat.mem_primeFactorsList hN0.ne').2 ⟨hq, hqN⟩
    have ha : a < 200 := by
      by_contra hge
      push Not at hge
      have h1 : 2 ^ 200 ≤ q ^ a :=
        (Nat.pow_le_pow_left hq.two_le 200).trans (Nat.pow_le_pow_right hq.pos hge)
      have h2 : q ^ a ≤ N := Nat.le_of_dvd hN0 hqa
      omega
    have hk := hN q hmem hq2 hqp a ha hqa
    have : q ^ a * q ^ (2 * a) ≤ q ^ a * (N / q ^ a) := by
      rw [hm, ← pow_add]
      calc q ^ (a + 2 * a) = q ^ (3 * a) := by ring_nf
        _ ≤ N := hk
    exact Nat.le_of_mul_le_mul_left this hpos
  · have ha : a = 0 := Nat.factorization_eq_zero_of_not_dvd hqN
    simp only [ha, mul_zero, pow_zero, Nat.div_one]
    exact hN0

theorem qtypeOK_A5 {p : ℕ} (hp : p = 3 ∨ p = 5) {T : Type}
    [Group T] (e : T ≃* ↥(alternatingGroup (Fin 5))) : QTypeOK p T := by
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt e
  refine qtypeOK_of_not_sq_dvd_aut (by rcases hp with rfl | rfl <;> norm_num) ?_
  rw [CFSG.GH74.KGroups.A5.card_mulAut e']
  rcases hp with rfl | rfl <;> norm_num

theorem qtypeOK_three_of_card_360 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (hT : Nat.card T = 360) : QTypeOK 3 T :=
  qtypeOK_of_card hb hT (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

theorem qtypeOK_A6 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type}
    [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) : QTypeOK 3 T := by
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  refine qtypeOK_three_of_card_360 hb ?_
  rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 6
    (by norm_num)]
  decide

section NotSq



theorem qrow_of_not_sq_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : I1416QRow s p := by
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
  exact @qrow_of_model_not_sq_dvd s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)


end NotSq

end CFSG.LocalAnalysis.GLTheoremA.I1416QRows
