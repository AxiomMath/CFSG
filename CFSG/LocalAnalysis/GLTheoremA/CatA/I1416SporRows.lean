module

public import CFSG.GH74.KGroups.A5
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporTh5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416SporS
public import CFSG.Milestones.CAT_native_realization
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDL227
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHN

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows



open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def TypeOK (p : ℕ) (T : Type) [Group T] : Prop :=
  IsChevSimple 2 T → p ^ 2 ∣ Nat.card (MulAut T) →
    ¬ (p = 3 ∧ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd T) →
    p = 3 ∧ catalogIs T (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i)

theorem TypeOK.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : TypeOK p T) : TypeOK p T' := by
  intro hc ha hl
  have h' := h (CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm hc)
    (by rwa [Nat.card_congr (MulAut.congr e).toEquiv])
    (fun ⟨h3, n, hn, h1, ⟨f⟩⟩ => hl ⟨h3, n, hn, h1, ⟨e.symm.trans f⟩⟩)
  exact ⟨h'.1, (KDSpor.catalogIs_congr e).1 h'.2⟩

@[expose] def CompOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    TypeOK p (PSimple p I)

theorem CompOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : CompOK p k) : CompOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact (h _ hI').of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm

theorem CompOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : CompOK p k) : CompOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem compOK_of_no_comp {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    CompOK p k := fun I hI => (h I hI).elim

@[expose] def I1416SporRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ K : Subgroup S,
      GLAPComponent p (fixSubgroup β) K → TypeOK p (PSimple p K)

theorem i1416TwoSporS_iff : I1416TwoSporS ↔ ∀ s p, I1416SporRow s p := by
  constructor
  · intro h s p S _ _ he hp hp2 β hβ hβ1 K hK hc ha hl
    obtain ⟨h3, h'⟩ := h S s he p hp hp2 β hβ hβ1 K hK hc ha hl
    subst h3
    exact ⟨rfl, h'⟩
  · intro h S _ _ s he p hp hp2 β hβ hβ1 K hK hc ha hl
    obtain ⟨h3, h'⟩ := h s p S he hp hp2 β hβ hβ1 K hK hc ha hl
    subst h3
    exact ⟨rfl, h'⟩

theorem row_of_model {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = p → CompOK p k) : I1416SporRow s p := by
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
  have := CompOK.of_mulEquiv hp φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this K hK

theorem row_of_model_not_sq_dvd {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hd : ¬ p ^ 2 ∣ Nat.card Q) : I1416SporRow s p :=
  row_of_model hOut b hnc fun k hk => compOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hk hd hI




open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem two_part_bound {a m v M : ℕ} (hm : Odd m) (h4 : 4 ^ a ≤ m)
    (h : 2 ^ a * m = 2 ^ v * M) : 2 ^ (2 * v) ≤ M := by
  have hva : v ≤ a := by
    by_contra hva
    push Not at hva
    have h1 : 2 ^ (a + 1) ∣ 2 ^ a * m :=
      h ▸ (Nat.pow_dvd_pow 2 hva).mul_right M
    rw [pow_succ] at h1
    have h2 : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)
  have hM : M = 2 ^ (a - v) * m := by
    have h2 : 2 ^ a = 2 ^ v * 2 ^ (a - v) := by rw [← pow_add]; congr 1; omega
    rw [h2, mul_assoc] at h
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
  rw [hM]
  calc 2 ^ (2 * v) = 4 ^ v := by rw [pow_mul]; norm_num
    _ ≤ 4 ^ a := Nat.pow_le_pow_right (by norm_num) hva
    _ ≤ m := h4
    _ ≤ 2 ^ (a - v) * m := Nat.le_mul_of_pos_left _ (by positivity)

theorem not_isChevSimple_two_of_card
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T] [Finite T]
    {a m : ℕ} (hT : Nat.card T = 2 ^ a * m) (hm : Odd m) (h4 : 4 ^ a ≤ m)
    (hamb : 2 ^ a * m ≠ 60 ∧ 2 ^ a * m ≠ 168 ∧ 2 ^ a * m ≠ 360 ∧ 2 ^ a * m ≠ 504 ∧
      2 ^ a * m ≠ 6048 ∧ 2 ^ a * m ≠ 20160 ∧ 2 ^ a * m ≠ 25920) :
    ¬ IsChevSimple 2 T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = 2 := hi
      have hn : Nat.card T = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 :=
        hb d T ⟨e⟩
      obtain ⟨v, M, hv, hM⟩ := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part d.1 d.2
      rw [hd] at hv hM
      have := two_part_bound hm h4 (hT.symm.trans (hn.trans hv))
      omega
    | _ => exact hi.elim
  · cases i with
    | lie d =>
      obtain ⟨ld, hvld⟩ := d
      have hn : Nat.card T = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula ld :=
        hb ⟨ld, hvld⟩ T ⟨e⟩
      have hval := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.amb_lie_order 2 ld hvld hi
      rw [hT] at hn
      rcases hval with h | h | h | h <;> omega
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hc : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hT] at hc
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial] at hc <;> omega
    | _ => exact hi.elim




open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem typeOK_of_not_chev {p : ℕ} {T : Type} [Group T] (h : ¬ IsChevSimple 2 T) : TypeOK p T :=
  fun hc => (h hc).elim

theorem typeOK_A6 {T : Type} [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) : TypeOK 3 T :=
  fun _ _ _ => ⟨rfl, TauCeti.CFSGIndex.alternating 6 (by norm_num), Or.inl rfl,
    ⟨e.trans (MulEquiv.refl _)⟩⟩

theorem typeOK_A5 {p : ℕ} (hp : p = 3 ∨ p = 5) {T : Type} [Group T]
    (e : T ≃* ↥(alternatingGroup (Fin 5))) : TypeOK p T := by
  intro _ ha _
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt e
  rw [CFSG.GH74.KGroups.A5.card_mulAut e'] at ha
  rcases hp with rfl | rfl <;> norm_num at ha

theorem compOK_of_pConstrained {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p
      (Subgroup.centralizer ({k} : Set Q))) : CompOK p k :=
  compOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_pConstrained hp h hI

theorem compOK_of_solvable {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({k} : Set Q))) : CompOK p k :=
  compOK_of_no_comp fun I hI => KDSpor.false_of_glaPComponent_of_solvable hp h hI

theorem compOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → TypeOK p T) : CompOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg




open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem compOK_of_centShape {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → TypeOK p T) {k : Q} (hk : orderOf k = p) :
    CompOK p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem row_three_of_perm {name : TauCeti.SporadicName} {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hs : IsSimpleGroup ↥P)
    (hcard : ¬ (Nat.card ↥P).Prime)
    (hsmall : ∀ x ∈ P, orderOf x = 3 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) < 60) :
    I1416SporRow name 3 := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 hs
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hcG : Nat.card G = Nat.card ↥P := (Nat.card_congr b.toEquiv).symm
  have hnc : ∃ a c : G, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcG]; exact hcard)
  refine row_of_model hOut (MulEquiv.refl _) hnc fun x hx => compOK_of_solvable Nat.prime_three
    (CFSG.GroupTheory.groups_order_below_sixty_solvable ?_)
  rw [KDSpor.card_centralizer_of_model b x]
  refine hsmall _ (b.symm x).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_M11_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1416SporRow .M11 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact row_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m11S3Data rep_m11A rep_m11B Certificates.certificate13511.1
      (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_M12_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1416SporRow .M12 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact row_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m12S3Data rep_m12A rep_m12B Certificates.certificate13511.2.1
      (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_M22_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1416SporRow .M22 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact row_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m22S3Data rep_m22A rep_m22B Certificates.certificate13511.2.2.1
      (by decide) x hx h3




open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

theorem compOK_of_lines {n p : ℕ} (hp : p.Prime) {P Q : Subgroup (Equiv.Perm (Fin n))}
    (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlines : ∀ H : Subgroup (Equiv.Perm (Fin n)), H ≤ Q → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (line j))
    (hmem : ∀ j, line j ∈ P)
    (hline : ∀ j, CompOK p (⟨line j, hmem j⟩ : ↥P)) :
    ∀ k : ↥P, orderOf k = p → CompOK p k := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro k hk
  have hko : orderOf (k : Equiv.Perm (Fin n)) = p := by rw [Subgroup.orderOf_coe]; exact hk
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ k.2 hko
  set t := g⁻¹ * (k : Equiv.Perm (Fin n)) * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin n) ≃* Equiv.Perm (Fin n)).orderOf_eq k
    simpa [MulAut.conj_apply, htdef, hko] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have htP : t ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hgP) k.2) hgP
  have ht : CompOK p (⟨t, htP⟩ : ↥P) :=
    CompOK.of_centralizer_eq
      (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers
        (KDSpor.zpowers_subtype_eq hj)).symm (hline j)
  have hk' : MulAut.conj (⟨g, hgP⟩ : ↥P) (⟨t, htP⟩ : ↥P) = k := by
    apply Subtype.ext
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, htdef]
    group
  rw [← hk']
  exact CompOK.of_mulEquiv hp _ ht


theorem compOK_of_pgroup_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C A : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAP : A ≤ P) (hAp : IsPGroup p ↥A)
    (hAc : Subgroup.centralizer (A : Set (Equiv.Perm (Fin n))) ⊓ C ≤ A) :
    CompOK p (⟨x, hxP⟩ : ↥P) := by
  haveI : Finite ↥P := inferInstance
  refine compOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) hp
    (Or.inl ?_) fun _ _ h => h.elim
  refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective P.subtype
    P.subtype_injective ?_
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
  have hCP : Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P ≤ C := by
    rw [hC]
    exact inf_le_inf_left _ hPR
  refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup
    (fun a ha => ⟨(hC ▸ hAC ha : a ∈ _ ⊓ R).1, hAP ha⟩) ⟨fun a ha g => ?_⟩ hAp
    ((inf_le_inf_left _ hCP).trans hAc)
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have := hAn.conj_mem ⟨a, hAC ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, hCP g.2⟩
  exact Subgroup.mem_subgroupOf.1 this


theorem compOK_of_derived_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hD : D = ⁅C, C⁆)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hT : TypeOK p ↥D) : CompOK p (⟨x, hxP⟩ : ↥P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k : ↥P := ⟨x, hxP⟩ with hk
  set Cq : Subgroup ↥P := Subgroup.centralizer ({k} : Set ↥P) with hCq
  set L : Subgroup ↥P := D.subgroupOf P with hL
  let eL : ↥L ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDP
  haveI hLs : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eL).2 hDs
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    refine ⟨eL.symm ⟨g, hg⟩, eL.symm ⟨h, hh⟩, fun he => hgh ?_⟩
    have := congrArg (fun z => ((eL z : ↥D) : Equiv.Perm (Fin n))) he
    simpa using this
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.HardMathSupport.Dickson.I271.isQuasisimpleOpen_of_simple_nonab hLnab
  have hDC : D ≤ C := by
    rw [hD, Subgroup.commutator_le]
    intro a ha c hc
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hc) (C.inv_mem ha)) (C.inv_mem hc)
  have hxcent : x ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) := by
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [← hDcent] at this
    exact this.1
  have hgC : ∀ g : ↥P, g ∈ Cq → (g : Equiv.Perm (Fin n)) ∈ C := by
    intro g hg
    rw [hC]
    refine Subgroup.mem_inf.2 ⟨?_, hPR g.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact congrArg Subtype.val hg
  have hLC : L ≤ Cq := by
    intro l hl
    rw [hCq, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hxcent _ (Subgroup.mem_subgroupOf.1 hl))
  have hLn : ∀ g ∈ Cq, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    rw [hL, Subgroup.mem_subgroupOf] at hl ⊢
    have h2 : ⁅(g : Equiv.Perm (Fin n)), (l : Equiv.Perm (Fin n))⁆ ∈ D := by
      rw [hD]
      exact Subgroup.commutator_mem_commutator (hgC g hg) (hDC hl)
    have h3 : ((g * l * g⁻¹ : ↥P) : Equiv.Perm (Fin n)) =
        ⁅(g : Equiv.Perm (Fin n)), (l : Equiv.Perm (Fin n))⁆ * l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [h3]
    exact D.mul_mem h2 hl
  have hcoreQ : GLAPPrimeCore p ↥Cq = ⊥ := by
    let e1 : ↥Cq ≃* ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) :=
      (Cq.equivMapOfInjective P.subtype P.subtype_injective).trans
        (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' P k))
    have h0 := (CFSG.HardMathSupport.Dickson.I271.glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore p _).1
      hcore
    rw [← glaPPrimeCore_map_iso p e1.symm, h0, Subgroup.map_bot]
  have hcent : IsPGroup p ↥(Cq ⊓ Subgroup.centralizer (L : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcD : ((c : ↥P) : Equiv.Perm (Fin n)) ∈
        Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_, hgC _ c.2.1⟩
      have h := Subgroup.mem_centralizer_iff.1 c.2.2 ⟨d, hDP hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val h
    rw [hDcent] at hcD
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcD
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo,
      pow_orderOf_eq_one, one_zpow]
  have hcoreL : GLAPPrimeCore p ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥L) with h | h
    · exact h
    · exfalso
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore hp ↥L
      rw [h, Subgroup.card_top, Nat.card_congr eL.toEquiv] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpD
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hLnab
  intro I hI
  have hIL : I = L :=
    CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple hp hLC hLn hLq
      hcoreQ hcent hI
  rw [hIL]
  exact (hT.of_mulEquiv eL.symm).of_mulEquiv
    (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf L hcoreL hZL).symm


theorem compOK_conj (hp : p.Prime) (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P)
    {r y : Equiv.Perm (Fin n)} (hr : r ∈ R) (hyP : y ∈ P) (h : CompOK p (⟨y, hyP⟩ : ↥P)) :
    CompOK p (⟨r * y * r⁻¹, hR r hr y hyP⟩ : ↥P) :=
  CompOK.of_mulEquiv hp (KDSpor.conjP hR hr) h








open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem row_of_noComp {name : TauCeti.SporadicName} {p : ℕ} {H : Type} [Group H] [Finite H]
    [IsSimpleGroup H] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : H ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hcard : ¬ (Nat.card H).Prime)
    (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hno : ∀ x : H, orderOf x = p → ∀ I : Subgroup H,
      GLAPComponent p (Subgroup.centralizer ({x} : Set H)) I → False) : I1416SporRow name p :=
  row_of_model hOut b (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple hcard)
    fun x hx => compOK_of_no_comp fun I hI => hno x hx I hI

theorem row_of_centShape {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (_hp2 : p ≠ 2) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → TypeOK p T) : I1416SporRow name p :=
  row_of_model hOut b hnc fun _ hk => compOK_of_centShape hp h hG hk

theorem compOK_five_of_card_dvd_3000 {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 3000) :
    CompOK 5 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hs
  have hd : Nat.card (PSimple 5 I) ∣ 3000 :=
    ((KDL227Rows.card_pSimple_dvd 5 I).trans (Subgroup.card_dvd_of_le hI.1)).trans hk
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact typeOK_A5 (Or.inr rfl) fA




open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
open scoped commutatorElement


set_option maxRecDepth 100000 in
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.HardMathSupport.Timmesfeld.Tables.Census in
theorem row_J4_eleven
    (hbr : SporadicBridges)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1416SporRow .J4 11 := by
  haveI hJs : IsSimpleGroup ↥J := isSimpleGroup_J j4Facts
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group :=
    (seedEquiv j4Facts.mat).symm.trans (hbr .J4).some
  have h2 : 2 ∣ Nat.card ↥J := by
    rw [card_J_eq]
    exact Dvd.intro (2 ^ 20 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) (by ring)
  have hcard : ¬ (Nat.card ↥J).Prime := by
    intro hpr
    rcases hpr.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [card_J_eq] at h
      norm_num at h
  refine @row_of_noComp .J4 11 ↥J _ inferInstance hJs hOut b hcard (by norm_num) (by norm_num)
    fun x hx I hI => ?_
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_eleven_pow_four_dvd_card_J hx
  refine no_comp_of_conj (by norm_num) h x (fun I hI => ?_) I hI
  set u := h⁻¹ * x * h with hu
  have huo : orderOf u = 11 := by
    have := orderOf_conj_eq' h⁻¹ x
    rw [inv_inv] at this
    rw [hu, this, hx]
  by_cases hz : u ∈ Subgroup.zpowers qz
  · have hzp : Subgroup.zpowers u = Subgroup.zpowers qz :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_qz])
    rw [centralizer_singleton_eq_of_zpowers hzp] at hI
    refine false_of_glaPComponent_of_pConstrained (by norm_num) ?_ hI
    have hQC : Q11 ≤ Subgroup.centralizer ({qz} : Set ↥J) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem hq)
    refine ⟨Q11, hQC, fun g hg q hq => ?_, IsPGroup.of_card card_Q11,
      inf_le_right.trans centralizer_Q11_le⟩
    exact (Subgroup.mem_normalizer_iff.1 (centralizer_qz_le_normalizer_J4 hg) q).1 hq
  · obtain ⟨h121, h242⟩ := card_centralizer_noncentral_le hh hz
    refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
    obtain ⟨k, hk⟩ := h121
    have hk2 : k = 1 ∨ k = 2 := by
      have : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk; exact absurd hk Nat.card_pos.ne'
        · exact h0
      omega
    haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({u} : Set ↥J))
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 11) (q := 2) (a := 2) (b := k - 1) (by norm_num) (by norm_num) (by norm_num) ?_
    rw [Fintype.card_eq_nat_card, hk]
    rcases hk2 with rfl | rfl <;> norm_num


set_option maxRecDepth 100000 in
theorem row_ON_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1416SporRow .ONan 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  haveI hs : IsSimpleGroup ↥CFSG.ONSchreier.Pv :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ON.isSimpleGroup_ON CFSG.ONSchreier.onEquivPv.symm
  have hc : Nat.card ↥CFSG.ONSchreier.Pv = 460815505920 := CFSG.ONSchreier.card_Pv
  refine @row_of_noComp .ONan 7 ↥CFSG.ONSchreier.Pv _ inferInstance hs hOut
    (CFSG.ONSchreier.onEquivPv.symm.trans b)
    (not_prime_of_two_dvd (by rw [hc]; norm_num) (by rw [hc]; norm_num)) (by norm_num)
    (by norm_num) fun x hx I hI => ?_
  refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
  rcases CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.card_centralizer_seven_Pv
    hx with h | h
  · exact isSolvable_of_card_eq (p := 2) (q := 7) (a := 2) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_eq (p := 7) (q := 2) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)


set_option maxRecDepth 100000 in
theorem row_ON_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .ONan 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  exact row_of_centShape hOut (hbr .ONan).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk)
    fun _ _ h => typeOK_A6 h.2.some


theorem row_McL_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .McL 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  exact row_of_centShape (Good := fun _ _ => False) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (fun k hk1 hk3 => Or.inl (hsh k hk1 hk3))
    fun _ _ h => h.elim


theorem row_Ly_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .Ly 5 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ly) = 51765179004000000 :=
    CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.1
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact row_of_centShape (Good := fun _ _ => False) hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_five (by norm_num)
    (fun k hk1 hk5 => Or.inl (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_Ly_five _
      ⟨MulEquiv.refl _⟩ (orderOf_eq_prime hk5 hk1)))
    fun _ _ h => h.elim


theorem row_McL_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .McL 5 := by
  have hc : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  haveI : Finite CFSG.Blueprint.NativeSporadic.McL :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL := CFSG.Sporadic.McL.isSimpleGroup_McL
  have b : CFSG.Blueprint.NativeSporadic.McL ≃* (TauCeti.CFSGIndex.sporadic .McL).Group :=
    (hbr .McL).some
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_five_of_certificate
  have hcard : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.McL).Prime := by
    rw [hc]; norm_num
  refine @row_of_noComp .McL 5 CFSG.Blueprint.NativeSporadic.McL _ inferInstance inferInstance
    hOut b hcard Nat.prime_five (by norm_num) fun x hx I hI => ?_
  refine false_of_glaPComponent_of_solvable Nat.prime_five ?_ hI
  rcases hall x hx with h | h
  · have : Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 750 := by
      rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₁]
    exact isSolvable_of_card_two_mul (p := 3) (q := 5) (a := 1) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [this]; norm_num)
  · have : Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 25 := by
      rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₂]
    exact isSolvable_of_card_eq (p := 5) (q := 2) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by rw [this]; norm_num)


open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier in
theorem row_Ru_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .Ru 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, ⟨hrec0, hrec1⟩, ⟨hC0, hC0c⟩,
    ⟨hC1, hC1c⟩, ⟨hAC, hAn, -, hAcard, -, -, hAc⟩,
    ⟨hDs, ⟨g1, hg1, h1, hh1, hgh⟩, hDcard, hDP, hDcent, -⟩⟩ :=
    R3E_Ru_full_five_centralizer_structures
  have hc : Nat.card ↥ruP = 145926144000 := card_ruP'
  have hfin : Finite ↥ruP := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  have hs : IsSimpleGroup ↥ruP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e.symm
  have hpr : ¬ (Nat.card ↥ruP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥ruP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥ruP _ hfin hs hpr
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group := e.symm.trans (hbr .Ru).some
  have hlines := CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlinesSet
  have hmemQ : ∀ j, ruFiveLine j ∈ ruFiveQ := by
    intro j
    have h : Subgroup.zpowers (ruFiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h.1 (Subgroup.mem_zpowers _)
  have hmem : ∀ j, ruFiveLine j ∈ ruP := fun j => hQP (hmemQ j)
  have hL0 : CompOK 5 (⟨ruFiveLine 0, hmem 0⟩ : ↥ruP) := by
    refine compOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) Nat.prime_five
      (Or.inl ?_) fun _ _ h => h.elim
    refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective ruP.subtype
      ruP.subtype_injective ?_
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
    show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 5
      (Subgroup.centralizer {ruFiveLine 0} ⊓ ruP)
    rw [← hC0]
    exact CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup hAC hAn
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : CompOK 5 (⟨ruFiveLine 1, hmem 1⟩ : ↥ruP) := by
    have hDC : ruFiveD1 ≤ ruFiveC1 := by
      show ⁅ruFiveC1, ruFiveC1⁆ ≤ ruFiveC1
      rw [Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact ruFiveC1.mul_mem (ruFiveC1.mul_mem (ruFiveC1.mul_mem ha hc) (ruFiveC1.inv_mem ha))
        (ruFiveC1.inv_mem hc)
    have hDfin : Finite ↥ruFiveD1 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    obtain ⟨fA⟩ := @CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty ↥ruFiveD1 _ hDfin hDs
      hDcard
    refine compOK_of_shapeRkAt (Good := fun T _ => TypeOK 5 T) (Rk := fun _ _ => True)
      Nat.prime_five ?_ fun _ _ h => h
    refine CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_subgroup_data (P := ruP)
      (L := ruFiveD1) Nat.prime_five
      (fun T T' _ _ e h => TypeOK.of_mulEquiv e h)
      (fun _ _ _ _ _ h => h) ⟨ruFiveLine 1, hmem 1⟩ (hC1 ▸ hDC) ?_ hDs
      ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩, fun h => hgh (congrArg Subtype.val h)⟩ (by rw [hDcard]; norm_num)
      (k := 1) ?_ ?_ trivial
    · intro g hg l hl
      rw [← hC1] at hg
      have h2 : ⁅g, l⁆ ∈ ruFiveD1 := Subgroup.commutator_mem_commutator hg (hDC hl)
      have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
        rw [commutatorElement_def]; group
      rw [h3]
      exact ruFiveD1.mul_mem h2 hl
    · show Nat.card ↥(Subgroup.centralizer {ruFiveLine 1} ⊓ ruP) = Nat.card ↥ruFiveD1 * 5 ^ 1
      rw [← hC1, hC1c, hDcard]; norm_num
    · exact typeOK_A5 (Or.inr rfl) fA
  have hline : ∀ j, CompOK 5 (⟨ruFiveLine j, hmem j⟩ : ↥ruP) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : CompOK 5 (⟨ruFiveLine (ruFiveRecordOf j), hmem _⟩ : ↥ruP) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · have : ruFiveRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : ruFiveRecordOf j = 1 := Fin.ext h
        rw [this]; exact hL1
    have hk' : MulAut.conj (⟨ruFiveTransporter j, hjP⟩ : ↥ruP)
        (⟨ruFiveLine (ruFiveRecordOf j), hmem _⟩ : ↥ruP) = ⟨ruFiveLine j, hmem j⟩ := by
      apply Subtype.ext
      simp [MulAut.conj_apply, hjconj]
    rw [← hk']
    exact @CompOK.of_mulEquiv 5 Nat.prime_five ↥ruP ↥ruP _ _ hfin _ _ hr
  exact @row_of_model .Ru 5 ↥ruP _ hfin hs hOut b hnc
    (@compOK_of_lines 4060 5 Nat.prime_five ruP ruFiveQ hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) _
      ruFiveLine hlines hmem hline)


open CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem row_HS_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .HS 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, -, ⟨hC0, -⟩, ⟨hC2, -⟩,
    ⟨hC23, -⟩, ⟨hA0C, hA0n, hA0P, hA0card, -, -, hA0c⟩, ⟨hA23C, hA23n, hA23P, hA23card, -, -, hA23c⟩,
    ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩⟩ := R3E_HS_full_five_centralizer_structures
  have hM := hs_autModel
  have hc : Nat.card ↥hs100P = 44352000 := card_hs100P
  have hfin : Finite ↥hs100P := inferInstance
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥hs100P := hs100Equiv
  have hs : IsSimpleGroup ↥hs100P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e.symm
  have hpr : ¬ (Nat.card ↥hs100P).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥hs100P, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥hs100P _ hfin hs hpr
  have b : ↥hs100P ≃* (TauCeti.CFSGIndex.sporadic .HS).Group := e.symm.trans (hbr .HS).some
  have hlines := CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (hs100FiveLine j) ≤ hs100FiveQ ∧
      Nat.card (Subgroup.zpowers (hs100FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (hs100FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, hs100FiveLine j ∈ hs100P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (hs100FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : CompOK 5 (⟨hs100FiveLine 0, hmem 0⟩ : ↥hs100P) :=
    compOK_of_pgroup_record Nat.prime_five hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 2) (by rw [hA0card]; norm_num)) hA0c
  have hL23 : CompOK 5 (⟨hs100FiveLine 23, hmem 23⟩ : ↥hs100P) :=
    compOK_of_pgroup_record Nat.prime_five hM.le (hmem 23) hC23 hA23C hA23n hA23P
      (IsPGroup.of_card (n := 3) (by rw [hA23card]; norm_num)) hA23c
  have hL2 : CompOK 5 (⟨hs100FiveLine 2, hmem 2⟩ : ↥hs100P) := by
    have hDfin : Finite ↥hs100FiveD2 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    refine compOK_of_derived_record (C := hs100FiveC2) (D := hs100FiveD2) Nat.prime_five hM.le
      (hmem 2) hC2 rfl hDs hDnab hDP hDcent
      (hord 2) ?_ (by rw [hDcard]; norm_num) (typeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
    exact CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_eq_bot_of_ambient
      Nat.prime_five hM.le hM.conj_mem
      (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_hs100FiveRecord_eq_bot 2
        (Or.inr (Or.inl rfl)))
  have hline : ∀ j, CompOK 5 (⟨hs100FiveLine j, hmem j⟩ : ↥hs100P) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : CompOK 5 (⟨hs100FiveLine (hs100FiveRecordOf j), hmem _⟩ : ↥hs100P) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : hs100FiveRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : hs100FiveRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
      · have : hs100FiveRecordOf j = 23 := Fin.ext h
        rw [this]; exact hL23
    have h := compOK_conj Nat.prime_five hM.conj_mem hjR (hmem _) hr
    have heq : (⟨hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥hs100P) =
        ⟨hs100FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @row_of_model .HS 5 ↥hs100P _ hfin hs hOut b hnc
    (@compOK_of_lines 100 5 Nat.prime_five hs100P hs100FiveQ hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) _
      hs100FiveLine hlines hmem hline)


set_option maxRecDepth 20000 in
theorem row_Th_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .Th 5 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Th.J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hnc : ∃ a c : ↥CFSG.Sporadic.Th.J, a * c ≠ c * a := by
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts
    have hcC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
      CFSG.RankThree.OddKernel.card_Th_eq
    obtain ⟨a, c, hac⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (S := CFSG.Blueprint.NativeSporadic.Carrier .Th) (by rw [hcC]; norm_num)
    refine ⟨e a, e c, fun h => hac ?_⟩
    exact e.injective ((e.map_mul a c).trans (h.trans (e.map_mul c a).symm))
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (hbr .Th).some
  have hcard := CFSG.HardMathSupport.Dickson.Sec6.I1431.card_centralizer_c5
  refine @row_of_model .Th 5 ↥CFSG.Sporadic.Th.J _ hfin hs hOut b hnc
     fun k hk => ?_
  obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_c5 hk
  refine compOK_five_of_card_dvd_3000 ?_
  have hck := @card_centralizer_conj_eq ↥CFSG.Sporadic.Th.J _ hfin m k
  rw [hck, hm, hcard]






open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA


theorem row_of_not_sq_dvd
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s) : I1416SporRow s p := by
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
  exact @row_of_model_not_sq_dvd s p _ _ hfin hsimp hOut b
    (@CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple _ _ hfin hsimp
      (by rw [hc]; exact hnp)) hp (by rw [hc]; exact hd)


end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
