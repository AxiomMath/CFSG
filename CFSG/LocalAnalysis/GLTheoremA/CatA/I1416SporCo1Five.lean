module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd604800
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Census
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveC

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA CFSG.Open
  CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

section Generic

variable {Good : ∀ (T : Type) [Group T], Prop}
  (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')

include hGood in
theorem shapeRkAt_J2_of_data_good
    (hJ2 : ∀ (T : Type) [Group T], T ≃* NativeSporadic.J2 → Good T) {G : Type} [Group G]
    (P : Subgroup G) [Finite P] (x : ↥P) (k u v : G) (hxk : (x : G) = k) (hu : u ∈ P) (hv : v ∈ P)
    (hk5 : k ^ 5 = 1) (hk1 : k ≠ 1) (hku : k * u = u * k) (hkv : k * v = v * k) (hu1 : u ≠ 1)
    (h1 : u * v * u * v⁻¹ * u⁻¹ * v⁻¹ = 1)
    (h2 : u * v * v * u * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ = 1)
    (h3 : (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) * (u * u * u * u * u * u * u) = 1)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G) ⊓ P) ≤ 3024000) :
    ShapeRkAt 5 Good (fun _ _ => True) x := by
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = Subgroup.closure ({u, v} : Set G) := ⟨_, rfl⟩
  obtain ⟨eL⟩ := nonempty_mulEquiv_J2_of_relators u v L hL h1 h2
    (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) rfl h3 hu1
  obtain ⟨hs, hcard, hnab⟩ := J2_facts_of_equiv eL
  have hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
    rw [hL]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      have hc := Subgroup.mem_centralizer_singleton_iff.2
        (show u * (x : G) = (x : G) * u by rw [hxk]; exact hku.symm)
      exact Subgroup.mem_inf.2 ⟨hc, hu⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hc := Subgroup.mem_centralizer_singleton_iff.2
        (show v * (x : G) = (x : G) * v by rw [hxk]; exact hkv.symm)
      exact Subgroup.mem_inf.2 ⟨hc, hv⟩
  refine shapeRkAt_of_bound (by norm_num) hGood (fun _ _ _ _ _ h => h) P x L hLC hs hnab
    (by rw [hcard]; norm_num) (by rw [hxk]; exact hk1) (by rw [hxk]; exact hk5) ?_ (hJ2 _ eL)
    trivial
  rw [hxk, hcard]
  exact hbound

@[expose] def CompGood (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → Good (PSimple p I)

include hGood in
theorem CompGood.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q']
    [Finite Q'] (σ : Q ≃* Q') {k : Q} (h : CompGood (Good := Good) p k) :
    CompGood (Good := Good) p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact hGood _ _ (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm (h _ hI')

theorem compGood_of_multiShapeAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Rk : ∀ (T : Type) [Group T], Prop} {k : Q} (h : MultiShapeAt p Good Rk k) :
    CompGood (Good := Good) p k := by
  intro I hI
  rcases h with hc | ⟨-, -, -, hall⟩
  · exact (CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_pConstrained hp hc
      hI).elim
  · exact (hall I hI).1


include hGood in
theorem five_good (hJ2 : ∀ (T : Type) [Group T], T ≃* NativeSporadic.J2 → Good T)
    (hA5 : Good ↥(alternatingGroup (Fin 5))) (x : ↥GA) (hx : orderOf x = 5) :
    CompGood (Good := Good) 5 x := by
  haveI : Finite ↥GA := finite_GA
  have hG : GOK := Certificates.certificate13670
  have hshape : ∀ y : ↥GA, (MRep repD0 (y : GL24) ∨ MRep repD1 (y : GL24) ∨ MRep repZ (y : GL24)) →
      CompGood (Good := Good) 5 y := by
    rintro y (h0 | h1 | h5)
    · obtain ⟨hrep, hk5, hk1, hku, hkv, hu1, hw1, hw2, hw3, hbound⟩ := fiveA_data
      obtain ⟨h1', h2', h3'⟩ := relators_of_wordG hw1 hw2 hw3
      exact compGood_of_multiShapeAt (by norm_num) (multiShapeAt_of_shapeRkAt (by norm_num)
        (shapeRkAt_J2_of_data_good hGood hJ2 GA y _ _ _ (h0.eq hrep) (kG_mem ext 89)
          (kG_mem ext 90) hk5 hk1 hku hkv hu1 h1' h2' h3' hbound))
    · obtain ⟨k, x₁, y₁, τ, hk, -, hx₁, hy₁, hτ, hk5, hk1, hkx, hky, hkt, htt, hc1, hc2, hc3, hc4,
        hL, hX, hY, hE, hCbd, hpt⟩ := fiveB_data
      exact compGood_of_multiShapeAt (Rk := fun _ _ => True) (by norm_num)
        (multiShapeAt_A5A5_of_data hGood (fun _ _ _ _ _ h => h) hA5 trivial GA y k x₁ y₁ τ
          (h1.eq hk) hk5 hk1 hx₁ hy₁ hτ hkx hky hkt htt hc1 hc2 hc3 hc4 hL hX hY hE hCbd hpt)
    · intro I hI
      exact (CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_pConstrained
        (by norm_num) (tabCo1_fiveC y h5) hI).elim
  obtain ⟨c, hc⟩ := tabCo1_census hG x hx
  have h := CompGood.of_mulEquiv hGood (by norm_num) (MulAut.conj c⁻¹) (hshape _ hc)
  rw [MulAut.conj_apply, show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h
  exact h

end Generic


theorem co1_model_five (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite ↥GA ∧ IsSimpleGroup ↥GA ∧ (∃ a c : ↥GA, a * c ≠ c * a) ∧
      Nonempty (↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) := by
  have hfin : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Co1 ≃* ↥GA := co1MatEquiv
  have hs : IsSimpleGroup ↥GA :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e.symm
  have hpr : ¬ (Nat.card ↥GA).Prime := by rw [card_GA_eq]; norm_num
  exact ⟨hfin, hs,
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥GA _ hfin hs hpr,
    ⟨e.symm.trans (hbr .Co1).some⟩⟩

theorem not_isChevSimple_J2 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] (e : T ≃* NativeSporadic.J2) (q : ℕ) : ¬ IsChevSimple q T := by
  obtain ⟨-, hc, -⟩ := J2_facts_of_equiv e
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_not_lieOrder hb hc
    (fun d hd => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.OrderDvd604800.lieOrderFormula_ne_604800 hd)
    (by decide) (by decide) (by decide) q

theorem row_Co1_five (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.I1416SporRow .Co1 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_of_model .Co1 5 ↥GA _ hfin hs hOut b hnc
    fun x hx => ?_
  exact five_good (Good := fun T _ => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.TypeOK 5 T)
    (fun _ _ _ _ e h => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.TypeOK.of_mulEquiv e h)
    (fun _ _ e => CFSG.LocalAnalysis.GLTheoremA.I1416Rows.typeOK_of_not_chev
      (not_isChevSimple_J2 hb e 2))
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.typeOK_A5 (Or.inr rfl) (MulEquiv.refl _)) x hx

theorem qrow_Co1_five (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Co1 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_model .Co1 5 ↥GA _ hfin hs hOut b hnc
    fun x hx => ?_
  exact five_good (Good := fun T _ => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeOK 5 T)
    (fun _ _ _ _ e h => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeOK.of_mulEquiv e h)
    (fun _ _ e => CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_of_not_chev
      fun q _ _ _ => not_isChevSimple_J2 hb e q)
    (CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_A5 (Or.inr rfl) (MulEquiv.refl _)) x hx

end CFSG.HardMathSupport.Dickson.I271.TabCo1
