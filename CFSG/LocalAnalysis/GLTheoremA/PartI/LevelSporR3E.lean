module

public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Multi
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveHSMcL
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def LevelOK (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    kLevel p (PSimple p I) ≤ 2

theorem LevelOK.of_mulEquiv {p : ℕ} (hp : p.Prime) {Q Q' : Type} [Group Q] [Group Q'] [Finite Q']
    (σ : Q ≃* Q') {k : Q} (h : LevelOK p k) : LevelOK p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  rw [kLevel_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective))]
  exact h _ hI'

theorem LevelOK.of_centralizer_eq {p : ℕ} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : LevelOK p k) : LevelOK p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem levelOK_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → kLevel p T ≤ 2) : LevelOK p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (false_of_glaPComponent_of_pConstrained hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem kdSporRow_of_levelOK {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hp2 : p ≠ 2) (h : ∀ k : Q, orderOf k = p → LevelOK p k) :
    KDSporRow name p := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 inferInstance
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hncG : ∃ a c : G, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨b a, b c, fun h' => hac ?_⟩
    have := congrArg b.symm h'
    simpa using this
  have hout := hOut G inferInstance hncG name ⟨MulEquiv.refl _⟩
  have hc : ∀ x : G, orderOf x = p → ∀ I : Subgroup G,
      GLAPComponent p (Subgroup.centralizer ({x} : Set G)) I → kLevel p (PSimple p I) ≤ 2 := by
    intro x hx I hI
    have hk : orderOf (b.symm x) = p := by rw [MulEquiv.orderOf_eq, hx]
    have := LevelOK.of_mulEquiv hp b (h _ hk)
    rw [MulEquiv.apply_symm_apply] at this
    exact this I hI
  exact ⟨fun h2 => downLe_of_centralizers hncG hout hp hp2 (kLevel_le_two ⟨_, h2, ⟨MulEquiv.refl _⟩⟩)
      hc,
    fun h3 => downLe_of_centralizers hncG hout hp hp2 (kLevel_le_three ⟨_, h3, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).trans (by norm_num)⟩

theorem zpowers_subtype_eq {G : Type*} [Group G] {P : Subgroup G} {a b : ↥P}
    (h : Subgroup.zpowers (a : G) = Subgroup.zpowers (b : G)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply Subgroup.map_injective P.subtype_injective
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact h

theorem levelOK_of_lines {n p : ℕ} (hp : p.Prime) {P Q : Subgroup (Equiv.Perm (Fin n))}
    (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlines : ∀ H : Subgroup (Equiv.Perm (Fin n)), H ≤ Q → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (line j))
    (hmem : ∀ j, line j ∈ P)
    (hline : ∀ j, LevelOK p (⟨line j, hmem j⟩ : ↥P)) :
    ∀ k : ↥P, orderOf k = p → LevelOK p k := by
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
  have ht : LevelOK p (⟨t, htP⟩ : ↥P) :=
    LevelOK.of_centralizer_eq
      (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers
        (zpowers_subtype_eq hj)).symm (hline j)
  have hk' : MulAut.conj (⟨g, hgP⟩ : ↥P) (⟨t, htP⟩ : ↥P) = k := by
    apply Subtype.ext
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, htdef]
    group
  rw [← hk']
  exact LevelOK.of_mulEquiv hp _ ht

section RowRu5

open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier


theorem kdSporRow_Ru_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Ru 5 := by
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
  have hL0 : LevelOK 5 (⟨ruFiveLine 0, hmem 0⟩ : ↥ruP) := by
    refine levelOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) Nat.prime_five
      (Or.inl ?_) fun _ _ h => h.elim
    refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective ruP.subtype
      ruP.subtype_injective ?_
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
    show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 5
      (Subgroup.centralizer {ruFiveLine 0} ⊓ ruP)
    rw [← hC0]
    exact CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup hAC hAn
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : LevelOK 5 (⟨ruFiveLine 1, hmem 1⟩ : ↥ruP) := by
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
    refine levelOK_of_shapeRkAt (Good := fun T _ => kLevel 5 T ≤ 2) (Rk := fun _ _ => True)
      Nat.prime_five ?_ fun _ _ h => h
    refine CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_subgroup_data (P := ruP)
      (L := ruFiveD1) Nat.prime_five
      (fun T T' _ _ e h => by show kLevel 5 T' ≤ 2; rw [← kLevel_congr e]; exact h)
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
    · refine (kLevel_le_one_of_chev (Or.inr ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num),
        Or.inl ⟨rfl, Or.inr rfl⟩, ⟨fA.trans (MulEquiv.refl _)⟩⟩)).trans (by norm_num)
  have hline : ∀ j, LevelOK 5 (⟨ruFiveLine j, hmem j⟩ : ↥ruP) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : LevelOK 5 (⟨ruFiveLine (ruFiveRecordOf j), hmem _⟩ : ↥ruP) := by
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
    exact @LevelOK.of_mulEquiv 5 Nat.prime_five ↥ruP ↥ruP _ _ hfin _ _ hr
  exact @kdSporRow_of_levelOK .Ru 5 ↥ruP _ hfin hs hOut b hnc Nat.prime_five (by norm_num)
    (@levelOK_of_lines 4060 5 Nat.prime_five ruP ruFiveQ hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) _
      ruFiveLine hlines hmem hline)

end RowRu5

open scoped commutatorElement



variable {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

@[expose] def conjP (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {r : Equiv.Perm (Fin n)}
    (hr : r ∈ R) : ↥P ≃* ↥P where
  toFun q := ⟨r * q * r⁻¹, hR r hr q q.2⟩
  invFun q := ⟨r⁻¹ * q * r, by
    have := hR r⁻¹ (R.inv_mem hr) q q.2
    rwa [inv_inv] at this⟩
  left_inv q := Subtype.ext (by simp only; group)
  right_inv q := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem levelOK_of_pgroup_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C A : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAP : A ≤ P) (hAp : IsPGroup p ↥A)
    (hAc : Subgroup.centralizer (A : Set (Equiv.Perm (Fin n))) ⊓ C ≤ A) :
    LevelOK p (⟨x, hxP⟩ : ↥P) := by
  haveI : Finite ↥P := inferInstance
  refine levelOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) hp
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

theorem levelOK_of_derived_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hD : D = ⁅C, C⁆)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hlev : kLevel p ↥D ≤ 2) : LevelOK p (⟨x, hxP⟩ : ↥P) := by
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
  rw [hIL, kLevel_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf L hcoreL hZL),
    kLevel_congr eL]
  exact hlev

theorem levelOK_conj (hp : p.Prime) (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P)
    {r y : Equiv.Perm (Fin n)} (hr : r ∈ R) (hyP : y ∈ P) (h : LevelOK p (⟨y, hyP⟩ : ↥P)) :
    LevelOK p (⟨r * y * r⁻¹, hR r hr y hyP⟩ : ↥P) :=
  LevelOK.of_mulEquiv hp (conjP hR hr) h




theorem kLevel_five_le_of_card_sixty {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (h : Nat.card T = 60) : kLevel 5 T ≤ 2 := by
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
  exact (kLevel_le_one_of_chev (Or.inr ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num),
    Or.inl ⟨rfl, Or.inr rfl⟩, ⟨fA.trans (MulEquiv.refl _)⟩⟩)).trans (by norm_num)

section RowHS5

open CFSG.RankThree.Native CFSG.RankThree.PartOne


theorem kdSporRow_HS_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .HS 5 := by
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
  have hL0 : LevelOK 5 (⟨hs100FiveLine 0, hmem 0⟩ : ↥hs100P) :=
    levelOK_of_pgroup_record Nat.prime_five hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 2) (by rw [hA0card]; norm_num)) hA0c
  have hL23 : LevelOK 5 (⟨hs100FiveLine 23, hmem 23⟩ : ↥hs100P) :=
    levelOK_of_pgroup_record Nat.prime_five hM.le (hmem 23) hC23 hA23C hA23n hA23P
      (IsPGroup.of_card (n := 3) (by rw [hA23card]; norm_num)) hA23c
  have hL2 : LevelOK 5 (⟨hs100FiveLine 2, hmem 2⟩ : ↥hs100P) := by
    have hDfin : Finite ↥hs100FiveD2 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    refine levelOK_of_derived_record (C := hs100FiveC2) (D := hs100FiveD2) Nat.prime_five hM.le
      (hmem 2) hC2 rfl hDs hDnab hDP hDcent
      (hord 2) ?_ (by rw [hDcard]; norm_num) (@kLevel_five_le_of_card_sixty _ _ hDfin hDs hDcard)
    exact CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_eq_bot_of_ambient
      Nat.prime_five hM.le hM.conj_mem
      (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_hs100FiveRecord_eq_bot 2
        (Or.inr (Or.inl rfl)))
  have hline : ∀ j, LevelOK 5 (⟨hs100FiveLine j, hmem j⟩ : ↥hs100P) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : LevelOK 5 (⟨hs100FiveLine (hs100FiveRecordOf j), hmem _⟩ : ↥hs100P) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : hs100FiveRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : hs100FiveRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
      · have : hs100FiveRecordOf j = 23 := Fin.ext h
        rw [this]; exact hL23
    have h := levelOK_conj Nat.prime_five hM.conj_mem hjR (hmem _) hr
    have heq : (⟨hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥hs100P) =
        ⟨hs100FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @kdSporRow_of_levelOK .HS 5 ↥hs100P _ hfin hs hOut b hnc Nat.prime_five (by norm_num)
    (@levelOK_of_lines 100 5 Nat.prime_five hs100P hs100FiveQ hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) _
      hs100FiveLine hlines hmem hline)

end RowHS5

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
