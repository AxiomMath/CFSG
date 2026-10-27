module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1415Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

theorem acompOK_of_lines {n p : ℕ} (hp : p.Prime) {P Q : Subgroup (Equiv.Perm (Fin n))}
    (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlines : ∀ H : Subgroup (Equiv.Perm (Fin n)), H ≤ Q → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (line j))
    (hmem : ∀ j, line j ∈ P)
    (hline : ∀ j, ACompOK p (⟨line j, hmem j⟩ : ↥P)) :
    ∀ k : ↥P, orderOf k = p → ACompOK p k := by
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
  have ht : ACompOK p (⟨t, htP⟩ : ↥P) :=
    ACompOK.of_centralizer_eq
      (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers
        (KDSpor.zpowers_subtype_eq hj)).symm (hline j)
  have hk' : MulAut.conj (⟨g, hgP⟩ : ↥P) (⟨t, htP⟩ : ↥P) = k := by
    apply Subtype.ext
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, htdef]
    group
  rw [← hk']
  exact ACompOK.of_mulEquiv hp _ ht

theorem acompOK_of_pgroup_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C A : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAP : A ≤ P) (hAp : IsPGroup p ↥A)
    (hAc : Subgroup.centralizer (A : Set (Equiv.Perm (Fin n))) ⊓ C ≤ A) :
    ACompOK p (⟨x, hxP⟩ : ↥P) := by
  haveI : Finite ↥P := inferInstance
  refine acompOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) hp
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

theorem acompOK_of_derived_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hD : D = ⁅C, C⁆)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hT : ATypeOK p ↥D) : ACompOK p (⟨x, hxP⟩ : ↥P) := by
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

theorem acompOK_conj (hp : p.Prime) (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P)
    {r y : Equiv.Perm (Fin n)} (hr : r ∈ R) (hyP : y ∈ P) (h : ACompOK p (⟨y, hyP⟩ : ↥P)) :
    ACompOK p (⟨r * y * r⁻¹, hR r hr y hyP⟩ : ↥P) :=
  ACompOK.of_mulEquiv hp (KDSpor.conjP hR hr) h

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem arow_of_noComp {name : TauCeti.SporadicName} {p : ℕ} {H : Type} [Group H] [Finite H]
    [IsSimpleGroup H] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : H ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hcard : ¬ (Nat.card H).Prime)
    (_hp : p.Prime) (_hp2 : p ≠ 2)
    (hno : ∀ x : H, orderOf x = p → ∀ I : Subgroup H,
      GLAPComponent p (Subgroup.centralizer ({x} : Set H)) I → False) : I1415Row name p :=
  arow_of_model hOut b (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple hcard)
    fun x hx => acompOK_of_no_comp fun I hI => hno x hx I hI

theorem arow_of_centShape {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (_hp2 : p ≠ 2) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → ATypeOK p T) : I1415Row name p :=
  arow_of_model hOut b hnc fun _ hk => acompOK_of_centShape hp h hG hk

theorem acompOK_five_of_card_dvd_3000 {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 3000) :
    ACompOK 5 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hs
  have hd : Nat.card (PSimple 5 I) ∣ 3000 :=
    ((KDL227Rows.card_pSimple_dvd 5 I).trans (Subgroup.card_dvd_of_le hI.1)).trans hk
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact atypeOK_A5 (Or.inr rfl) fA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
open scoped commutatorElement

theorem arow_McL_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .McL 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  exact arow_of_centShape (Good := fun _ _ => False) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (fun k hk1 hk3 => Or.inl (hsh k hk1 hk3))
    fun _ _ h => h.elim

theorem arow_Ly_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .Ly 5 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ly) = 51765179004000000 :=
    CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.1
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact arow_of_centShape (Good := fun _ _ => False) hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_five (by norm_num)
    (fun k hk1 hk5 => Or.inl (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_Ly_five _
      ⟨MulEquiv.refl _⟩ (orderOf_eq_prime hk5 hk1)))
    fun _ _ h => h.elim

theorem arow_McL_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .McL 5 := by
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
  refine @arow_of_noComp .McL 5 CFSG.Blueprint.NativeSporadic.McL _ inferInstance inferInstance
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

set_option maxRecDepth 20000 in
theorem arow_Th_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1415Row .Th 5 := by
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
  refine @arow_of_model .Th 5 ↥CFSG.Sporadic.Th.J _ hfin hs hOut b hnc
     fun k hk => ?_
  obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_c5 hk
  refine acompOK_five_of_card_dvd_3000 ?_
  have hck := @card_centralizer_conj_eq ↥CFSG.Sporadic.Th.J _ hfin m k
  rw [hck, hm, hcard]

end CFSG.LocalAnalysis.GLTheoremA.I1415Rows
