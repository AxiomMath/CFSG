module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDL227SporRows
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ONThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLy
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabJ3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.LyFive

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kdSporRow_of_centShape {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (hp2 : p ≠ 2) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hlev : ∀ (T : Type) [Group T], Good T → Nat.card T ∣ Nat.card Q → kLevel p T ≤ 2) :
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
    have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp b.symm hI
    rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv] at hI'
    have hk : orderOf (b.symm x) = p := by rw [MulEquiv.orderOf_eq, hx]
    have hk1 : b.symm x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
    rw [kLevel_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
      (I.equivMapOfInjective b.symm.toMonoidHom b.symm.injective))]
    rcases h (b.symm x) hk1 (by rw [← hk]; exact pow_orderOf_eq_one _) with hcon | ⟨J0, -, huniq, hg⟩
    · exact (false_of_glaPComponent_of_pConstrained hp hcon hI').elim
    · rw [huniq _ hI']
      exact hlev _ hg ((KDL227Rows.card_pSimple_dvd p J0).trans (Subgroup.card_subgroup_dvd_card J0))
  exact ⟨fun h2 => downLe_of_centralizers hncG hout hp hp2 (kLevel_le_two ⟨_, h2, ⟨MulEquiv.refl _⟩⟩)
      hc,
    fun h3 => downLe_of_centralizers hncG hout hp hp2 (kLevel_le_three ⟨_, h3, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).trans (by norm_num)⟩

theorem kLevel_le_one_of_chev {p : ℕ} {T : Type} [Group T] (h : IsChevSimple p T) :
    kLevel p T ≤ 1 := by
  unfold kLevel
  rw [if_pos h]

theorem kLevel_le_one_of_A6 {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.IsA6At 3 T) : kLevel 3 T ≤ 1 := by
  obtain ⟨-, ⟨f⟩⟩ := h
  refine kLevel_le_one_of_chev (Or.inr ⟨TauCeti.CFSGIndex.alternating 6 (by norm_num), ?_,
    ⟨f.trans (MulEquiv.refl _)⟩⟩)
  exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)

theorem kLevel_le_two_of_leafType {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.LeafType 3 T) {N : ℕ} (hd : Nat.card T ∣ N)
    (hN : ¬ 239500800 ∣ N) : kLevel 3 T ≤ 2 := by
  rcases h with ⟨hC, -, -⟩ | ⟨n, hn5, hn6, h3n, ⟨f⟩⟩
  · exact (kLevel_le_one_of_chev hC).trans (by norm_num)
  · have hcT : Nat.card T = n.factorial / 2 := (Nat.card_congr f.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
    have hn12 : n < 12 := by
      by_contra h12
      push Not at h12
      apply hN
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial h12
      have h2 : 2 ∣ Nat.factorial 12 := Nat.dvd_factorial (by norm_num) (by norm_num)
      have : n.factorial / 2 = Nat.factorial 12 / 2 * c := by
        rw [hc, Nat.div_mul_right_comm h2]
      refine Dvd.dvd.trans ⟨c, ?_⟩ (hcT ▸ hd)
      rw [this]
      norm_num [Nat.factorial]
    have hn9 : n = 9 := by
      obtain ⟨m, rfl⟩ := h3n
      omega
    subst hn9
    exact kLevel_le_two ⟨TauCeti.CFSGIndex.alternating 9 (by norm_num),
      Or.inl ⟨rfl, Or.inr rfl⟩, ⟨f.trans (MulEquiv.refl _)⟩⟩

section RowON3


set_option maxRecDepth 100000 in
theorem kdSporRow_ON_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .ONan 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  exact kdSporRow_of_centShape hOut (hbr .ONan).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk)
    fun _ _ h _ => (kLevel_le_one_of_A6 h).trans (by norm_num)

end RowON3

section RowMcL3


theorem kdSporRow_McL_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .McL 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  exact kdSporRow_of_centShape (Good := fun _ _ => False) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (fun k hk1 hk3 => Or.inl (hsh k hk1 hk3))
    fun _ _ h _ => h.elim

end RowMcL3

section RowTh3


theorem kdSporRow_Th_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Th 3 := by
  haveI : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th CFSG.Sporadic.Th.th_kernel_facts
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.OddKernel.card_Th_eq
  exact kdSporRow_of_centShape hOut (hbr .Th).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) CFSG.HardMathSupport.Dickson.I271.leafShape_Th
    fun _ _ h hd => kLevel_le_two_of_leafType h hd (by rw [hc]; norm_num)

end RowTh3

section RowLy3


theorem kdSporRow_Ly_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Ly 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ly) = 51765179004000000 :=
    CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.1
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  refine kdSporRow_of_centShape hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      (CFSG.HardMathSupport.Dickson.I271.tabLy_centShapeRk hOut hbr)) ?_
  intro T _ h hd
  rcases h with h | h | ⟨S, hS, ⟨f⟩⟩
  · exact kLevel_le_two_of_leafType h hd (by rw [hc]; norm_num)
  · exact (kLevel_le_one_of_A6 h).trans (by norm_num)
  · simp only [List.mem_singleton] at hS
    subst hS
    exact kLevel_le_two ⟨TauCeti.CFSGIndex.sporadic .McL,
      (show k2 3 (TauCeti.CFSGIndex.sporadic .McL) from Or.inl rfl), ⟨f⟩⟩

end RowLy3

section RowJ3


theorem kdSporRow_J3_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .J3 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J3) = 50232960 :=
    CFSG.Sporadic.J3.card_J3
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J3) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J3) :=
    CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsh := CFSG.HardMathSupport.Dickson.I271.centShapeSplit_J3
  refine kdSporRow_of_centShape
    (Good := fun T _ => CFSG.HardMathSupport.Dickson.I271.LeafType 3 T ∨
      CFSG.HardMathSupport.Dickson.I271.IsA6At 3 T) hOut (hbr .J3).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) ?_ ?_
  · intro k hk1 hk3
    rcases hsh k hk1 hk3 with h | ⟨J0, hJ0, huniq, hg⟩
    · exact Or.inl h
    · exact Or.inr ⟨J0, hJ0, huniq, hg.imp id fun h => h.1⟩
  · intro T _ h hd
    rcases h with h | h
    · exact kLevel_le_two_of_leafType h hd (by rw [hc]; norm_num)
    · exact (kLevel_le_one_of_A6 h).trans (by norm_num)

end RowJ3

section RowLy5


theorem kdSporRow_Ly_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Ly 5 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ly) = 51765179004000000 :=
    CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.1
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ly) :=
    CFSG.Sporadic.Ly.fam_ly_simplicity.2.2
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact kdSporRow_of_centShape (Good := fun _ _ => False) hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_five (by norm_num)
    (fun k hk1 hk5 => Or.inl (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_Ly_five _
      ⟨MulEquiv.refl _⟩ (orderOf_eq_prime hk5 hk1)))
    fun _ _ h _ => h.elim

end RowLy5

theorem isSolvable_of_card_two_mul {X : Type} [Group X] [Finite X] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (h : Nat.card X = 2 * (p ^ a * q ^ b)) : Group.IsSolvable X := by
  have hodd : Odd (p ^ a * q ^ b) := (hp.odd_of_ne_two hp2).pow.mul (hq.odd_of_ne_two hq2).pow
  have h2 : 2 ∣ (⊥ : Subgroup X).index := by
    rw [Subgroup.index_bot, h]; exact dvd_mul_right 2 _
  have h4 : ¬ 4 ∣ (⊥ : Subgroup X).index := by
    rw [Subgroup.index_bot, h]
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨M, hMn, hMi, -⟩ :=
    CFSG.GorensteinWalter.exists_normal_index_two_containing_of_index_eq_two_mul_odd
      (Subgroup.normal_bot) h2 h4
  have hMc : Nat.card M = p ^ a * q ^ b := by
    have := M.card_mul_index
    rw [hMi, h] at this
    omega
  haveI : Group.IsSolvable M := isSolvable_of_card_eq hp hq hpq hMc
  haveI : Group.IsSolvable (X ⧸ M) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nat.card (X ⧸ M) = 2 := by rw [← Subgroup.index_eq_card, hMi]
    haveI : IsCyclic (X ⧸ M) := isCyclic_of_prime_card hc
    letI := IsCyclic.commGroup (α := X ⧸ M)
    exact isSolvable_of_comm (fun a b => mul_comm a b)
  exact solvable_of_ker_le_range M.subtype (QuotientGroup.mk' M)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

section RowMcL5


theorem kdSporRow_McL_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .McL 5 := by
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
  refine @kdSporRow_of_model .McL 5 CFSG.Blueprint.NativeSporadic.McL _ inferInstance inferInstance
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

end RowMcL5

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
