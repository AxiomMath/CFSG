module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd2520

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416QRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows



theorem qtypeOK_three_of_card_dvd_2520
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 2520) :
    QTypeOK 3 T := by
  intro q hq hq2 hq3 hC hA
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 60 ∨ Nat.card T = 72 ∨ Nat.card T = 168 ∨ Nat.card T = 180 ∨
      Nat.card T = 360 ∨ Nat.card T = 504 := by
    have hlie : ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) →
        Nat.card T = 60 ∨ Nat.card T = 72 ∨ Nat.card T = 168 ∨ Nat.card T = 180 ∨
          Nat.card T = 360 ∨ Nat.card T = 504 := by
      intro d he
      have hn := hb d T he
      have hm := OrderDvd2520.lieOrderFormula_dvd_2520 d.2 (hn ▸ hd)
      simp only [OrderDvd2520.ords, List.mem_cons, List.not_mem_nil, or_false] at hm
      rw [← hn] at hm
      omega
    rcases hC with ⟨i, hi, he⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | lie d => exact hlie d he
      | _ => exact hi.elim
    · cases i with
      | lie d => exact hlie d ⟨e⟩
      | alternating n hn5 =>
        have hcn : Nat.card T = n.factorial / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
        simp only [ambiguousChev] at hi
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, h23⟩ | ⟨rfl, h2⟩
        · left; rw [hcn]; decide
        · exfalso; omega
        · exact absurd h2 hq2
      | _ => exact hi.elim
  have hT : QTypeOK 3 T := by
    rcases hcases with h | h | h | h | h | h
    · obtain ⟨fA⟩ :=
        CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
      exact qtypeOK_A5 (Or.inl rfl) fA
    · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
        Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [h]; norm_num))).elim
    · exact qtypeOK_three_of_card_168 hnab h
    · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
    · exact qtypeOK_three_of_card_360 hb h
    · exact qtypeOK_of_card hb h (by norm_num) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)
  exact hT q hq hq2 hq3 hC hA

theorem qcompOK_three_of_card_dvd_7560
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) : QCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 7560 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact qtypeOK_three_of_card_dvd_2520 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))



theorem qrow_three_of_check_7560 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data) (n' : ℕ) (hn : D.n = n')
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin n')}
    (hA : CFSG.Monster.B.Co2.Rep n' D.A A) (hB : CFSG.Monster.B.Co2.Rep n' D.B B)
    (P : Subgroup (Equiv.Perm (Fin n'))) (hP : P = Subgroup.closure {A, B})
    (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥P) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 7560) : I1416QRow s 3 := by
  subst hn
  subst hP
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine qrow_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine qcompOK_three_of_card_dvd_7560 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem qrow_He_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRow .He 3 := by
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  refine qrow_of_model hOut (e.symm.trans (hbr .He).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [CFSG.Sporadic.HeldB.card_heP]; norm_num))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine qcompOK_three_of_card_dvd_7560 hb hx ?_
  have hcc : Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.HeldB.heP)) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) := by
    rw [← map_centralizer_subtype CFSG.Sporadic.HeldB.heP x,
      Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective]
  rw [hcc]
  rcases he3_card x.2 hx3 with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.GLTheoremA.I1416QRows

