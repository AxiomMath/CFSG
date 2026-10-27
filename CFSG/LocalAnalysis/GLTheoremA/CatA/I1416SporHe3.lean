module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder280
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder504
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder120
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem isL2TwoPowOdd_of_catalog_A1 {T : Type} [Group T] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq8 : q.card = 8)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd T := by
  obtain ⟨p, k, hp, hk⟩ := q
  have hc : p ^ k = 8 := by
    have := TauCeti.PrimePower.card_def ⟨p, k, hp, hk⟩
    rw [hq8] at this
    exact this.symm
  have hp2 : p = 2 := by
    have hd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hc]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  subst hp2
  have hk3 : k = 3 := by
    have : (2 : ℕ) ^ k = 2 ^ 3 := by rw [hc]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hk3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨3, by decide, by norm_num,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, 3, hp, hk⟩ hv)⟩⟩

theorem typeOK_three_of_card_dvd_2520
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 2520) :
    TypeOK 3 T := by
  intro hC h9 hl
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  by_cases hc60 : Nat.card T = 60
  · exfalso
    obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hc60
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
    rw [CFSG.GH74.KGroups.A5.card_mulAut e'] at h9
    norm_num at h9
  by_cases hc168 : Nat.card T = 168
  · exact absurd h9 (not_sq_three_dvd_card_mulAut_of_card_168 hnab hc168)
  have hle : Nat.card T ≤ 2520 := Nat.le_of_dvd (by norm_num) hd
  have h504 : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) →
      CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 = 504 → False := by
    intro d ⟨e⟩ h
    obtain ⟨q, hdq, hq8⟩ := Order504.lieOrderFormula_eq_504 d.2 h
    obtain ⟨d, hv⟩ := d
    simp only at hdq
    subst hdq
    exact hl ⟨rfl, isL2TwoPowOdd_of_catalog_A1 q hv hq8 e⟩
  rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hd2 : d.1.characteristic = 2 := hi
      have hn := hb d T ⟨e⟩
      obtain ⟨v, M, hv, hM⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part d.1 d.2
      rw [hd2] at hv hM
      rw [← hn] at hv
      have hv3 : v ≤ 3 := by
        have h2v : 2 ^ v ∣ 2520 := (Dvd.intro M hv.symm).trans hd
        by_contra hv4
        have : 2 ^ 4 ∣ 2520 := (pow_dvd_pow 2 (by omega)).trans h2v
        norm_num at this
      interval_cases v
      · omega
      · omega
      · omega
      ·
        have hv' : Nat.card T = 8 * M := by rw [hv]; norm_num
        have hM' : M < 64 := by simpa using hM
        have hM315 : M ∣ 315 := by
          have : 8 * M ∣ 8 * 315 := by rw [← hv']; exact hd.trans (by norm_num)
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
        interval_cases M
        all_goals (try (norm_num at hM315; done))
        all_goals first
          | omega
          | (have hc : Nat.card T = 72 := by omega
             exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
              Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [hc]; norm_num))).elim)
          | (have hc : Nat.card T = 120 := by omega
             exact (Order120.lieOrderFormula_ne_120 d.2 (hn.symm.trans hc)).elim)
          | (have hc : Nat.card T = 280 := by omega
             exact (Order280.lieOrderFormula_ne_280 d.2 (hn.symm.trans hc)).elim)
          | (have hc : Nat.card T = 360 := by omega
             exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2
              (hn.symm.trans hc)).elim)
          | (have hc : Nat.card T = 504 := by omega
             exact (h504 d ⟨e⟩ (hn.symm.trans hc)).elim)
    | _ => exact hi.elim
  · cases i with
    | lie d =>
      exfalso
      have hn := hb d T ⟨e⟩
      have hval := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.amb_lie_order 2 d.1 d.2 hi
      rcases hval with h' | h' | h' | h'
      · exact hc168 (hn.trans h')
      · exact h504 d ⟨e⟩ h'
      · omega
      · omega
    | alternating n hn5 =>
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      have hi' := hi
      simp only [ambiguousChev] at hi'
      rcases hi' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd (by rw [hcn]; decide) hc60
      · exact ⟨rfl, TauCeti.CFSGIndex.alternating 6 hn5, Or.inl rfl, ⟨e⟩⟩
      · exfalso
        rw [hcn] at hle
        norm_num [Nat.factorial] at hle
    | _ => exact hi.elim

theorem compOK_three_of_card_dvd_7560
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) : CompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 7560 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact typeOK_three_of_card_dvd_2520 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem row_three_of_check_7560 {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data) (n' : ℕ) (hn : D.n = n')
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin n')}
    (hA : CFSG.Monster.B.Co2.Rep n' D.A A) (hB : CFSG.Monster.B.Co2.Rep n' D.B B)
    (P : Subgroup (Equiv.Perm (Fin n'))) (hP : P = Subgroup.closure {A, B})
    (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : IsSimpleGroup ↥P) (hpr : ¬ D.ord.Prime)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 7560) : I1416SporRow s 3 := by
  subst hn
  subst hP
  obtain ⟨hcardP, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine row_of_model hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcardP]; exact hpr))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine compOK_three_of_card_dvd_7560 hb hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem row_He_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .He 3 := by
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  refine row_of_model hOut (e.symm.trans (hbr .He).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [CFSG.Sporadic.HeldB.card_heP]; norm_num))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine compOK_three_of_card_dvd_7560 hb hx ?_
  have hcc : Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.HeldB.heP)) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) := by
    rw [← map_centralizer_subtype CFSG.Sporadic.HeldB.heP x,
      Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective]
  rw [hcc]
  rcases he3_card x.2 hx3 with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
