module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Five
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711c2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K14Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.I271 (CentShape CentShapeRk)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp noCardComp_of_mulEquiv)

@[expose] def K14Row (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      (catalogIs (PSimple 3 J) S9.isU5two ∨ catalogIs (PSimple 3 J) S9.isSp6two) → False

@[expose] def CardRow (n : ℕ) (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
        Nat.card (PSimple 3 J) ≠ n

theorem cardRow_of_model {n : ℕ} {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = 3 → NoCardComp n k) : CardRow n s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ
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
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hJ
  have hk : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq, hxo]
  have := noCardComp_of_mulEquiv φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this J hJ

theorem cardRow_of_centShapeRk {n : ℕ} {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    {Good : ∀ (T : Type) [Group T], Prop} {Rk : ∀ (T : Type) [Group T], Prop}
    (hC : CentShapeRk 3 Good Rk Q) (hG : ∀ (T : Type) [Group T], Good T → Nat.card T ≠ n) :
    CardRow n s := by
  refine cardRow_of_model hOut b hnc fun k hk => ?_
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; norm_num at hk
  intro I hI
  rcases (CentShape.of_centShapeRk hC) k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with
    hc | ⟨J, -, huniq, hg⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem noCardComp_of_not_dvd {Q : Type} [Group Q] [Finite Q] {n : ℕ} {k : Q}
    (h : ¬ n ∣ Nat.card (Subgroup.centralizer ({k} : Set Q))) : NoCardComp n k := by
  intro I hI hc
  apply h
  rw [← hc]
  have h2 : Nat.card (PSimple 3 I) ∣ Nat.card (PQuot 3 I) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 I) ∣ Nat.card I := Subgroup.card_quotient_dvd_card _
  exact h2.trans (h3.trans (Subgroup.card_dvd_of_le hI.1))


theorem card_u5two {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isU5two) :
    Nat.card S = 13685760 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedA n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 2 := hi
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨f⟩]
        show orderTwistedA 4 q.card = 13685760
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem card_sp6two {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isSp6two) :
    Nat.card S = 1451520 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 2 := hi
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨f⟩]
        show orderBC 3 q.card = 1451520
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem k14Row_of_card {s : TauCeti.SporadicName} (h1 : CardRow 13685760 s)
    (h2 : CardRow 1451520 s) : K14Row s := by
  intro S _ _ e β hβ hβ1 J hJ hT
  rcases hT with hT | hT
  · exact h1 S e β hβ hβ1 J hJ (card_u5two hT)
  · exact h2 S e β hβ hβ1 J hJ (card_sp6two hT)

section Shape

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c


theorem cardRow_shape (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) (n : ℕ)
    (hn : n = 13685760 ∨ n = 1451520) :
    CardRow n .Fi22 ∧ CardRow n .Th ∧ CardRow n .Fi23 ∧ CardRow n .Fi24Prime ∧ CardRow n .Co1 ∧
      CardRow n .ONan := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
      CFSG.Sporadic.Fi22.card_Fi22
    haveI : Finite (NativeSporadic.Carrier .Fi22) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
    refine cardRow_of_centShapeRk (s := .Fi22) hOut (hbr .Fi22).some
      (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
      fi22CentShapeRk_native ?_
    intro T _ hT hcT
    obtain ⟨e⟩ := hT
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀] at hcT
    rcases hn with rfl | rfl <;> norm_num at hcT
  · have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
      CFSG.RankThree.PartOne.CTP.card_Th
    haveI : Finite (NativeSporadic.Carrier .Th) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    haveI : IsSimpleGroup (NativeSporadic.Carrier .Th) :=
      CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts
    refine cardRow_of_centShapeRk (s := .Th) hOut (hbr .Th).some
      (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
      thCentShapeRk_native ?_
    intro T _ hT hcT
    obtain ⟨e⟩ := hT
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.QTGen4.Recog.G23.ghat_card] at hcT
    rcases hn with rfl | rfl <;> norm_num at hcT
  · have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
      CFSG.Sporadic.Fi23.card_Fi23
    haveI : Finite (NativeSporadic.Carrier .Fi23) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
    refine cardRow_of_centShapeRk (s := .Fi23) hOut (hbr .Fi23).some
      (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
      fi23CentShapeRk_native ?_
    intro T _ hT hcT
    obtain ⟨e⟩ := hT
    rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Dickson.I271.tabFi23_card_om] at hcT
    rcases hn with rfl | rfl <;> norm_num at hcT
  · obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.fi24_model hbr
    have hC := CFSG.HardMathSupport.Dickson.I271.TabFi24.centShapeRk_J_good
      (Good := fun T _ => Nat.card T ≠ n)
      (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
      (fun _ _ _ _ hT => by rw [hT]; rcases hn with rfl | rfl <;> norm_num)
      (fun _ _ _ _ hT => by rw [hT]; rcases hn with rfl | rfl <;> norm_num)
    exact @cardRow_of_centShapeRk n .Fi24Prime _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)
  · obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hbr
    have hC := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_centShapeRk_three_good
      (Good := fun T _ => Nat.card T ≠ n)
      (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
      (fun T _ e hc => by
        have h1 : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans
          CFSG.LieType.Multipliers.U43.card_X₀
        rw [h1] at hc
        rcases hn with rfl | rfl <;> norm_num at hc)
      (by
        show Nat.card ↥(alternatingGroup (Fin 9)) ≠ n
        rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.card_alt_nine]
        rcases hn with rfl | rfl <;> norm_num)
      (fun _ _ hc _ => by
        show _ ≠ n
        rw [hc]
        rcases hn with rfl | rfl <;> norm_num)
      (hbr .Suz)
    exact @cardRow_of_centShapeRk n .Co1 _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)
  · have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
      CFSG.Sporadic.ON.card_ON
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
      Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
      CFSG.Sporadic.ON.isSimpleGroup_ON
    refine cardRow_of_centShapeRk (s := .ONan) hOut (hbr .ONan).some
      (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
      CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk ?_
    intro T _ hT hcT
    obtain ⟨-, ⟨e⟩⟩ := hT
    rw [Nat.card_congr e.toEquiv, I1431Z.card_alt_six_eq] at hcT
    rcases hn with rfl | rfl <;> norm_num at hcT

end Shape

end CFSG.LocalAnalysis.GLTheoremA.K14Spor

end
