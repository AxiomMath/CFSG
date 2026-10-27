module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSevenType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
import CFSG.HardMathSupport.Dickson.BMRows.TypesLie80640

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

theorem card_mulAut_of_equiv_alt {T : Type} [Group T] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : T ≃* alternatingGroup (Fin n)) : Nat.card (MulAut T) = n.factorial := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6),
    Nat.card_perm, Nat.card_fin]

theorem isSimpleGroup_of_catalog_A1 {T : Type} [Group T] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : 4 ≤ q.card)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : IsSimpleGroup T := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  exact (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)).isSimpleGroup_congr.2
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := GaloisField q.p q.exponent)
      (by rw [hF]; exact hq))

theorem card_mulAut_of_catalog_A2_four {T : Type} [Group T] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 4)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : Nat.card (MulAut T) = 241920 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq]
  let f : T ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField q.p q.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 _)).symm
  rw [Nat.card_congr (MulAut.congr f).toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hF

theorem not_sq_seven_dvd_card_mulAut_of_chev_dvd_80640
    (hb : LieOrderBridge) {T : Type} [Group T] {r : ℕ} (hC : IsChevSimple r T)
    (hd : Nat.card T ∣ 80640) : ¬ 7 ^ 2 ∣ Nat.card (MulAut T) := by
  have : Finite T := Nat.finite_of_card_ne_zero fun h0 => by rw [h0] at hd; norm_num at hd
  have hlie : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ¬ 7 ^ 2 ∣ Nat.card (MulAut T) := by
    rintro ⟨d, hv⟩ ⟨e⟩
    have hn := hb ⟨d, hv⟩ T ⟨e⟩
    obtain ⟨q, ⟨rfl, hq | hq⟩ | ⟨rfl, hq⟩⟩ := Lie80640.lieOrderFormula_dvd_80640 hv (hn ▸ hd)
    · haveI := isSimpleGroup_of_catalog_A1 q hv (by omega) e
      have h168 : Nat.card T = 168 := by
        rw [hn]
        show orderA 1 q.card = 168
        rw [hq]
        decide +kernel
      exact I1416Rows.not_sq_seven_dvd_card_mulAut_of_card_168 h168
    · obtain ⟨e'⟩ := I1416Rows.nonempty_equiv_L28_of_catalog_A1 q hv hq e
      rw [I1416Rows.card_mulAut_of_equiv_L28 e']
      norm_num
    · rw [card_mulAut_of_catalog_A2_four q hv hq e]
      norm_num
  rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d => exact hlie d ⟨e⟩
    | _ => exact hi.elim
  · cases i with
    | lie d => exact hlie d ⟨e⟩
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [card_mulAut_of_equiv_alt le_rfl (by norm_num) e]
        decide
      · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 (K := T) ⟨e⟩
        rw [CFSG.GH74.KGroups.A6.card_mulAut e']
        norm_num
      · rw [card_mulAut_of_equiv_alt (by norm_num) (by norm_num) e]
        decide
    | _ => exact hi.elim

theorem typeOK_B7
    (hb : LieOrderBridge) :
    ∀ (T : Type) [Group T], Nat.card T ∣ 80640 → I1416Rows.TypeOK 7 T :=
  fun _ _ hd hC h49 _ => absurd h49 (not_sq_seven_dvd_card_mulAut_of_chev_dvd_80640 hb hC hd)

theorem qtypeOK_B7
    (hb : LieOrderBridge) :
    ∀ (T : Type) [Group T], Nat.card T ∣ 80640 → I1416QRows.QTypeOK 7 T := by
  intro T _ hd _ _ _ _ hC hA
  have : Finite T := Nat.finite_of_card_ne_zero fun h0 => by rw [h0] at hd; norm_num at hd
  exact not_sq_seven_dvd_card_mulAut_of_chev_dvd_80640 hb hC hd
    (I1416QRows.sq_dvd_card_mulAut_of_elemAb (by norm_num) hA)

theorem atypeOK_B7 {p : ℕ} :
    ∀ (T : Type) [Group T], Nat.card T ∣ 80640 → I1415Rows.ATypeOK p T :=
  fun _ _ hd => I1415Rows.atypeOK_of_card_lt
    (lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hd) (by norm_num))

end CFSG.HardMathSupport.Dickson.BMRows
