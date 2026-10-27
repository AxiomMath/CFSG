module

public import CFSG.Quasithin.H13.A6S1372L76X
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76W

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique.Bridge
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

theorem lem1376L1K_of_F4
    (hS : Lem1376L1KSmall_F4) (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) : Lem1376L1K_F4 := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hHyp
  have hX : ∀ {X : Type} [Group X] [Finite X], ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) →
      A318Exclusion X → S.L1 ≤ K := fun E hE => S.L1_le_of_quotEquiv hF h36 h38 hH hK E hE
  have hR : ∀ {D : FFModel}, D.Faithful →
      ∀ {U Z : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))},
      D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) U Z →
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* D.Gam) :=
    fun {_} hD {_ _} hRe => S.exists_quotEquiv_of_realizes_F4 hNS h13315 h1356two hH hK hD hRe
  have hr2 : ∀ {X : Type} [Group X] [Finite X], ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 :=
    fun E => Setting4.pRank_le_two_of_quotEquiv hH.1.2 hK E S.h13.qtke
  have hsmall := hS G T L V S hNS hNU H hH hab K hK
  rcases hHyp with ⟨n, hn, hSL⟩ | hX5 | ⟨n, hA⟩ | hX4 | ⟨α, hA7⟩ | ⟨n, hSL3⟩ | ⟨n, hSp⟩ |
    ⟨n, hG2⟩
  ·
    obtain ⟨F, _, _, hF2, hRe⟩ := id hSL
    have hF2' : Nat.card F = 2 := by simpa using hF2
    obtain ⟨E⟩ := hR (FFModel.nat_faithful _) hRe
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | h6
    · exact hsmall (Or.inl ⟨1, hSL⟩)
    · exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
        (A6L76X.isPSL_of_statedSL (by norm_num) hF2' E))
    · exact hX (MulEquiv.refl _)
        (a318Exclusion_psl52 (A6L76X.isPSL_of_statedSL (by norm_num) hF2' E))
    · have h1 := hr2 (X := ↥(StatedSL n F)) E
      have h2 := A6L76X.three_le_pRank_statedSL h6 hF2'
      omega
  ·
    obtain ⟨E⟩ := hR (FFC.extSq_faithful (d := 5) (by norm_num)) hX5
    exact hX (MulEquiv.refl _) (a318Exclusion_psl52 (R3c2.isPSL_two_of_statedSL (by norm_num) E))
  ·
    rcases (show n ≤ 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with
      hn | rfl | rfl | rfl | rfl | h9
    · exfalso
      obtain ⟨π, hπ⟩ := hA
      obtain ⟨e₀⟩ := S.exists_quotEquiv_tilde_F4 hNS h13315 h1356two hH hK
      have := Setting4.nontrivial_of_quotEquiv hK e₀
      have hcard : Nat.card (Fin n) ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        exact hn
      have : Group.IsSolvable (FFModel.altDn n).Gam := alternatingGroup.isSolvable hcard
      have hsolv : Group.IsSolvable ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := Group.isSolvable_of_surjective hπ.1
      have := S.isPerfect_tilde hH hK
      exact Group.IsPerfect.not_isSolvable _ hsolv
    · exact hsmall (Or.inr hA)
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (X := ↥(alternatingGroup (Fin 6))) E a318Exclusion_alt6
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (X := ↥(alternatingGroup (Fin 7))) E a318Exclusion_alt7
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by norm_num)) hA
      exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
        (R3c2.isPSL_two_of_statedSL (by norm_num) (E.trans A6L76X.alt8Equiv)))
    · obtain ⟨E⟩ := hR (FFC.altDn_faithful (by omega)) hA
      have h1 := hr2 (X := ↥(alternatingGroup (Fin n))) E
      have h2 := A6L76E.three_le_pRank_alt h9
      omega
  ·
    obtain ⟨E⟩ := hR (FFC.extSq_faithful (d := 4) (by norm_num)) hX4
    exact hX (MulEquiv.refl _) (a318Exclusion_psl42 A6L76X.l34NotL42
      (R3c2.isPSL_two_of_statedSL (by norm_num) E))
  ·
    obtain ⟨E⟩ := hR (FFC.a7Four_faithful α) hA7
    exact hX (X := ↥(alternatingGroup (Fin 7))) E a318Exclusion_alt7
  ·
    exact hsmall (Or.inl ⟨n, hSL3⟩)
  ·
    obtain ⟨F, _, _, hFn, hRe⟩ := id hSp
    obtain ⟨E⟩ := hR (FFModel.nat_faithful _) hRe
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hFn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · exact (A6L76X.not_isPerfect_statedSp_two (by simpa using hFn)
        (Setting4.isPerfect_of_quotEquiv hK E)).elim
    · have h4 : 4 ≤ Nat.card F := by
        rw [hFn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hq := CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num) (Or.inl (Or.inr h4)))
      exact hX (MulEquiv.refl _) (R3c2.exclusion_sp4 factA318Excl_holds hFn E hq)
  ·
    obtain ⟨F, _, _, hFn, hRe⟩ := id hG2
    have : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hFn
    obtain ⟨E⟩ := hR (FFC.zornQ_faithful _ le_rfl) hRe
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hFn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · exact (A6L76X.not_isPerfect_g2_two (by simpa using hFn)
        (Setting4.isPerfect_of_quotEquiv hK E)).elim
    · have : IsSimpleGroup (FFModel.zornQ (CFSG.Open.quasithinG2 F)).Gam :=
        A6L76X.isSimpleGroup_g2 hn2 hFn
      have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := E.isSimpleGroup
      have hq := isQuasisimple_of_perfect_of_isSimple1521d
        (Setting4.isPerfect_of_quotEquiv hK (MulEquiv.refl _)) this
      exact hX (MulEquiv.refl _) (R3c2.exclusion_g2 factA318Excl_holds hFn E hq)

end CFSG.Quasithin.H13.A6
