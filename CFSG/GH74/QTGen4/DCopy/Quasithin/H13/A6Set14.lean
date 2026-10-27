module

public import CFSG.Quasithin.H13.A6Set14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Producers
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S14

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem set14_of_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (S : Setting4 G T L V) (hV2 : IsV2 T V S.V2) {Lp : Subgroup G} (P : PlusData S Lp)
    (hb : ∃ g ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G), g ^ 3 = 1 ∧
      g ∉ Subgroup.normalizer (fsuV1 T V : Set G) ∧
      Subgroup.centralizer ((S.V3 ⊔ S.V3.map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G) ≤ Subgroup.normalizer (L : Set G))
    (hdef : (IsHatA6 L → Lp = l1plus T L V) ∧ (¬ IsHatA6 L → Lp = L₁Of L (fsuV1 T V))) :
    U3.Set14 G T L V S.V2 S.V3 Lp where
  h13 := S.h13
  irr := S.irr
  zv := S.zv
  v2 := hV2
  card1 := S.card_V1
  le23 := S.V2_le_V3
  le3V := S.V3_le_V
  T_V3 := S.T_le_normalizer_V3
  card3 := S.card_V3
  Lp_eq := P.eq
  Lp_L := P.le_L
  Lp_V1 := P.le_NV1
  T_Lp := P.T_le
  gen := P.gen
  irred := P.irred
  comm3 := P.comm3
  index2 := P.index2_eq
  Lp_def := hdef
  Lp3 := P.Lp3
  cv3 := cv3 S
  clv := S.centralizer_le_o2Z
  bcase := Or.inr hb
  genL := genL S
  fsu := S.fsu
  T_L := S.T_le_NL
  V_T := S.V_le_T
  T_V := S.frame.T_le
  Mmax := S.uniqueM.1.1
  uniq := fun M hM hLT => S.uniqueM.2 M ⟨hM, hLT⟩
  ti := (stmt12_2_6_of_F4 h1222 h323 G T L V (hyp1223 S)).2

end S14

theorem set14ProducerA6_of_F4 (h1332 : Stmt13_3_2_F4)
    (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) : U3.Set14ProducerA6_F4 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hnat
  obtain ⟨S⟩ := U3.setting4_of_case_b_F4 h1332 hH hV hZV hnat
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  by_cases hhat : IsHatA6 L
  · have hP1 := S.hatL1Plus hhat
    have hP2 := S.hatL2Plus hhat
    obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_hat S hP2
    have hxL2 : x ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G) := by
      have hT2 : T ⊓ L ≤ Subgroup.normalizer (L₁Of L S.V2 : Set G) :=
        inf_le_left.trans (A5.le_normalizer_oTwoRes_of_le_normalizer
          (F7.le_normalizer_inf S.T_le_NL (S.T_le_normalizer_V2.trans Subgroup.le_normalizer)))
      have hc : ⁅L₁Of L S.V2, T ⊓ L⁆ ≤ L₁Of L S.V2 := by
        rw [Subgroup.commutator_le]
        intro h hh k hk
        have e : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (L₁Of L S.V2).mul_mem hh
          ((Subgroup.mem_normalizer_iff.mp (hT2 hk) h⁻¹).mp ((L₁Of L S.V2).inv_mem hh))
      exact oTwoRes_le _ (hc (oTwoRes_le _ hx))
    exact ⟨S.V3, l1plus T L V, S14.set14_of_F4 h1222 h323 S hV2 (S14.plusData_l1plus S hP1)
      (S14.bcase_of S hxL2 hx3 hxN hρx) ⟨fun _ => rfl, fun h => absurd hhat h⟩⟩
  · obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_nonhat S hhat
    exact ⟨S.V3, S.L1, S14.set14_of_F4 h1222 h323 S hV2 (S14.plusData_L1 S hhat)
      (S14.bcase_of S (oTwoRes_le _ hx) hx3 hxN hρx) ⟨fun h => absurd h hhat, fun _ => rfl⟩⟩

end CFSG.Quasithin.H13.A6
