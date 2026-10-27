module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompList
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273c2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (SporTables.SporTypes)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables

private theorem typeInv_not_isList93 :
    TypeInv (fun T _ => ¬ catalogIs T (S9.isList93 3)) := by
  intro T T' _ _ e h h'
  exact h (typeInv_catalogIs (S9.isList93 3) _ _ e.symm h')

private theorem sporTypes_of_carrier_centTypes {name : TauCeti.SporadicName}
    {Good : ∀ (T : Type) [Group T], Prop} (hBr : SporadicBridges)
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier name)]
    (h : CentTypes 3 Good (CFSG.Blueprint.NativeSporadic.Carrier name))
    (hgood : ∀ (T : Type) [Group T] [Finite T], Good T → ¬ catalogIs T (S9.isList93 3)) :
    SporTypes 3 (fun T _ => ¬ catalogIs T (S9.isList93 3)) name := by
  intro T _ _ ⟨f⟩ s hs I hI
  have hfs : orderOf ((f.trans (hBr name).some.symm) s) = 3 := by
    rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨hI', ⟨g⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.comp_transport Nat.prime_three
      (f.trans (hBr name).some.symm) hI
  exact typeInv_not_isList93 _ _ g.symm (hgood _ (h _ hfs _ hI'))

section ListCertificates

theorem not_isList93_of_leafType (hb : LieOrderBridge) (hA : Chev2OddAmb) {T : Type} [Group T]
    [Finite T] (h : CFSG.HardMathSupport.Dickson.I271.LeafType 3 T) :
    ¬ catalogIs T (S9.isList93 3) := by
  rintro hlist
  rcases h with ⟨hChev, -, -⟩ | ⟨n, hn, hn6, h3n, ⟨e⟩⟩
  · exact not_isChevSimple_of_isList93 hb hA Nat.prime_three (by norm_num) hlist hChev
  · exact not_isList93_of_alt hb (p := 3) hn (by rintro rfl; norm_num at h3n) e hlist

end ListCertificates

section RowCertificates

theorem sporTypes_notList93_three
    (hb : LieOrderBridge) (hA : Chev2OddAmb)
    (hN2 : ∀ (S : Type) [Group S] (j : TauCeti.CFSGIndex), List93.NotChev2Idx j →
      Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : SporadicBridges) (hOrd : SporadicOrdersTable)
    (name : TauCeti.SporadicName) (hname : k2Spor 3 name)
    (hK : CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier name)) :
    SporTables.SporTypes 3 (fun T _ => ¬ catalogIs T (S9.isList93 3)) name := by
  cases name with
  | M11 =>
    intro T _ _ ⟨eT⟩ s hs I hI hcat
    have hcatM11 : catalogIs T (fun i => i = .sporadic .M11) :=
      ⟨.sporadic .M11, rfl, ⟨eT⟩⟩
    have hcardT : Nat.card T = 7920 := by
      rw [card_of_catalogIs_sporadic hOrd hcatM11]
      rfl
    have hdvd : Nat.card (PSimple 3 I) ∣ Nat.card T :=
      (KDL227Rows.card_pSimple_dvd 3 I).trans (by
        have h := Subgroup.card_dvd_of_le (le_top : I ≤ ⊤)
        rwa [Subgroup.card_top] at h)
    haveI : Finite (PSimple 3 I) := inferInstance
    have hle : Nat.card (PSimple 3 I) ≤ 7920 := by
      rw [← hcardT]
      exact Nat.le_of_dvd Nat.card_pos hdvd
    exact absurd (card_ge_of_isList93 hb hcat) (by omega)
  | J3 =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .J3 (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (GLTheoremB.MovingAround.Inputs273c.centTypes_of_centShapeSplit Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.centShapeSplit_J3)
      (fun T _ _ h => h.elim (fun hL => not_isList93_of_leafType hb hA hL)
        (fun hA6 => by
          obtain ⟨-, ⟨e6⟩⟩ := hA6
          exact not_isList93_of_alt hb (n := 6) (by norm_num) (by norm_num) e6))
  | McL =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .McL (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (GLTheoremB.MovingAround.Inputs273c.centTypes_of_constrained Nat.prime_three fun k hk =>
        CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL k
          (fun h1 => by rw [h1, orderOf_one] at hk; norm_num at hk)
          (by rw [← hk]; exact pow_orderOf_eq_one k))
      (fun T _ _ h => h.elim)
  | Suz =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Suz (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (GLTheoremB.MovingAround.Inputs273c.centTypes_of_centShapeSplit Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.centShapeSplit_Suz)
      (fun T _ _ h => h.elim (fun hL => not_isList93_of_leafType hb hA hL)
        (fun hA6 => by
          obtain ⟨-, ⟨e6⟩⟩ := hA6
          exact not_isList93_of_alt hb (n := 6) (by norm_num) (by norm_num) e6))
  | ONan =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .ONan (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShapeRk Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk)
      (fun T _ _ h => by
        obtain ⟨-, ⟨e6⟩⟩ := h
        exact not_isList93_of_alt hb (n := 6) (by norm_num) (by norm_num) e6)
  | Co2 =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co2 (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.leafShape_Co2)
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Co3 =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Co3 (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.leafShape_Co3)
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Fi22 =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi22 (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.leafShape_Fi22)
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Fi23 =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi23 (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        (HardMathSupport.Dickson.I271.TabFi23.leafShape_Fi23_of
            HardMathSupport.Dickson.I271.TabFi23.pConstrained_t3_two))
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Fi24Prime =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Fi24Prime (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.leafShape_Fi24_three)
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Th =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Th (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShape Nat.prime_three
        CFSG.HardMathSupport.Dickson.I271.leafShape_Th)
      (fun T _ _ h => not_isList93_of_leafType hb hA h)
  | Ly =>
    haveI := CFSG.Sporadic.finite_carrier_of_ne_M .Ly (by decide)
    exact sporTypes_of_carrier_centTypes hBr
      (centTypes_of_centShapeRk Nat.prime_three
        (CFSG.HardMathSupport.Dickson.I271.tabLy_centShapeRk hOut hBr))
      (fun T _ _ h => by
        rcases h with hL | hA6 | ⟨S, hS, ⟨eS⟩⟩
        · exact not_isList93_of_leafType hb hA hL
        · obtain ⟨-, ⟨e6⟩⟩ := hA6
          exact not_isList93_of_alt hb (n := 6) (by norm_num) (by norm_num) e6
        · rw [List.mem_singleton] at hS
          subst hS
          exact not_isList93_of_sporadic (s := .McL) hN2 ⟨3, by simp [k2Spor]⟩ ⟨eS⟩)
  | B =>
    exact (sporTypes_of_census Nat.prime_three hBr
      (CFSG.HardMathSupport.Dickson.BMRows.census_B_three hK)).mono
      (fun T _ hcat => by
        obtain ⟨i, hi, ⟨e⟩⟩ := hcat
        subst hi
        exact not_isList93_of_sporadic (s := .Fi22) hN2 ⟨3, by simp [k2Spor]⟩ ⟨e⟩)
  | M =>
    exact (sporTypes_of_census Nat.prime_three hBr
      (CFSG.HardMathSupport.Dickson.BMRows.census_M_three hK)).mono
      (fun T _ hcat => by
        obtain ⟨i, hi, ⟨e⟩⟩ := hcat
        rcases hi with rfl | rfl
        · exact not_isList93_of_sporadic (s := .Fi24Prime) hN2 ⟨3, by simp [k2Spor]⟩ ⟨e⟩
        · exact not_isList93_of_sporadic (s := .Th) hN2 ⟨3, by simp [k2Spor]⟩ ⟨e⟩)
  | M12 | M22 | M23 | M24 | J1 | J2 | J4 | HS | He | Ru | Co1 | HN =>
    simp only [k2Spor] at hname <;> omega

end RowCertificates

end CFSG.LocalAnalysis.GLTheoremA
