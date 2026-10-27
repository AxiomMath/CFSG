module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4FrameTransport

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree



open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Blueprint.Chevalley.TwistTag CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

theorem embE6F4_xE_coe (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    ((embE6F4 L (xE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) = f4OrbitXUnit L j c := by
  have hT : (e6FixedF4EquivAll L).symm (xE Tag.F4 L j c) = OX j c := by
    rw [MulEquiv.symm_apply_eq, psi_OX]
  have h1 : ((embE6F4 L (xE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      (((e6FixedF4EquivAll L).symm (xE Tag.F4 L j c) :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : ModGL TwistTag.E6.tag L) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem embE6F4_yE_coe (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    ((embE6F4 L (yE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) = f4OrbitYUnit L j c := by
  have hT : (e6FixedF4EquivAll L).symm (yE Tag.F4 L j c) = OY j c := by
    rw [MulEquiv.symm_apply_eq, psi_OY]
  have h1 : ((embE6F4 L (yE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      (((e6FixedF4EquivAll L).symm (yE Tag.F4 L j c) :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : ModGL TwistTag.E6.tag L) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

noncomputable def iotaE6 (L : Type) [Field L] (x : adjointGroup .F4 L) : ModGL TwistTag.E6.tag L :=
  ((embE6F4 L x : adjointGroup .E6 L) : ModGL Tag.E6 L)

theorem iotaE6_mul (L : Type) [Field L] (x y : adjointGroup .F4 L) :
    iotaE6 L (x * y) = iotaE6 L x * iotaE6 L y := by
  unfold iotaE6
  rw [map_mul, Subgroup.coe_mul]
  rfl

theorem iotaE6_one (L : Type) [Field L] : iotaE6 L 1 = 1 := by
  unfold iotaE6
  rw [map_one, Subgroup.coe_one]
  rfl

theorem iotaE6_xE (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    iotaE6 L (xE Tag.F4 L j c) = f4OrbitXUnit L j c :=
  embE6F4_xE_coe L j c

theorem iotaE6_yE (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    iotaE6 L (yE Tag.F4 L j c) = f4OrbitYUnit L j c :=
  embE6F4_yE_coe L j c

theorem weylElt_one_eq_xyx (τ : Tag) (L : Type) [Field L] (i : Fin τ.rank) :
    weylElt τ L i 1 = xUnit τ L i 1 * yUnit τ L i (-1) * xUnit τ L i 1 := by
  apply Units.ext
  simp [weylElt, xUnit, yUnit]

theorem double_orbit_identity {M : Type*} [Group M] (a b c d : M)
    (hab : a * b = b * a) (had : a * d = d * a) (hbc : b * c = c * b) :
    a * b * (c * d) * (a * b) = a * c * a * (b * d * b) := by
  calc a * b * (c * d) * (a * b) = a * b * c * (d * a) * b := by group
    _ = a * b * c * (a * d) * b := by rw [← had]
    _ = a * (b * c) * a * d * b := by group
    _ = a * (c * b) * a * d * b := by rw [hbc]
    _ = a * c * (b * a) * d * b := by group
    _ = a * c * (a * b) * d * b := by rw [← hab]
    _ = a * c * a * (b * d * b) := by group

theorem f4_orbitWord_zero : TwistTag.E6.orbitWord (f4FoldedIndex 0) = [1] := by decide
theorem f4_orbitWord_one : TwistTag.E6.orbitWord (f4FoldedIndex 1) = [3] := by decide
theorem f4_orbitWord_two : TwistTag.E6.orbitWord (f4FoldedIndex 2) = [2, 4] := by decide
theorem f4_orbitWord_three : TwistTag.E6.orbitWord (f4FoldedIndex 3) = [0, 5] := by decide

theorem f4_local_zero (L : Type) [Field L] :
    f4OrbitXUnit L 0 1 * f4OrbitYUnit L 0 (-1) * f4OrbitXUnit L 0 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 0)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_eq_xyx]

theorem f4_local_one (L : Type) [Field L] :
    f4OrbitXUnit L 1 1 * f4OrbitYUnit L 1 (-1) * f4OrbitXUnit L 1 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 1)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_one, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_eq_xyx]

theorem f4_local_two (L : Type) [Field L] :
    f4OrbitXUnit L 2 1 * f4OrbitYUnit L 2 (-1) * f4OrbitXUnit L 2 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 2)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag L 2 1) (xUnit TwistTag.E6.tag L 4 1) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 2) L (by decide) (by decide) 1 1
  have had : Commute (xUnit TwistTag.E6.tag L 2 1) (yUnit TwistTag.E6.tag L 4 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) L (by decide) (by decide) (by decide) 1 (-1)
  have hbc : Commute (xUnit TwistTag.E6.tag L 4 1) (yUnit TwistTag.E6.tag L 2 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) L (by decide) (by decide) (by decide) 1 (-1)
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_two, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_eq_xyx]
  exact double_orbit_identity _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_local_three (L : Type) [Field L] :
    f4OrbitXUnit L 3 1 * f4OrbitYUnit L 3 (-1) * f4OrbitXUnit L 3 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 3)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag L 0 1) (xUnit TwistTag.E6.tag L 5 1) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 3) L (by decide) (by decide) 1 1
  have had : Commute (xUnit TwistTag.E6.tag L 0 1) (yUnit TwistTag.E6.tag L 5 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) L (by decide) (by decide) (by decide) 1 (-1)
  have hbc : Commute (xUnit TwistTag.E6.tag L 5 1) (yUnit TwistTag.E6.tag L 0 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) L (by decide) (by decide) (by decide) 1 (-1)
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_three, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_eq_xyx]
  exact double_orbit_identity _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_local_all (L : Type) [Field L] (j : Fin Tag.F4.rank) :
    f4OrbitXUnit L j 1 * f4OrbitYUnit L j (-1) * f4OrbitXUnit L j 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  fin_cases j
  · exact f4_local_zero L
  · exact f4_local_one L
  · exact f4_local_two L
  · exact f4_local_three L

theorem f4_T_coe (L : Type) [Field L] (ω : List (Fin Tag.F4.rank)) :
    (((ω.map fun j => xE Tag.F4 L j 1 * yE Tag.F4 L j (-1) * xE Tag.F4 L j 1).prod :
        adjointGroup .F4 L) : ModGL Tag.F4 L) =
      (ω.map fun j => weylElt Tag.F4 L j 1).prod := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, weylElt_one_eq_xyx]
    rfl

theorem list_prod_flatten {α β M : Type*} [Monoid M] (F : α → List β) (g : β → M) (ω : List α) :
    (ω.map fun j => ((F j).map g).prod).prod = (((ω.map F).flatten).map g).prod := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.flatten_cons, List.map_append,
      List.prod_append]

theorem f4_triple_iota (L : Type) [Field L] (j : Fin Tag.F4.rank) :
    iotaE6 L (xE Tag.F4 L j 1 * yE Tag.F4 L j (-1) * xE Tag.F4 L j 1) =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun k => weylElt TwistTag.E6.tag L k 1).prod := by
  rw [iotaE6_mul, iotaE6_mul, iotaE6_xE, iotaE6_yE]
  exact f4_local_all L j

theorem f4_T_iota (L : Type) [Field L] (ω : List (Fin Tag.F4.rank)) :
    iotaE6 L (ω.map fun j => xE Tag.F4 L j 1 * yE Tag.F4 L j (-1) * xE Tag.F4 L j 1).prod =
      (ω.map fun j => ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map
        fun k => weylElt TwistTag.E6.tag L k 1).prod).prod := by
  induction ω with
  | nil => simp only [List.map_nil, List.prod_nil]; exact iotaE6_one L
  | cons j ω ih =>
    rw [List.map_cons, List.prod_cons, iotaE6_mul, ih, List.map_cons, List.prod_cons, f4_triple_iota]

theorem folded_wordF4_eq :
    (TwClass.wordF4.map fun j => TwistTag.E6.orbitWord (f4FoldedIndex j)).flatten =
      [3, 2, 4, 0, 5, 3, 2, 4, 3] := by
  decide +kernel

theorem folded_reduced : (coxeterSystem Tag.E6).IsReduced [3, 2, 4, 0, 5, 3, 2, 4, 3] :=
  isReduced_of_reducedCheck (by decide +kernel)

theorem folded_wordProd_eq :
    (coxeterSystem Tag.E6).wordProd [3, 2, 4, 0, 5, 3, 2, 4, 3] =
      (coxeterSystem Tag.E6).wordProd TwClass.wordE6 := by
  have key : ∀ i : Fin Tag.E6.rank,
      ((coxeterSystem Tag.E6).wordProd [3, 2, 4, 0, 5, 3, 2, 4, 3])⁻¹ •
          (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
        ((coxeterSystem Tag.E6).wordProd TwClass.wordE6)⁻¹ •
          (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    intro i
    rw [← reflectWord_eq, ← reflectWord_eq]
    fin_cases i <;> decide +kernel
  exact inv_injective (ext_single key)

theorem e6TransportTits_holds : E6TransportTits := by
  intro L _
  refine ⟨(TwClass.wordF4.map fun j => xE Tag.F4 L j 1 * yE Tag.F4 L j (-1) * xE Tag.F4 L j 1).prod,
    ?_, ?_⟩
  · have hred : (coxeterSystem TwClass.f4Six.tag).IsReduced TwClass.wordF4 :=
      isReduced_of_reducedCheck (by decide +kernel)
    have key := canonicalRep_wordProd (R := L) (cs := coxeterSystem TwClass.f4Six.tag) hred
    rw [f4_T_coe]
    exact key.symm
  · show iotaE6 L _ = _
    rw [f4_T_iota, list_prod_flatten (fun j => TwistTag.E6.orbitWord (f4FoldedIndex j))
      (fun k => weylElt TwistTag.E6.tag L k 1) TwClass.wordF4, folded_wordF4_eq]
    have hredE : (coxeterSystem TwClass.e6Six.tag).IsReduced [3, 2, 4, 0, 5, 3, 2, 4, 3] :=
      folded_reduced
    have key := canonicalRep_wordProd (R := L) (cs := coxeterSystem TwClass.e6Six.tag) hredE
    have hw : TwClass.e6Six.w = (coxeterSystem TwClass.e6Six.tag).wordProd [3, 2, 4, 0, 5, 3, 2, 4, 3] :=
      folded_wordProd_eq.symm
    rw [hw]
    exact key.symm


theorem f4_local_gen_zero (L : Type) [Field L] (c d : L) :
    f4OrbitXUnit L 0 c * f4OrbitYUnit L 0 d * f4OrbitXUnit L 0 c =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 0)).map fun k =>
        xUnit TwistTag.E6.tag L k c * yUnit TwistTag.E6.tag L k d * xUnit TwistTag.E6.tag L k c).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

theorem f4_local_gen_one (L : Type) [Field L] (c d : L) :
    f4OrbitXUnit L 1 c * f4OrbitYUnit L 1 d * f4OrbitXUnit L 1 c =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 1)).map fun k =>
        xUnit TwistTag.E6.tag L k c * yUnit TwistTag.E6.tag L k d * xUnit TwistTag.E6.tag L k c).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_one, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

theorem f4_local_gen_two (L : Type) [Field L] (c d : L) :
    f4OrbitXUnit L 2 c * f4OrbitYUnit L 2 d * f4OrbitXUnit L 2 c =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 2)).map fun k =>
        xUnit TwistTag.E6.tag L k c * yUnit TwistTag.E6.tag L k d * xUnit TwistTag.E6.tag L k c).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag L 2 c) (xUnit TwistTag.E6.tag L 4 c) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 2) L (by decide) (by decide) c c
  have had : Commute (xUnit TwistTag.E6.tag L 2 c) (yUnit TwistTag.E6.tag L 4 d) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) L (by decide) (by decide) (by decide) c d
  have hbc : Commute (xUnit TwistTag.E6.tag L 4 c) (yUnit TwistTag.E6.tag L 2 d) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) L (by decide) (by decide) (by decide) c d
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_two, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  exact double_orbit_identity _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_local_gen_three (L : Type) [Field L] (c d : L) :
    f4OrbitXUnit L 3 c * f4OrbitYUnit L 3 d * f4OrbitXUnit L 3 c =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 3)).map fun k =>
        xUnit TwistTag.E6.tag L k c * yUnit TwistTag.E6.tag L k d * xUnit TwistTag.E6.tag L k c).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag L 0 c) (xUnit TwistTag.E6.tag L 5 c) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 3) L (by decide) (by decide) c c
  have had : Commute (xUnit TwistTag.E6.tag L 0 c) (yUnit TwistTag.E6.tag L 5 d) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) L (by decide) (by decide) (by decide) c d
  have hbc : Commute (xUnit TwistTag.E6.tag L 5 c) (yUnit TwistTag.E6.tag L 0 d) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) L (by decide) (by decide) (by decide) c d
  simp only [f4OrbitXUnit, f4OrbitYUnit, f4_orbitWord_three, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  exact double_orbit_identity _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_nodes : ∀ j : Fin Tag.F4.rank, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide

theorem f4_local_gen (L : Type) [Field L] (j : Fin Tag.F4.rank) (c d : L) :
    f4OrbitXUnit L j c * f4OrbitYUnit L j d * f4OrbitXUnit L j c =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun k =>
        xUnit TwistTag.E6.tag L k c * yUnit TwistTag.E6.tag L k d * xUnit TwistTag.E6.tag L k c).prod := by
  rcases f4_nodes j with rfl | rfl | rfl | rfl
  · exact f4_local_gen_zero L c d
  · exact f4_local_gen_one L c d
  · exact f4_local_gen_two L c d
  · exact f4_local_gen_three L c d

noncomputable def wAdj (L : Type) [Field L] (i : Fin Tag.F4.rank) (t : Lˣ) : adjointGroup .F4 L :=
  ⟨weylElt Tag.F4 L i t, weylElt_mem_adjointGroup i t⟩

noncomputable def torusAdj (L : Type) [Field L] (i : Fin Tag.F4.rank) (t : Lˣ) : adjointGroup .F4 L :=
  ⟨torusElt Tag.F4 L i t, torusElt_mem_adjointGroup i t⟩

theorem weylElt_eq_xyx (τ : Tag) (L : Type) [Field L] (i : Fin τ.rank) (t : Lˣ) :
    weylElt τ L i t = xUnit τ L i (t : L) * yUnit τ L i (-((t⁻¹ : Lˣ) : L)) * xUnit τ L i (t : L) := by
  apply Units.ext
  simp [weylElt, xUnit, yUnit]

theorem wAdj_eq_xyx (L : Type) [Field L] (i : Fin Tag.F4.rank) (t : Lˣ) :
    wAdj L i t = xE Tag.F4 L i (t : L) * yE Tag.F4 L i (-((t⁻¹ : Lˣ) : L)) * xE Tag.F4 L i (t : L) := by
  apply Subtype.ext
  exact weylElt_eq_xyx Tag.F4 L i t

theorem iotaE6_wAdj (L : Type) [Field L] (i : Fin Tag.F4.rank) (t : Lˣ) :
    iotaE6 L (wAdj L i t) =
      ((TwistTag.E6.orbitWord (f4FoldedIndex i)).map fun k => weylElt TwistTag.E6.tag L k t).prod := by
  rw [wAdj_eq_xyx, iotaE6_mul, iotaE6_mul, iotaE6_xE, iotaE6_yE, f4_local_gen]
  simp only [weylElt_eq_xyx TwistTag.E6.tag L]

theorem commute_weylElt_orbit (L : Type) [Field L] (a : Fin TwistTag.E6.foldedTag.rank)
    (k l : Fin TwistTag.E6.tag.rank) (hk : k ∈ TwistTag.E6.orbit a) (hl : l ∈ TwistTag.E6.orbit a)
    (hkl : k ≠ l) (t u : Lˣ) :
    Commute (weylElt TwistTag.E6.tag L k t) (weylElt TwistTag.E6.tag L l u) := by
  rw [weylElt_eq_xyx TwistTag.E6.tag L k t, weylElt_eq_xyx TwistTag.E6.tag L l u]
  have hxx : ∀ c d : L, Commute (xUnit TwistTag.E6.tag L k c) (xUnit TwistTag.E6.tag L l d) :=
    fun c d => commute_xUnit_xUnit (a := a) L hk hl c d
  have hxy : ∀ c d : L, Commute (xUnit TwistTag.E6.tag L k c) (yUnit TwistTag.E6.tag L l d) :=
    fun c d => commute_xUnit_yUnit (a := a) L hk hl hkl c d
  have hyx : ∀ c d : L, Commute (yUnit TwistTag.E6.tag L k c) (xUnit TwistTag.E6.tag L l d) :=
    fun c d => (commute_xUnit_yUnit (a := a) L hl hk hkl.symm d c).symm
  have hyy : ∀ c d : L, Commute (yUnit TwistTag.E6.tag L k c) (yUnit TwistTag.E6.tag L l d) :=
    fun c d => commute_yUnit_yUnit (a := a) L hk hl hkl c d
  apply Commute.mul_left
  · apply Commute.mul_left
    · exact Commute.mul_right (Commute.mul_right (hxx _ _) (hxy _ _)) (hxx _ _)
    · exact Commute.mul_right (Commute.mul_right (hyx _ _) (hyy _ _)) (hyx _ _)
  · exact Commute.mul_right (Commute.mul_right (hxx _ _) (hxy _ _)) (hxx _ _)

theorem swap_middle {M : Type*} [Group M] (A B C D : M) (h : B * C = C * B) :
    A * B * (C * D) = A * C * (B * D) := by
  calc A * B * (C * D) = A * (B * C) * D := by group
    _ = A * (C * B) * D := by rw [h]
    _ = A * C * (B * D) := by group

theorem iotaE6_torusAdj (L : Type) [Field L] (i : Fin Tag.F4.rank) (t : Lˣ) :
    iotaE6 L (torusAdj L i t) =
      ((TwistTag.E6.orbitWord (f4FoldedIndex i)).map fun k => torusElt TwistTag.E6.tag L k t).prod := by
  have hsplit : torusAdj L i t = wAdj L i t * wAdj L i (-1) := by
    apply Subtype.ext
    rfl
  rw [hsplit, iotaE6_mul, iotaE6_wAdj, iotaE6_wAdj]
  rcases f4_nodes i with rfl | rfl | rfl | rfl
  · simp only [f4_orbitWord_zero, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · simp only [f4_orbitWord_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · simp only [f4_orbitWord_two, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hc : Commute (weylElt TwistTag.E6.tag L 4 t) (weylElt TwistTag.E6.tag L 2 (-1)) :=
      commute_weylElt_orbit L (f4FoldedIndex 2) 4 2 (by decide) (by decide) (by decide) t (-1)
    rw [swap_middle _ _ _ _ hc.eq]
    rfl
  · simp only [f4_orbitWord_three, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hc : Commute (weylElt TwistTag.E6.tag L 5 t) (weylElt TwistTag.E6.tag L 0 (-1)) :=
      commute_weylElt_orbit L (f4FoldedIndex 3) 5 0 (by decide) (by decide) (by decide) t (-1)
    rw [swap_middle _ _ _ _ hc.eq]
    rfl

noncomputable def levi6Set (L : Type) [Field L] : Subgroup (ModGL Tag.F4 L) where
  carrier := {g | ∃ h : adjointGroup .F4 L, (h : ModGL Tag.F4 L) = g ∧
    ((embE6F4 L h : adjointGroup .E6 L) : ModGL Tag.E6 L) ∈ Lθ Tag.E6 L}
  mul_mem' := by
    rintro _ _ ⟨h1, rfl, h1'⟩ ⟨h2, rfl, h2'⟩
    refine ⟨h1 * h2, rfl, ?_⟩
    rw [map_mul, Subgroup.coe_mul]
    exact (Lθ Tag.E6 L).mul_mem h1' h2'
  one_mem' := ⟨1, rfl, by rw [map_one, Subgroup.coe_one]; exact (Lθ Tag.E6 L).one_mem⟩
  inv_mem' := by
    rintro _ ⟨h, rfl, h'⟩
    refine ⟨h⁻¹, rfl, ?_⟩
    rw [map_inv, Subgroup.coe_inv]
    exact (Lθ Tag.E6 L).inv_mem h'

theorem mem_levi6Set (L : Type) [Field L] (g : ModGL Tag.F4 L) :
    g ∈ levi6Set L ↔ ∃ h : adjointGroup .F4 L, (h : ModGL Tag.F4 L) = g ∧
      ((embE6F4 L h : adjointGroup .E6 L) : ModGL Tag.E6 L) ∈ Lθ Tag.E6 L :=
  Iff.rfl

theorem torusElt_mem_lev6 (L : Type) [Field L] (k : Fin Tag.E6.rank) (t : Lˣ) :
    torusElt TwistTag.E6.tag L k t ∈ Lθ Tag.E6 L := by
  refine le_sup_left (a := torusGroup Tag.E6 L) ?_
  exact Subgroup.subset_closure ⟨(k, t), rfl⟩

theorem xUnit_mem_lev6 (L : Type) [Field L] (k : Fin Tag.E6.rank) (hk : k ≠ (1 : Fin Tag.E6.rank))
    (c : L) : xUnit Tag.E6 L k c ∈ Lθ Tag.E6 L := by
  refine le_sup_right (a := torusGroup Tag.E6 L) ?_
  exact Subgroup.subset_closure ⟨k, hk, c, Or.inl rfl⟩

theorem yUnit_mem_lev6 (L : Type) [Field L] (k : Fin Tag.E6.rank) (hk : k ≠ (1 : Fin Tag.E6.rank))
    (c : L) : yUnit Tag.E6 L k c ∈ Lθ Tag.E6 L := by
  refine le_sup_right (a := torusGroup Tag.E6 L) ?_
  exact Subgroup.subset_closure ⟨k, hk, c, Or.inr rfl⟩

theorem torus_le_levi6Set (L : Type) [Field L] : torusGroup Tag.F4 L ≤ levi6Set L := by
  unfold torusGroup
  apply (Subgroup.closure_le _).2
  rintro _ ⟨⟨i, t⟩, rfl⟩
  refine (mem_levi6Set L _).2 ⟨torusAdj L i t, rfl, ?_⟩
  show iotaE6 L (torusAdj L i t) ∈ Lθ Tag.E6 L
  rw [iotaE6_torusAdj]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_lev6 L k t

theorem orbit_ne_one (j : Fin Tag.F4.rank) (hj : j ≠ 0) :
    ∀ k ∈ TwistTag.E6.orbitWord (f4FoldedIndex j), k ≠ (1 : Fin TwistTag.E6.tag.rank) := by
  rcases f4_nodes j with rfl | rfl | rfl | rfl
  · exact absurd rfl hj
  · rw [f4_orbitWord_one]; decide
  · rw [f4_orbitWord_two]; decide
  · rw [f4_orbitWord_three]; decide

theorem xUnit_levi6Set (L : Type) [Field L] (j : Fin Tag.F4.rank) (hj : j ≠ 0) (c : L) :
    xUnit Tag.F4 L j c ∈ levi6Set L := by
  rw [mem_levi6Set]
  refine ⟨xE Tag.F4 L j c, rfl, ?_⟩
  show iotaE6 L (xE Tag.F4 L j c) ∈ Lθ Tag.E6 L
  rw [iotaE6_xE]
  unfold f4OrbitXUnit
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_lev6 L k (orbit_ne_one j hj k hk) c

theorem yUnit_levi6Set (L : Type) [Field L] (j : Fin Tag.F4.rank) (hj : j ≠ 0) (c : L) :
    yUnit Tag.F4 L j c ∈ levi6Set L := by
  rw [mem_levi6Set]
  refine ⟨yE Tag.F4 L j c, rfl, ?_⟩
  show iotaE6 L (yE Tag.F4 L j c) ∈ Lθ Tag.E6 L
  rw [iotaE6_yE]
  unfold f4OrbitYUnit
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact yUnit_mem_lev6 L k (orbit_ne_one j hj k hk) c

theorem e6TransportLevi_holds : E6TransportLevi := by
  intro L _ g hg
  have hle : Lθ Tag.F4 L ≤ levi6Set L := by
    show parabolicLevi Tag.F4 L (Jθ Tag.F4) ≤ levi6Set L
    unfold parabolicLevi
    apply sup_le (torus_le_levi6Set L)
    apply (Subgroup.closure_le _).2
    rintro _ ⟨j, hj, c, (rfl | rfl)⟩
    · exact xUnit_levi6Set L j hj c
    · exact yUnit_levi6Set L j hj c
  exact (mem_levi6Set L g).1 (hle hg)

theorem mulSingle_apply_zpow {L : Type} [Field L] {n : ℕ} (i j : Fin n) (x : Lˣ) :
    (Pi.mulSingle (M := fun _ : Fin n => Lˣ) i x) j = x ^ (if j = i then (1 : ℤ) else 0) := by
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg h, zpow_zero, Pi.mulSingle_eq_of_ne h]

theorem zSplit_eq_torusAdj (L : Type) [Field L] (ω : Lˣ) :
    zSplit L ω = torusAdj L 0 (ω ^ (3 : ℤ)) * torusAdj L 1 (ω ^ (6 : ℤ)) *
      torusAdj L 2 (ω ^ (4 : ℤ)) * torusAdj L 3 (ω ^ (2 : ℤ)) := by
  apply Subtype.ext
  show rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) =
    torusElt Tag.F4 L 0 (ω ^ (3 : ℤ)) * torusElt Tag.F4 L 1 (ω ^ (6 : ℤ)) *
      torusElt Tag.F4 L 2 (ω ^ (4 : ℤ)) * torusElt Tag.F4 L 3 (ω ^ (2 : ℤ))
  simp only [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, ← zpow_mul, ← zpow_add]
  rw [mulSingle_apply_zpow]
  congr 1
  revert j
  decide

theorem e6TransportSplit_holds : E6TransportSplit := by
  intro L _ ω _
  show iotaE6 L (zSplit L ω) =
    rootDiagUnit TwistTag.E6.tag (Pi.mulSingle (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) ω)
  rw [zSplit_eq_torusAdj]
  simp only [iotaE6_mul, iotaE6_torusAdj, f4_orbitWord_zero, f4_orbitWord_one,
    f4_orbitWord_two, f4_orbitWord_three, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  simp only [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, ← zpow_mul, ← zpow_add]
  rw [mulSingle_apply_zpow]
  congr 1
  revert j
  decide

theorem f4OrbitXUnit_natural {K L : Type} [Field K] [Field L] (f : K →+* L)
    (ψ : ∀ τ : Tag, ModGL τ K →* ModGL τ L)
    (hx : ∀ (τ : Tag) (i : Fin τ.rank) (c : K), ψ τ (xUnit τ K i c) = xUnit τ L i (f c))
    (j : Fin Tag.F4.rank) (c : K) :
    ψ TwistTag.E6.tag (f4OrbitXUnit K j c) = f4OrbitXUnit L j (f c) := by
  simp only [f4OrbitXUnit, map_list_prod, List.map_map, Function.comp_def, hx]

theorem f4OrbitYUnit_natural {K L : Type} [Field K] [Field L] (f : K →+* L)
    (ψ : ∀ τ : Tag, ModGL τ K →* ModGL τ L)
    (hy : ∀ (τ : Tag) (i : Fin τ.rank) (c : K), ψ τ (yUnit τ K i c) = yUnit τ L i (f c))
    (j : Fin Tag.F4.rank) (c : K) :
    ψ TwistTag.E6.tag (f4OrbitYUnit K j c) = f4OrbitYUnit L j (f c) := by
  simp only [f4OrbitYUnit, map_list_prod, List.map_map, Function.comp_def, hy]

theorem iotaE6_inv (L : Type) [Field L] (x : adjointGroup .F4 L) :
    iotaE6 L x⁻¹ = (iotaE6 L x)⁻¹ := by
  unfold iotaE6
  rw [map_inv, Subgroup.coe_inv]
  rfl

theorem iota_transport {K L : Type} [Field K] [Field L] (f : K →+* L)
    (ψ : ∀ τ : Tag, ModGL τ K →* ModGL τ L)
    (hx : ∀ (τ : Tag) (i : Fin τ.rank) (c : K), ψ τ (xUnit τ K i c) = xUnit τ L i (f c))
    (hy : ∀ (τ : Tag) (i : Fin τ.rank) (c : K), ψ τ (yUnit τ K i c) = yUnit τ L i (f c))
    (g : ModGL Tag.F4 K) (hg : g ∈ adjointGroup Tag.F4 K) :
    ∃ h' : adjointGroup Tag.F4 L, (h' : ModGL Tag.F4 L) = ψ Tag.F4 g ∧
      ψ TwistTag.E6.tag (iotaE6 K ⟨g, hg⟩) = iotaE6 L h' := by
  unfold adjointGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx' =>
    obtain ⟨i, c, h | h⟩ := hx'
    · obtain rfl : x = xUnit Tag.F4 K i c := Units.ext h
      refine ⟨xE Tag.F4 L i (f c), (hx Tag.F4 i c).symm, ?_⟩
      show ψ TwistTag.E6.tag (iotaE6 K (xE Tag.F4 K i c)) = iotaE6 L (xE Tag.F4 L i (f c))
      rw [iotaE6_xE, iotaE6_xE]
      exact f4OrbitXUnit_natural f ψ hx i c
    · obtain rfl : x = yUnit Tag.F4 K i c := Units.ext h
      refine ⟨yE Tag.F4 L i (f c), (hy Tag.F4 i c).symm, ?_⟩
      show ψ TwistTag.E6.tag (iotaE6 K (yE Tag.F4 K i c)) = iotaE6 L (yE Tag.F4 L i (f c))
      rw [iotaE6_yE, iotaE6_yE]
      exact f4OrbitYUnit_natural f ψ hy i c
  | one =>
    refine ⟨1, by simp, ?_⟩
    show ψ TwistTag.E6.tag (iotaE6 K 1) = iotaE6 L 1
    rw [iotaE6_one, iotaE6_one, map_one]
  | mul x y hx1 hy1 ih1 ih2 =>
    obtain ⟨a, ha1, ha2⟩ := ih1
    obtain ⟨b, hb1, hb2⟩ := ih2
    refine ⟨a * b, ?_, ?_⟩
    · rw [Subgroup.coe_mul, ha1, hb1, map_mul]
    · show ψ TwistTag.E6.tag (iotaE6 K (⟨x, hx1⟩ * ⟨y, hy1⟩)) = iotaE6 L (a * b)
      rw [iotaE6_mul, iotaE6_mul, map_mul, ha2, hb2]
  | inv x hx1 ih =>
    obtain ⟨a, ha1, ha2⟩ := ih
    refine ⟨a⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_inv, ha1, map_inv]
    · show ψ TwistTag.E6.tag (iotaE6 K (⟨x, hx1⟩⁻¹)) = iotaE6 L a⁻¹
      rw [iotaE6_inv, iotaE6_inv, map_inv, ha2]

theorem e6TransportFrob_holds : E6TransportFrob := by
  intro L _ φ h
  exact iota_transport φ (fun τ => Units.map (entrywiseHom (τ := τ) φ))
    (fun τ i c => units_map_entrywiseHom_xUnit (τ := τ) φ i c)
    (fun τ i c => units_map_entrywiseHom_yUnit (τ := τ) φ i c) h.1 h.2

theorem e6TransportBase_holds : E6TransportBase := by
  intro K L _ _ _ z
  exact iota_transport (algebraMap K L) (fun τ => baseChangeGL (τ := τ) (algebraMap K L))
    (fun τ i c => baseChangeGL_xUnit (τ := τ) (algebraMap K L) i c)
    (fun τ i c => baseChangeGL_yUnit (τ := τ) (algebraMap K L) i c) z.1 z.2

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
