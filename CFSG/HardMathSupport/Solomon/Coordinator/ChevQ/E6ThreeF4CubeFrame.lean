module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeClose
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4Two
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false

theorem commute_conjBy_of_commute {G : Type*} [Group G] {N Y s : G}
    (h : Commute Y (N⁻¹ * s * N)) : Commute (N * Y * N⁻¹) s := by
  show N * Y * N⁻¹ * s = s * (N * Y * N⁻¹)
  calc N * Y * N⁻¹ * s = N * (Y * (N⁻¹ * s * N)) * N⁻¹ := by group
    _ = N * (N⁻¹ * s * N * Y) * N⁻¹ := by rw [h.eq]
    _ = s * (N * Y * N⁻¹) := by group

@[expose] def frameWordF4 : Fin 4 → List (Fin Tag.F4.rank) :=
  ![[3, 2], [0, 1, 2, 1, 0, 3, 2], [], [2]]

@[expose] def unfoldF4 (ω : List (Fin Tag.F4.rank)) : List (Fin Tag.E6.rank) :=
  (ω.map fun j => TwistTag.E6.orbitWord (f4FoldedIndex j)).flatten

theorem f4Frame_eq_foldr : ∀ i : Fin 4,
    f4Frame i = (frameWordF4 i).foldr (reflect .F4) (Pi.single (1 : Fin Tag.F4.rank) 1) := by
  decide +kernel

theorem frame_antiA_vanish : ∀ i : Fin 4,
    ∑ j, (Tag.E6.cartan (e6Index 2) j - Tag.E6.cartan (e6Index 4) j) *
      ((unfoldF4 (frameWordF4 i)).foldr (reflect Tag.E6) (Pi.single (e6Index 3) 1)) j = 0 := by
  decide +kernel

theorem frame_antiB_vanish : ∀ i : Fin 4,
    ∑ j, (Tag.E6.cartan (e6Index 0) j - Tag.E6.cartan (e6Index 5) j) *
      ((unfoldF4 (frameWordF4 i)).foldr (reflect Tag.E6) (Pi.single (e6Index 3) 1)) j = 0 := by
  decide +kernel

theorem orbitWord_F4_node0 : TwistTag.E6.orbitWord (f4FoldedIndex 0) = [1] := by decide
theorem orbitWord_F4_node1 : TwistTag.E6.orbitWord (f4FoldedIndex 1) = [3] := by decide
theorem orbitWord_F4_node2 : TwistTag.E6.orbitWord (f4FoldedIndex 2) = [2, 4] := by decide
theorem orbitWord_F4_node3 : TwistTag.E6.orbitWord (f4FoldedIndex 3) = [0, 5] := by decide

theorem double_orbit_identity_aux {M : Type*} [Group M] (a b c d : M)
    (hab : a * b = b * a) (had : a * d = d * a) (hbc : b * c = c * b) :
    a * b * (c * d) * (a * b) = a * c * a * (b * d * b) := by
  calc a * b * (c * d) * (a * b) = a * b * c * (d * a) * b := by group
    _ = a * b * c * (a * d) * b := by rw [← had]
    _ = a * (b * c) * a * d * b := by group
    _ = a * (c * b) * a * d * b := by rw [hbc]
    _ = a * c * (b * a) * d * b := by group
    _ = a * c * (a * b) * d * b := by rw [← hab]
    _ = a * c * a * (b * d * b) := by group

section Torus


theorem coxeterWordProd_smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem rootChar_antiCharA {K : Type} [Field K] (u : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (antiCharA u) v =
      u ^ ∑ j, (Tag.E6.cartan (e6Index 2) j - Tag.E6.cartan (e6Index 4) j) * v j := by
  rw [← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [antiCharA]
  rw [inv_zpow', ← zpow_add, ← zpow_mul]
  congr 1

theorem rootChar_antiCharB {K : Type} [Field K] (u : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (antiCharB u) v =
      u ^ ∑ j, (Tag.E6.cartan (e6Index 0) j - Tag.E6.cartan (e6Index 5) j) * v j := by
  rw [← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [antiCharB]
  rw [inv_zpow', ← zpow_add, ← zpow_mul]
  congr 1

theorem weylElt_one_xyx (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) :
    weylElt τ K i 1 = xUnit τ K i 1 * yUnit τ K i (-1) * xUnit τ K i 1 := by
  apply Units.ext
  simp [weylElt, xUnit, yUnit]

end Torus

section Lifts


theorem weylWord_inv_conj_rootDiagUnit {L : Type} [Field L] (ω : List (Fin Tag.E6.rank))
    (a : Fin Tag.E6.rank → Lˣ) :
    (weylWord L ω)⁻¹ * rootDiagUnit Tag.E6 a * weylWord L ω =
      rootDiagUnit Tag.E6 (weylAct ((coxeterSystem Tag.E6).wordProd ω)⁻¹ a) := by
  have h := weylWord_conj_rootDiagUnit (L := L) ω
    (weylAct ((coxeterSystem Tag.E6).wordProd ω)⁻¹ a)
  rw [← weylAct_mul, mul_inv_cancel, weylAct_one] at h
  rw [← h]
  group

theorem coe_embE6F4_xE (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    ((embE6F4 K (xE Tag.F4 K j c) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      f4OrbitXUnit K j c := by
  have hT : (e6FixedF4EquivAll K).symm (xE Tag.F4 K j c) = OX j c := by
    rw [MulEquiv.symm_apply_eq, psi_OX]
  have h1 : ((embE6F4 K (xE Tag.F4 K j c) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      (((e6FixedF4EquivAll K).symm (xE Tag.F4 K j c) :
        twistedFixedGroup TwistTag.E6 K (RingHom.id K)) : ModGL TwistTag.E6.tag K) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem coe_embE6F4_yE (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    ((embE6F4 K (yE Tag.F4 K j c) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      f4OrbitYUnit K j c := by
  have hT : (e6FixedF4EquivAll K).symm (yE Tag.F4 K j c) = OY j c := by
    rw [MulEquiv.symm_apply_eq, psi_OY]
  have h1 : ((embE6F4 K (yE Tag.F4 K j c) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      (((e6FixedF4EquivAll K).symm (yE Tag.F4 K j c) :
        twistedFixedGroup TwistTag.E6 K (RingHom.id K)) : ModGL TwistTag.E6.tag K) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem f4_orbit_xyx_zero (K : Type) [Field K] :
    f4OrbitXUnit K 0 1 * f4OrbitYUnit K 0 (-1) * f4OrbitXUnit K 0 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 0)).map
        fun k => weylElt TwistTag.E6.tag K k 1).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, orbitWord_F4_node0, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_xyx]

theorem f4_orbit_xyx_one (K : Type) [Field K] :
    f4OrbitXUnit K 1 1 * f4OrbitYUnit K 1 (-1) * f4OrbitXUnit K 1 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 1)).map
        fun k => weylElt TwistTag.E6.tag K k 1).prod := by
  simp only [f4OrbitXUnit, f4OrbitYUnit, orbitWord_F4_node1, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_xyx]

theorem f4_orbit_xyx_two (K : Type) [Field K] :
    f4OrbitXUnit K 2 1 * f4OrbitYUnit K 2 (-1) * f4OrbitXUnit K 2 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 2)).map
        fun k => weylElt TwistTag.E6.tag K k 1).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag K 2 1) (xUnit TwistTag.E6.tag K 4 1) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 2) K (by decide) (by decide) 1 1
  have had : Commute (xUnit TwistTag.E6.tag K 2 1) (yUnit TwistTag.E6.tag K 4 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) K (by decide) (by decide) (by decide) 1 (-1)
  have hbc : Commute (xUnit TwistTag.E6.tag K 4 1) (yUnit TwistTag.E6.tag K 2 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 2) K (by decide) (by decide) (by decide) 1 (-1)
  simp only [f4OrbitXUnit, f4OrbitYUnit, orbitWord_F4_node2, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_xyx]
  exact double_orbit_identity_aux _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_orbit_xyx_three (K : Type) [Field K] :
    f4OrbitXUnit K 3 1 * f4OrbitYUnit K 3 (-1) * f4OrbitXUnit K 3 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex 3)).map
        fun k => weylElt TwistTag.E6.tag K k 1).prod := by
  have hab : Commute (xUnit TwistTag.E6.tag K 0 1) (xUnit TwistTag.E6.tag K 5 1) :=
    commute_xUnit_xUnit (a := f4FoldedIndex 3) K (by decide) (by decide) 1 1
  have had : Commute (xUnit TwistTag.E6.tag K 0 1) (yUnit TwistTag.E6.tag K 5 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) K (by decide) (by decide) (by decide) 1 (-1)
  have hbc : Commute (xUnit TwistTag.E6.tag K 5 1) (yUnit TwistTag.E6.tag K 0 (-1)) :=
    commute_xUnit_yUnit (a := f4FoldedIndex 3) K (by decide) (by decide) (by decide) 1 (-1)
  simp only [f4OrbitXUnit, f4OrbitYUnit, orbitWord_F4_node3, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylElt_one_xyx]
  exact double_orbit_identity_aux _ _ _ _ hab.eq had.eq hbc.eq

theorem f4_orbit_xyx (K : Type) [Field K] (j : Fin Tag.F4.rank) :
    f4OrbitXUnit K j 1 * f4OrbitYUnit K j (-1) * f4OrbitXUnit K j 1 =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map
        fun k => weylElt TwistTag.E6.tag K k 1).prod := by
  fin_cases j
  · exact f4_orbit_xyx_zero K
  · exact f4_orbit_xyx_one K
  · exact f4_orbit_xyx_two K
  · exact f4_orbit_xyx_three K

theorem weylElement_F4_eq_xyx (K : Type) [Field K] (j : Fin Tag.F4.rank) :
    weylElement Tag.F4 K j = xE Tag.F4 K j 1 * yE Tag.F4 K j (-1) * xE Tag.F4 K j 1 :=
  Subtype.ext (weylElt_one_xyx Tag.F4 K j)

theorem coe_embE6F4_weylElement (K : Type) [Field K] (j : Fin Tag.F4.rank) :
    ((embE6F4 K (weylElement Tag.F4 K j) : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      weylWord (τ := Tag.E6) K (TwistTag.E6.orbitWord (f4FoldedIndex j)) := by
  rw [weylElement_F4_eq_xyx, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_embE6F4_xE, coe_embE6F4_yE]
  exact f4_orbit_xyx K j

theorem coe_embE6F4_weylProd (K : Type) [Field K] (ω : List (Fin Tag.F4.rank)) :
    ((embE6F4 K (ω.map (weylElement Tag.F4 K)).prod : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      weylWord K (unfoldF4 ω) := by
  induction ω with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one, Subgroup.coe_one]
    rfl
  | cons j ω ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Subgroup.coe_mul, ih, coe_embE6F4_weylElement]
    exact (weylWord_append (τ := Tag.E6) K _ _).symm

theorem xPar_single_F4 (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily Tag.F4) (Pi.single j 1) c =
      xE Tag.F4 K j c := by
  rw [CFSG.LieType.Steinberg.Adjoint.xPar_simple]
  exact Subtype.ext ((rootOperatorFamily Tag.F4).eltUnit_simple j c)

theorem xPar_neg_single_F4 (K : Type) [Field K] (j : Fin Tag.F4.rank) (c : K) :
    CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily Tag.F4) (-Pi.single j 1) c =
      yE Tag.F4 K j c := by
  rw [CFSG.LieType.Steinberg.Adjoint.xPar_neg_simple]
  exact Subtype.ext ((rootOperatorFamily Tag.F4).eltUnit_neg_simple j c)

theorem embE6F4_xE_one (K : Type) [Field K] (c : K) :
    embE6F4 K (xE Tag.F4 K 1 c) = xE Tag.E6 K (e6Index 3) c := by
  apply Subtype.ext
  rw [coe_embE6F4_xE]
  simp only [f4OrbitXUnit, orbitWord_F4_node1, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

theorem embE6F4_yE_one (K : Type) [Field K] (c : K) :
    embE6F4 K (yE Tag.F4 K 1 c) = yE Tag.E6 K (e6Index 3) c := by
  apply Subtype.ext
  rw [coe_embE6F4_yE]
  simp only [f4OrbitYUnit, orbitWord_F4_node1, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

end Lifts

section Frame


theorem rootPairF4_foldr (K : Type) [Field K] (ω : List (Fin Tag.F4.rank))
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) :
    IsRoot .F4 (ω.foldr (reflect .F4) γ) ∧ rootPairF4 K (ω.foldr (reflect .F4) γ) =
      (rootPairF4 K γ).map (MulAut.conj (ω.map (weylElement Tag.F4 K)).prod).toMonoidHom := by
  induction ω with
  | nil =>
    refine ⟨hγ, ?_⟩
    have h1 : (MulAut.conj (([] : List (Fin Tag.F4.rank)).map
        (weylElement Tag.F4 K)).prod).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      simp only [List.map_nil, List.prod_nil, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        one_mul, inv_one, mul_one, MonoidHom.id_apply]
    rw [List.foldr_nil, h1, Subgroup.map_id]
  | cons i ω ih =>
    obtain ⟨hr, he⟩ := ih
    refine ⟨IsRoot.reflect i hr, ?_⟩
    have hhom : (MulAut.conj (weylElement Tag.F4 K i)).toMonoidHom.comp
        (MulAut.conj (ω.map (weylElement Tag.F4 K)).prod).toMonoidHom =
        (MulAut.conj ((i :: ω).map (weylElement Tag.F4 K)).prod).toMonoidHom := by
      refine MonoidHom.ext fun z => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        List.map_cons, List.prod_cons]
      group
    rw [List.foldr_cons, show rootPairF4 K (reflect .F4 i (ω.foldr (reflect .F4) γ)) =
        (rootPairF4 K (ω.foldr (reflect .F4) γ)).map
          (MulAut.conj (weylElement Tag.F4 K i)).toMonoidHom from
        (map_conj_weylElement_rootPair_F4 i hr).symm, he, Subgroup.map_map, hhom]

end Frame

section Main


theorem commute_embE6F4_rootPair_one (K : Type) [Field K] {s : adjointGroup .E6 K}
    {b : Fin Tag.E6.rank → Kˣ} (hs : (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 b)
    (hb : b (e6Index 3) = 1) {y : adjointGroup .F4 K}
    (hy : y ∈ rootPairF4 K (Pi.single (1 : Fin Tag.F4.rank) 1)) :
    Commute (embE6F4 K y) s := by
  have hx : ∀ c : K, xE Tag.E6 K (e6Index 3) c * s = s * xE Tag.E6 K (e6Index 3) c := by
    intro c
    have h := conj_xE_of_coe hs (e6Index 3) c
    rw [hb, Units.val_one, one_mul] at h
    calc xE Tag.E6 K (e6Index 3) c * s = s * xE Tag.E6 K (e6Index 3) c * s⁻¹ * s := by rw [h]
      _ = s * xE Tag.E6 K (e6Index 3) c := by group
  have hy' : ∀ c : K, yE Tag.E6 K (e6Index 3) c * s = s * yE Tag.E6 K (e6Index 3) c := by
    intro c
    have h := conj_yE_of_coe hs (e6Index 3) c
    rw [hb, inv_one, Units.val_one, one_mul] at h
    calc yE Tag.E6 K (e6Index 3) c * s = s * yE Tag.E6 K (e6Index 3) c * s⁻¹ * s := by rw [h]
      _ = s * yE Tag.E6 K (e6Index 3) c := by group
  suffices h : rootPairF4 K (Pi.single (1 : Fin Tag.F4.rank) 1) ≤
      (Subgroup.centralizer {s}).comap (embE6F4 K) from
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (h hy))
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
      (F := rootOperatorFamily Tag.F4) (isRoot_single Tag.F4 1) g).1 hg
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, xPar_single_F4,
      embE6F4_xE_one]
    exact hx c
  · intro g hg
    obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
      (F := rootOperatorFamily Tag.F4) (isRoot_neg_single Tag.F4 1) g).1 hg
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, xPar_neg_single_F4,
      embE6F4_yE_one]
    exact hy' c

theorem commute_diag_of_conj (K : Type) [Field K] {P : adjointGroup .F4 K}
    {ω : List (Fin Tag.E6.rank)}
    (hN : ((embE6F4 K P : adjointGroup .E6 K) : ModGL Tag.E6 K) = weylWord K ω)
    {y : adjointGroup .F4 K} (hy : y ∈ rootPairF4 K (Pi.single (1 : Fin Tag.F4.rank) 1))
    {s : adjointGroup .E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hs : (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 a)
    (ha : rootChar a (ω.foldr (reflect Tag.E6) (Pi.single (e6Index 3) 1)) = 1) :
    Commute (embE6F4 K (P * y * P⁻¹)) s := by
  have hc : Commute (embE6F4 K y) ((embE6F4 K P)⁻¹ * s * embE6F4 K P) := by
    refine commute_embE6F4_rootPair_one K
      (b := weylAct ((coxeterSystem Tag.E6).wordProd ω)⁻¹ a) ?_ ?_ hy
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hN, hs]
      exact weylWord_inv_conj_rootDiagUnit ω a
    · show rootChar a (((coxeterSystem Tag.E6).wordProd ω)⁻¹⁻¹ •
        (Pi.single (e6Index 3) 1 : Fin Tag.E6.rank → ℤ)) = 1
      rw [inv_inv, coxeterWordProd_smul_foldr]
      exact ha
  rw [map_mul, map_mul, map_inv]
  exact commute_conjBy_of_commute hc

theorem commute_anti_of_mem_f4FrameGroup (K : Type) [Field K] {x : adjointGroup .F4 K}
    (hx : x ∈ f4FrameGroup K) (u : Kˣ) :
    Commute (embE6F4 K x) (e6AntiA K u) ∧ Commute (embE6F4 K x) (e6AntiB K u) := by
  suffices h : f4FrameGroup K ≤
      (Subgroup.centralizer (Set.range (e6AntiA K) ∪ Set.range (e6AntiB K))).comap
        (embE6F4 K) by
    have hm := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 (h hx))
    exact ⟨(hm _ (Or.inl ⟨u, rfl⟩)).symm, (hm _ (Or.inr ⟨u, rfl⟩)).symm⟩
  refine iSup_le fun i => ?_
  rw [f4Frame_eq_foldr i, (rootPairF4_foldr K (frameWordF4 i) (isRoot_single _ _)).2,
    Subgroup.map_le_iff_le_comap]
  intro y hy
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hN := coe_embE6F4_weylProd K (frameWordF4 i)
  rintro s (⟨v, rfl⟩ | ⟨v, rfl⟩)
  · exact (commute_diag_of_conj K hN hy (coe_e6AntiA K v)
      (by rw [rootChar_antiCharA, frame_antiA_vanish i, zpow_zero])).symm
  · exact (commute_diag_of_conj K hN hy (coe_e6AntiB K v)
      (by rw [rootChar_antiCharB, frame_antiB_vanish i, zpow_zero])).symm

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
