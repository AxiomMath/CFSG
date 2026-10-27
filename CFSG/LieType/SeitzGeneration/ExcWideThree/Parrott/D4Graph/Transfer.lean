module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.ClassOne
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial


variable {K : Type} [Field K]

theorem sl2At_uSL (i : Fin Tag.D4.rank) (c : K) : sl2At K i (uSL c) = adjX Tag.D4 K i c :=
  Subtype.ext (simpleRootSL2_uSL i c)

theorem sl2At_vSL (i : Fin Tag.D4.rank) (c : K) : sl2At K i (vSL c) = adjY Tag.D4 K i c :=
  Subtype.ext (simpleRootSL2_vSL i c)

theorem sl2_hom_ext {H : Type*} [Group H] {f g : SL2 K →* H} (hu : ∀ c, f (uSL c) = g (uSL c))
    (hv : ∀ c, f (vSL c) = g (vSL c)) : f = g :=
  MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun A hA => by
    rcases hA with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hu c
    · exact hv c

theorem d4Graph_sl2At (ε : ℕ) (i : Fin Tag.D4.rank) (A : SL2 K) :
    d4Graph K ε (sl2At K i A) = sl2At K ((d4Rho ^ ε) i) A := by
  have h : (d4Graph K ε).toMonoidHom.comp (sl2At K i) = sl2At K ((d4Rho ^ ε) i) := by
    refine sl2_hom_ext (fun c => ?_) fun c => ?_
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_uSL,
        d4Graph_adjX]
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_vSL,
        d4Graph_adjY]
  exact DFunLike.congr_fun h A

theorem outer_orth (i j : Fin Tag.D4.rank) (hi : i ≠ ⟨2, by decide⟩) (hj : j ≠ ⟨2, by decide⟩)
    (hij : i ≠ j) :
    iform (Pi.single i 1 : Fin Tag.D4.rank → ℤ) (Pi.single j 1) = 0 ∧
      ¬IsRoot Tag.D4 ((Pi.single i 1 : Fin Tag.D4.rank → ℤ) + Pi.single j 1) ∧
      ¬IsRoot Tag.D4 ((Pi.single i 1 : Fin Tag.D4.rank → ℤ) - Pi.single j 1) := by
  rw [isRoot_iff_mem_artifactRoots, isRoot_iff_mem_artifactRoots]
  revert i j
  decide

theorem sl2At_commute {i j : Fin Tag.D4.rank} (hi : i ≠ ⟨2, by decide⟩) (hj : j ≠ ⟨2, by decide⟩)
    (hij : i ≠ j) (A B : SL2 K) : Commute (sl2At K i A) (sl2At K j B) := by
  obtain ⟨h0, hp, hm⟩ := outer_orth i j hi hj hij
  have h := CFSG.RankThree.Chevalley.rootSL2_commute_of_orth (K := K) (isRoot_single Tag.D4 i)
    (isRoot_single Tag.D4 j) h0 hp hm A B
  rw [CFSG.RankThree.Chevalley.rootSL2_single_apply,
    CFSG.RankThree.Chevalley.rootSL2_single_apply] at h
  exact Subtype.ext h.eq

variable (K) in
@[expose] noncomputable def sl2Short : SL2 K →* ↥(adjointGroup Tag.D4 K) where
  toFun A := sl2At K ⟨0, by decide⟩ A * sl2At K ⟨1, by decide⟩ A * sl2At K ⟨3, by decide⟩ A
  map_one' := by simp
  map_mul' A B := by
    have h01 := sl2At_commute (K := K) (i := ⟨1, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
      (by decide) (by decide) A B
    have h03 := sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
      (by decide) (by decide) A B
    have h13 := sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨1, by decide⟩) (by decide)
      (by decide) (by decide) A B
    simp only [map_mul]
    set a0 := sl2At K ⟨0, by decide⟩ A
    set a1 := sl2At K ⟨1, by decide⟩ A
    set a3 := sl2At K ⟨3, by decide⟩ A
    set b0 := sl2At K ⟨0, by decide⟩ B
    set b1 := sl2At K ⟨1, by decide⟩ B
    set b3 := sl2At K ⟨3, by decide⟩ B
    have h01' : Commute a1 b0 := h01
    have h03' : Commute a3 b0 := h03
    have h13' : Commute a3 b1 := h13
    calc a0 * b0 * (a1 * b1) * (a3 * b3) = a0 * (b0 * a1) * b1 * a3 * b3 := by group
      _ = a0 * (a1 * b0) * b1 * a3 * b3 := by rw [h01'.eq]
      _ = a0 * a1 * b0 * (b1 * a3) * b3 := by group
      _ = a0 * a1 * b0 * (a3 * b1) * b3 := by rw [h13'.eq]
      _ = a0 * a1 * (b0 * a3) * b1 * b3 := by group
      _ = a0 * a1 * (a3 * b0) * b1 * b3 := by rw [h03'.eq]
      _ = a0 * a1 * a3 * (b0 * b1 * b3) := by group

theorem sl2Short_apply (A : SL2 K) :
    sl2Short K A =
      sl2At K ⟨0, by decide⟩ A * sl2At K ⟨1, by decide⟩ A * sl2At K ⟨3, by decide⟩ A :=
  rfl

theorem d4Graph_one_sl2Two (A : SL2 K) :
    d4Graph K 1 (sl2At K ⟨2, by decide⟩ A) = sl2At K ⟨2, by decide⟩ A := by
  rw [d4Graph_sl2At]
  rfl

theorem d4Graph_one_sl2Short (A : SL2 K) : d4Graph K 1 (sl2Short K A) = sl2Short K A := by
  rw [sl2Short_apply, map_mul, map_mul, d4Graph_sl2At, d4Graph_sl2At, d4Graph_sl2At]
  have e0 : (d4Rho ^ 1) (⟨0, by decide⟩ : Fin Tag.D4.rank) = ⟨1, by decide⟩ := by decide
  have e1 : (d4Rho ^ 1) (⟨1, by decide⟩ : Fin Tag.D4.rank) = ⟨3, by decide⟩ := by decide
  have e3 : (d4Rho ^ 1) (⟨3, by decide⟩ : Fin Tag.D4.rank) = ⟨0, by decide⟩ := by decide
  rw [e0, e1, e3]
  have h03 := sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
    (by decide) (by decide) A A
  have h13 := sl2At_commute (K := K) (i := ⟨1, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
    (by decide) (by decide) A A
  rw [mul_assoc, h03.eq, ← mul_assoc, h13.eq]

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

variable [Finite K]

@[expose] noncomputable def sl2TwoFix : SL2 K →* ↥(fixSubgroup (d4Graph K 1)) :=
  (sl2At K ⟨2, by decide⟩).codRestrict _ fun A => mem_fixSubgroup.2 (d4Graph_one_sl2Two A)

@[expose] noncomputable def sl2ShortFix : SL2 K →* ↥(fixSubgroup (d4Graph K 1)) :=
  (sl2Short K).codRestrict _ fun A => mem_fixSubgroup.2 (d4Graph_one_sl2Short A)

theorem coe_fixSubgroupEquivG2 (hK3 : 3 ≤ Nat.card K) (y : ↥(fixSubgroup (d4Graph K 1))) :
    ((fixSubgroupEquivG2 K hK3 y : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      d4FixedToG2 K ⟨y.1.1, mem_fixSubgroup_d4Graph_one_iff.1 y.2⟩ :=
  rfl

theorem xUnit_two_eq_g2OrbitXUnit (c : K) :
    xUnit Tag.D4 K ⟨2, by decide⟩ c = g2OrbitXUnit K ⟨0, by decide⟩ c := by
  show _ = [xUnit Tag.D4 K ⟨2, by decide⟩ c].prod
  rw [List.prod_singleton]

theorem yUnit_two_eq_g2OrbitYUnit (c : K) :
    yUnit Tag.D4 K ⟨2, by decide⟩ c = g2OrbitYUnit K ⟨0, by decide⟩ c := by
  show _ = [yUnit Tag.D4 K ⟨2, by decide⟩ c].prod
  rw [List.prod_singleton]

theorem xUnit_short_eq_g2OrbitXUnit (c : K) :
    xUnit Tag.D4 K ⟨0, by decide⟩ c * xUnit Tag.D4 K ⟨1, by decide⟩ c *
      xUnit Tag.D4 K ⟨3, by decide⟩ c = g2OrbitXUnit K ⟨1, by decide⟩ c := by
  show _ = [xUnit Tag.D4 K ⟨0, by decide⟩ c, xUnit Tag.D4 K ⟨1, by decide⟩ c,
    xUnit Tag.D4 K ⟨3, by decide⟩ c].prod
  simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem yUnit_short_eq_g2OrbitYUnit (c : K) :
    yUnit Tag.D4 K ⟨0, by decide⟩ c * yUnit Tag.D4 K ⟨1, by decide⟩ c *
      yUnit Tag.D4 K ⟨3, by decide⟩ c = g2OrbitYUnit K ⟨1, by decide⟩ c := by
  show _ = [yUnit Tag.D4 K ⟨0, by decide⟩ c, yUnit Tag.D4 K ⟨1, by decide⟩ c,
    yUnit Tag.D4 K ⟨3, by decide⟩ c].prod
  simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem fixSubgroupEquivG2_sl2Two (hK3 : 3 ≤ Nat.card K) (A : SL2 K) :
    ((fixSubgroupEquivG2 K hK3 (sl2TwoFix A) : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      simpleRootSL2 Tag.G2 K ⟨0, by decide⟩ A := by
  set ρ : SL2 K →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp
    ((fixSubgroupEquivG2 K hK3).toMonoidHom.comp sl2TwoFix)
  have hρ : ρ = simpleRootSL2 Tag.G2 K ⟨0, by decide⟩ := by
    refine eq_simpleRootSL2 _ (fun c => ?_) fun c => ?_
    · show ((fixSubgroupEquivG2 K hK3 (sl2TwoFix (uSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2, ← d4FixedToG2_g2OrbitXUnitAll]
      congr 1
      exact Subtype.ext ((congrArg Subtype.val (sl2At_uSL (K := K) ⟨2, by decide⟩ c)).trans
        (xUnit_two_eq_g2OrbitXUnit c))
    · show ((fixSubgroupEquivG2 K hK3 (sl2TwoFix (vSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2, ← d4FixedToG2_g2OrbitYUnitAll]
      congr 1
      exact Subtype.ext ((congrArg Subtype.val (sl2At_vSL (K := K) ⟨2, by decide⟩ c)).trans
        (yUnit_two_eq_g2OrbitYUnit c))
  exact DFunLike.congr_fun hρ A

theorem fixSubgroupEquivG2_sl2Short (hK3 : 3 ≤ Nat.card K) (A : SL2 K) :
    ((fixSubgroupEquivG2 K hK3 (sl2ShortFix A) : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      simpleRootSL2 Tag.G2 K ⟨1, by decide⟩ A := by
  set ρ : SL2 K →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp
    ((fixSubgroupEquivG2 K hK3).toMonoidHom.comp sl2ShortFix)
  have hρ : ρ = simpleRootSL2 Tag.G2 K ⟨1, by decide⟩ := by
    refine eq_simpleRootSL2 _ (fun c => ?_) fun c => ?_
    · show ((fixSubgroupEquivG2 K hK3 (sl2ShortFix (uSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2, ← d4FixedToG2_g2OrbitXUnitAll]
      congr 1
      refine Subtype.ext ?_
      show ((sl2Short K (uSL c) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = _
      rw [sl2Short_apply, sl2At_uSL, sl2At_uSL, sl2At_uSL]
      exact xUnit_short_eq_g2OrbitXUnit c
    · show ((fixSubgroupEquivG2 K hK3 (sl2ShortFix (vSL c)) : adjointGroup Tag.G2 K) :
        ModGL Tag.G2 K) = _
      rw [coe_fixSubgroupEquivG2, ← d4FixedToG2_g2OrbitYUnitAll]
      congr 1
      refine Subtype.ext ?_
      show ((sl2Short K (vSL c) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = _
      rw [sl2Short_apply, sl2At_vSL, sl2At_vSL, sl2At_vSL]
      exact yUnit_short_eq_g2OrbitYUnit c
  exact DFunLike.congr_fun hρ A

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
