module

public import CFSG.LieType.Chevalley.E6SignedGraphFixed
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.E6SignedGraphRoots

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix

variable (K : Type) [Field K]

variable {K} in
@[expose] def diagConjFun (s : Kˣ) (M : SL2 K) : SL2 K :=
  ⟨!![(M : Matrix (Fin 2) (Fin 2) K) 0 0, (s : K) * (M : Matrix (Fin 2) (Fin 2) K) 0 1;
      ((s⁻¹ : Kˣ) : K) * (M : Matrix (Fin 2) (Fin 2) K) 1 0, (M : Matrix (Fin 2) (Fin 2) K) 1 1], by
    rw [det_fin_two_of]
    have h := det_SL2 M
    have hs : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := Units.mul_inv s
    linear_combination h - (M : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 * hs⟩

section DiagConjFun

variable {K}

theorem diagConjFun_00 (s : Kˣ) (M : SL2 K) :
    ((diagConjFun s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (M : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl

theorem diagConjFun_01 (s : Kˣ) (M : SL2 K) :
    ((diagConjFun s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (s : K) * (M : Matrix (Fin 2) (Fin 2) K) 0 1 := rfl

theorem diagConjFun_10 (s : Kˣ) (M : SL2 K) :
    ((diagConjFun s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((s⁻¹ : Kˣ) : K) * (M : Matrix (Fin 2) (Fin 2) K) 1 0 := rfl

theorem diagConjFun_11 (s : Kˣ) (M : SL2 K) :
    ((diagConjFun s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 := rfl

theorem SL2_mul_apply (M N : SL2 K) (i j : Fin 2) :
    ((M * N : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      (M : Matrix (Fin 2) (Fin 2) K) i 0 * (N : Matrix (Fin 2) (Fin 2) K) 0 j +
        (M : Matrix (Fin 2) (Fin 2) K) i 1 * (N : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

end DiagConjFun

@[expose] def diagConj (s : Kˣ) : SL2 K →* SL2 K where
  toFun := diagConjFun s
  map_one' := SL2_ext (by rw [diagConjFun_00]) (by rw [diagConjFun_01]; simp)
    (by rw [diagConjFun_10]; simp) (by rw [diagConjFun_11])
  map_mul' M N := by
    have hs : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := Units.mul_inv s
    refine SL2_ext ?_ ?_ ?_ ?_
    · rw [diagConjFun_00, SL2_mul_apply, SL2_mul_apply, diagConjFun_00, diagConjFun_00,
        diagConjFun_01, diagConjFun_10]
      linear_combination -((M : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (N : Matrix (Fin 2) (Fin 2) K) 1 0) * hs
    · rw [diagConjFun_01, SL2_mul_apply, SL2_mul_apply, diagConjFun_00, diagConjFun_01,
        diagConjFun_01, diagConjFun_11]
      ring
    · rw [diagConjFun_10, SL2_mul_apply, SL2_mul_apply, diagConjFun_10, diagConjFun_00,
        diagConjFun_11, diagConjFun_10]
      ring
    · rw [diagConjFun_11, SL2_mul_apply, SL2_mul_apply, diagConjFun_10, diagConjFun_01,
        diagConjFun_11, diagConjFun_11]
      linear_combination -((M : Matrix (Fin 2) (Fin 2) K) 1 0 *
        (N : Matrix (Fin 2) (Fin 2) K) 0 1) * hs

variable {K}

theorem diagConj_apply (s : Kˣ) (M : SL2 K) : diagConj K s M = diagConjFun s M :=
  rfl

theorem diagConj_uSL (s : Kˣ) (c : K) : diagConj K s (uSL c) = uSL ((s : K) * c) := by
  rw [diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [diagConjFun_00, diagConjFun_01, diagConjFun_10, diagConjFun_11, coe_uSL]

theorem diagConj_vSL (s : Kˣ) (c : K) : diagConj K s (vSL c) = vSL (((s⁻¹ : Kˣ) : K) * c) := by
  rw [diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [diagConjFun_00, diagConjFun_01, diagConjFun_10, diagConjFun_11, coe_vSL]

theorem diagConj_HSL (s t : Kˣ) : diagConj K s (HSL t) = HSL t := by
  rw [diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [diagConjFun_00, diagConjFun_01, diagConjFun_10, diagConjFun_11, coe_HSL]

theorem diagConj_nSL (s t : Kˣ) : diagConj K s (nSL t) = nSL (s * t) := by
  rw [diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [diagConjFun_00]
    simp [nSL]
  · rw [diagConjFun_01]
    simp [nSL]
  · rw [diagConjFun_10]
    simp [nSL, mul_comm]
  · rw [diagConjFun_11]
    simp [nSL]

theorem diagConj_diagConj {s : Kˣ} (hs : s * s = 1) (M : SL2 K) :
    diagConj K s (diagConj K s M) = M := by
  have h1 : (s : K) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
  have h2 : ((s⁻¹ : Kˣ) : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, ← mul_inv, hs, inv_one, Units.val_one]
  rw [diagConj_apply, diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [diagConjFun_00, diagConjFun_00]
  · rw [diagConjFun_01, diagConjFun_01, ← mul_assoc, h1, one_mul]
  · rw [diagConjFun_10, diagConjFun_10, ← mul_assoc, h2, one_mul]
  · rw [diagConjFun_11, diagConjFun_11]

theorem diagConj_one (M : SL2 K) : diagConj K 1 M = M := by
  rw [diagConj_apply]
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [diagConjFun_00]
  · rw [diagConjFun_01, Units.val_one, one_mul]
  · rw [diagConjFun_10, inv_one, Units.val_one, one_mul]
  · rw [diagConjFun_11]

theorem signTuple_apply_one : signTuple K ⟨1, by decide⟩ = -1 :=
  rfl

theorem rootChar_signTuple (v : E6Vec) :
    rootChar (signTuple K) v = (-1) ^ (v ⟨1, by decide⟩) := by
  have h : ∀ f : Fin TwistTag.E6.tag.rank → Kˣ, ∏ i, f i =
      f ⟨0, by decide⟩ * f ⟨1, by decide⟩ * f ⟨2, by decide⟩ * f ⟨3, by decide⟩ *
        f ⟨4, by decide⟩ * f ⟨5, by decide⟩ := fun f => Fin.prod_univ_six f
  rw [rootChar, h, signTuple_of_ne (by decide), signTuple_apply_one, signTuple_of_ne (by decide),
    signTuple_of_ne (by decide), signTuple_of_ne (by decide), signTuple_of_ne (by decide)]
  simp

theorem rootChar_signTuple_rho (v : E6Vec) :
    rootChar (signTuple K) (rho v) = rootChar (signTuple K) v := by
  rw [rootChar_signTuple, rootChar_signTuple, rho_apply_one]

theorem rootChar_signTuple_mul_self (v : E6Vec) :
    rootChar (signTuple K) v * rootChar (signTuple K) v = 1 := by
  rw [rootChar_signTuple, ← mul_zpow, neg_one_mul, neg_neg, _root_.one_zpow]

theorem rootChar_neg' (b : Fin TwistTag.E6.tag.rank → Kˣ) (v : E6Vec) :
    rootChar b (-v) = (rootChar b v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem rootChar_signTuple_inv (v : E6Vec) :
    (rootChar (signTuple K) v)⁻¹ = rootChar (signTuple K) v :=
  inv_eq_of_mul_eq_one_right (rootChar_signTuple_mul_self v)

theorem canonicalRep_conj_xUnit
    (w : WeylGroup TwistTag.E6.tag) (k : Fin TwistTag.E6.tag.rank) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w * xUnit TwistTag.E6.tag K k c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
        pinnedX TwistTag.E6.tag K (w • Pi.single k 1) (ε * c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single _ k)
  exact ⟨ε, hε, fun c => by rw [← pinnedX_single, h]⟩

theorem canonicalRep_conj_yUnit
    (w : WeylGroup TwistTag.E6.tag) (k : Fin TwistTag.E6.tag.rank) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w * yUnit TwistTag.E6.tag K k c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ =
        pinnedX TwistTag.E6.tag K (w • -Pi.single k 1) (ε * c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_neg_single _ k)
  exact ⟨ε, hε, fun c => by rw [← pinnedX_neg_single, h]⟩

theorem conjD_canonicalRep_conj_xUnit
    (w : WeylGroup TwistTag.E6.tag)
    (k : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * xUnit TwistTag.E6.tag K k c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          xUnit TwistTag.E6.tag K k ((rootChar (signTuple K) (w • Pi.single k 1) : K) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  obtain ⟨ε, -, h⟩ := canonicalRep_conj_xUnit (K := K) w k
  rw [h, h, rootDiagUnit_conj_pinnedX _ (IsRoot.smul (isRoot_single _ k) w)]
  congr 1
  ring

theorem conjD_canonicalRep_conj_yUnit
    (w : WeylGroup TwistTag.E6.tag)
    (k : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag (signTuple K) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * yUnit TwistTag.E6.tag K k c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          yUnit TwistTag.E6.tag K k ((rootChar (signTuple K) (w • Pi.single k 1) : K) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  obtain ⟨ε, -, h⟩ := canonicalRep_conj_yUnit (K := K) w k
  rw [h, h, rootDiagUnit_conj_pinnedX _ (IsRoot.smul (isRoot_neg_single _ k) w), smul_neg,
    rootChar_neg', rootChar_signTuple_inv]
  congr 1
  ring

theorem conjP_canonicalRep
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6) :
    diagramMap TwistTag.E6 K * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (diagramMap TwistTag.E6 K)⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) K w := by
  have h := congrArg (fun φ : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag K =>
    φ (canonicalRep (coxeterSystem TwistTag.E6.tag) K w))
      (conj_diagramMap_eq_twistHom TwistTag.E6 K)
  rw [twistHom_canonicalRep, (mem_relWeylTwist TwistTag.E6).1 hw] at h
  exact h

theorem conjP_canonicalRep_conj
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (g : ModGL TwistTag.E6.tag K) :
    diagramMap TwistTag.E6 K * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * g *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  calc diagramMap TwistTag.E6 K * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * g *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
        (diagramMap TwistTag.E6 K * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
            (diagramMap TwistTag.E6 K)⁻¹) *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
            (diagramMap TwistTag.E6 K * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
              (diagramMap TwistTag.E6 K)⁻¹)⁻¹ := by group
    _ = _ := by rw [conjP_canonicalRep hw]

theorem rootChar_smul_single_perm
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (k : Fin TwistTag.E6.tag.rank) :
    rootChar (signTuple K) (w • (Pi.single (TwistTag.E6.perm k) 1 : E6Vec)) =
      rootChar (signTuple K) (w • (Pi.single k 1 : E6Vec)) := by
  rw [← permLattice_single, (mem_relWeylTwist_iff_smul TwistTag.E6).1 hw]
  exact rootChar_signTuple_rho _

theorem twistA_conj (g : ModGL TwistTag.E6.tag K) :
    twistA K * g * (twistA K)⁻¹ = rootDiagUnit TwistTag.E6.tag (signTuple K) *
      (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ := by
  rw [twistA]
  group

theorem twistA_conj_canonicalRep_simpleRootSL2
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (k : Fin TwistTag.E6.tag.rank) (M : SL2 K) :
    twistA K * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        simpleRootSL2 TwistTag.E6.tag K k M *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) *
        (twistA K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm k)
            (diagConj K (rootChar (signTuple K) (w • (Pi.single k 1 : E6Vec))) M) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
  set χ := rootChar (signTuple K) (w • (Pi.single k 1 : E6Vec))
  have key := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := K))
    (f := (MulAut.conj (twistA K)).toMonoidHom.comp ((MulAut.conj n).toMonoidHom.comp
      (simpleRootSL2 TwistTag.E6.tag K k)))
    (g := (MulAut.conj n).toMonoidHom.comp ((simpleRootSL2 TwistTag.E6.tag K
      (TwistTag.E6.perm k)).comp (diagConj K χ))) fun M hM => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [twistA_conj, conjP_canonicalRep_conj hw]
    rcases hM with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change _ = n * simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm k)
        (diagConj K χ (uSL c)) * n⁻¹
      rw [diagConj_uSL]
      change rootDiagUnit TwistTag.E6.tag (signTuple K) * (n * (diagramMap TwistTag.E6 K *
        simpleRootSL2 TwistTag.E6.tag K k (uSL c) * (diagramMap TwistTag.E6 K)⁻¹) * n⁻¹) *
          (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = _
      rw [simpleRootSL2_uSL, simpleRootSL2_uSL, conjP_xUnit, conjD_canonicalRep_conj_xUnit,
        rootChar_smul_single_perm hw]
    · change _ = n * simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm k)
        (diagConj K χ (vSL c)) * n⁻¹
      rw [diagConj_vSL, rootChar_signTuple_inv]
      change rootDiagUnit TwistTag.E6.tag (signTuple K) * (n * (diagramMap TwistTag.E6 K *
        simpleRootSL2 TwistTag.E6.tag K k (vSL c) * (diagramMap TwistTag.E6 K)⁻¹) * n⁻¹) *
          (rootDiagUnit TwistTag.E6.tag (signTuple K))⁻¹ = _
      rw [simpleRootSL2_vSL, simpleRootSL2_vSL, conjP_yUnit, conjD_canonicalRep_conj_yUnit,
        rootChar_smul_single_perm hw]
  exact DFunLike.congr_fun key M

theorem commute_simpleRootSL2_perm
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (M N : SL2 K) :
    Commute (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M)
      (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) N) :=
  commute_rankOneHom (t := TwistTag.E6) (TwistTag.E6.orbitMin_mem a)
    (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a)) (Ne.symm h) M N

variable (K) in
@[expose] def orbitBase
    (s : Kˣ) (a : Fin TwistTag.E6.foldedTag.rank) :
    SL2 K →* ModGL TwistTag.E6.tag K :=
  if h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a then
    simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
  else
    (MonoidHom.noncommCoprod (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a))
      ((simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))).comp
        (diagConj K s)) fun M N => commute_simpleRootSL2_perm h M (diagConj K s N)).comp
      ((MonoidHom.id (SL2 K)).prod (MonoidHom.id (SL2 K)))

variable (K) in
@[expose] def orbitSign
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) : Kˣ :=
  (-1) ^ ((w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) ⟨1, by decide⟩)

variable (K) in
@[expose] def orbitSL2
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    SL2 K →* ModGL TwistTag.E6.tag K :=
  (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)).toMonoidHom.comp
    (orbitBase K (orbitSign K w a) a)

theorem orbitBase_of_eq
    {s : Kˣ} {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) (M : SL2 K) :
    orbitBase K s a M = simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M := by
  simp only [orbitBase, h, ↓reduceDIte]

theorem orbitBase_of_ne
    {s : Kˣ} {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (M : SL2 K) :
    orbitBase K s a M = simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M *
      simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
        (diagConj K s M) := by
  simp only [orbitBase, h, ↓reduceDIte]
  rfl

theorem orbitSL2_apply
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (M : SL2 K) :
    orbitSL2 K w a M = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      orbitBase K (orbitSign K w a) a M * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ :=
  rfl

theorem orbitSign_mul_self
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitSign K w a * orbitSign K w a = 1 := by
  rw [orbitSign, ← mul_zpow, neg_one_mul, neg_neg, _root_.one_zpow]

theorem orbitSign_eq_rootChar
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitSign K w a =
      rootChar (signTuple K) (w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) :=
  (rootChar_signTuple _).symm

theorem orbitBase_mem_adjointGroup
    (s : Kˣ) (a : Fin TwistTag.E6.foldedTag.rank) (M : SL2 K) :
    orbitBase K s a M ∈ adjointGroup TwistTag.E6.tag K := by
  by_cases h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a
  · rw [orbitBase_of_eq h]
    exact simpleRootSL2_mem_adjointGroup _ _
  · rw [orbitBase_of_ne h]
    exact mul_mem (simpleRootSL2_mem_adjointGroup _ _) (simpleRootSL2_mem_adjointGroup _ _)

theorem orbitSL2_mem_adjointGroup
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (M : SL2 K) :
    orbitSL2 K w a M ∈ adjointGroup TwistTag.E6.tag K := by
  rw [orbitSL2_apply]
  exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K w)
    (orbitBase_mem_adjointGroup _ a M)) (inv_mem (canonicalRep_mem_adjointGroup _ K w))

theorem twistA_conj_orbitSL2
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    {a : Fin TwistTag.E6.foldedTag.rank}
    (hs : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a →
      orbitSign K w a = 1) (M : SL2 K) :
    twistA K * orbitSL2 K w a M * (twistA K)⁻¹ = orbitSL2 K w a M := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
  set i := TwistTag.E6.orbitMin a
  rw [orbitSL2_apply]
  by_cases h : TwistTag.E6.perm i = i
  · rw [orbitBase_of_eq h, twistA_conj_canonicalRep_simpleRootSL2 hw, h, ← orbitSign_eq_rootChar,
      hs h, diagConj_one]
  · rw [orbitBase_of_ne h]
    have e : n * (simpleRootSL2 TwistTag.E6.tag K i M *
        simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i) (diagConj K (orbitSign K w a) M)) *
          n⁻¹ = (n * simpleRootSL2 TwistTag.E6.tag K i M * n⁻¹) *
            (n * simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i)
              (diagConj K (orbitSign K w a) M) * n⁻¹) := by group
    have hpp : TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
      have := perm_symm_symm i
      rwa [show TwistTag.E6.perm.symm = TwistTag.E6.perm by decide] at this
    rw [e, show ∀ x y : ModGL TwistTag.E6.tag K,
        twistA K * (x * y) * (twistA K)⁻¹ = (twistA K * x * (twistA K)⁻¹) *
          (twistA K * y * (twistA K)⁻¹) from fun x y => by group,
      twistA_conj_canonicalRep_simpleRootSL2 hw, twistA_conj_canonicalRep_simpleRootSL2 hw, hpp,
      rootChar_smul_single_perm hw, ← orbitSign_eq_rootChar,
      diagConj_diagConj (orbitSign_mul_self w a)]
    have hc : simpleRootSL2 TwistTag.E6.tag K i M *
        simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i) (diagConj K (orbitSign K w a) M) =
          simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i) (diagConj K (orbitSign K w a) M) *
            simpleRootSL2 TwistTag.E6.tag K i M :=
      (commute_simpleRootSL2_perm (K := K) h M (diagConj K (orbitSign K w a) M)).eq
    calc n * simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i)
            (diagConj K (orbitSign K w a) M) * n⁻¹ *
          (n * simpleRootSL2 TwistTag.E6.tag K i M * n⁻¹) =
        n * (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i)
            (diagConj K (orbitSign K w a) M) * simpleRootSL2 TwistTag.E6.tag K i M) * n⁻¹ := by
          group
      _ = n * (simpleRootSL2 TwistTag.E6.tag K i M *
            simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i)
              (diagConj K (orbitSign K w a) M)) * n⁻¹ := by rw [hc]
      _ = n * simpleRootSL2 TwistTag.E6.tag K i M * n⁻¹ *
            (n * simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i)
              (diagConj K (orbitSign K w a) M) * n⁻¹) := by group

theorem orbitSL2_mem_fixedGroup
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hs : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a →
      orbitSign K w a = 1) (M : SL2 K) : orbitSL2 K w a M ∈ fixedGroup K := by
  refine mem_fixedGroup.2 ⟨orbitSL2_mem_adjointGroup w a M, ?_⟩
  have h := twistA_conj_orbitSL2 hw hs M
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem ker_orbitSL2_le_center
    (hK : ringChar K ≠ 2) (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) : (orbitSL2 K w a).ker ≤ Subgroup.center (SL2 K) := by
  intro M hM
  rw [MonoidHom.mem_ker, orbitSL2_apply, conj_eq_one_iff] at hM
  set i := TwistTag.E6.orbitMin a
  have hinj := simpleRootSL2_injective (τ := TwistTag.E6.tag) hK i
  by_cases h : TwistTag.E6.perm i = i
  · rw [orbitBase_of_eq h] at hM
    rw [hinj (hM.trans (map_one _).symm)]
    exact one_mem _
  · rw [orbitBase_of_ne h] at hM
    have hM' : simpleRootSL2 TwistTag.E6.tag K i M =
        (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.perm i) (diagConj K (orbitSign K w a) M))⁻¹ :=
      eq_inv_of_mul_eq_one_left hM
    refine Subgroup.mem_center_iff.2 fun N => hinj ?_
    rw [map_mul, map_mul, hM', ← map_inv]
    exact ((commute_simpleRootSL2_perm (K := K) h N _).symm).eq.symm

end CFSG.LieType.Chevalley.E6SignedGraph
