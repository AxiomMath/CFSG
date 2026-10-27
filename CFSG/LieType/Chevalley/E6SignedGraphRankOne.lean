module

public import CFSG.LieType.Chevalley.E6SignedGraphRankOneMaps

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix CFSG.LieType.Steinberg.Adjoint

variable (K : Type) [Field K]

@[expose] def orbitFixed
    (O : Finset E6Vec) : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootSpan TwistTag.E6.tag K (O : Set E6Vec) ⊓ fixedGroup K

@[expose] def orbitImage
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    Finset E6Vec :=
  (TwistTag.E6.orbit a).image fun i => w • (Pi.single i 1 : E6Vec)

variable {K}

theorem orbit_pair_or_single (a : Fin TwistTag.E6.foldedTag.rank) :
    (TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a ∧
      TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)} ∧
      TwistTag.E6.orbitWord a =
        [TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)]) ∨
    (TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a ∧
      TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a} ∧
      TwistTag.E6.orbitWord a = [TwistTag.E6.orbitMin a]) := by
  fin_cases a <;> decide

theorem perm_perm (i : Fin TwistTag.E6.tag.rank) : TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  revert i
  decide

theorem orbitXProd_pair
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i, j]) (γ : Fin TwistTag.E6.tag.rank → K) :
    orbitXProd TwistTag.E6 a γ =
      xUnit TwistTag.E6.tag K i (γ i) * xUnit TwistTag.E6.tag K j (γ j) := by
  simp [orbitXProd, h]

theorem orbitXProd_single
    {a : Fin TwistTag.E6.foldedTag.rank} {i : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i]) (γ : Fin TwistTag.E6.tag.rank → K) :
    orbitXProd TwistTag.E6 a γ = xUnit TwistTag.E6.tag K i (γ i) := by
  simp [orbitXProd, h]

abbrev simpleSet (a : Fin TwistTag.E6.foldedTag.rank) : Set E6Vec :=
  (fun i => (Pi.single i 1 : E6Vec)) '' ↑(TwistTag.E6.orbit a)

theorem exists_eq_pair
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i, j]) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (simpleSet a)) :
    ∃ c d : K, u = xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K j d := by
  obtain ⟨γ, rfl⟩ := exists_orbitXProd_eq TwistTag.E6 hu
  exact ⟨γ i, γ j, orbitXProd_pair h γ⟩

theorem exists_eq_single
    {a : Fin TwistTag.E6.foldedTag.rank} {i : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i]) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (simpleSet a)) :
    ∃ c : K, u = xUnit TwistTag.E6.tag K i c := by
  obtain ⟨γ, rfl⟩ := exists_orbitXProd_eq TwistTag.E6 hu
  exact ⟨γ i, orbitXProd_single h γ⟩

theorem pair_eq_pair
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i, j]) (hij : i ≠ j) {c d c' d' : K}
    (e : xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K j d =
      xUnit TwistTag.E6.tag K i c' * xUnit TwistTag.E6.tag K j d') : c = c' ∧ d = d' := by
  have hi : i ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  have hj : j ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  set γ : Fin TwistTag.E6.tag.rank → K := fun k => if k = i then c else d
  set γ' : Fin TwistTag.E6.tag.rank → K := fun k => if k = i then c' else d'
  have hγ : orbitXProd TwistTag.E6 a γ =
      xUnit TwistTag.E6.tag K i c * xUnit TwistTag.E6.tag K j d := by
    rw [orbitXProd_pair h]
    simp [γ, Ne.symm hij]
  have hγ' : orbitXProd TwistTag.E6 a γ' =
      xUnit TwistTag.E6.tag K i c' * xUnit TwistTag.E6.tag K j d' := by
    rw [orbitXProd_pair h]
    simp [γ', Ne.symm hij]
  have key := eq_of_orbitXProd_eq TwistTag.E6 (hγ.trans (e.trans hγ'.symm))
  have h1 := key i hi
  have h2 := key j hj
  simp [γ, γ', Ne.symm hij] at h1 h2
  exact ⟨h1, h2⟩

theorem xUnit_inj
    {i : Fin TwistTag.E6.tag.rank} {c c' : K}
    (e : xUnit TwistTag.E6.tag K i c = xUnit TwistTag.E6.tag K i c') : c = c' := by
  rw [← pinnedX_single, ← pinnedX_single] at e
  exact pinnedX_injective TwistTag.E6.tag K _ e

theorem yUnit_inj
    {i : Fin TwistTag.E6.tag.rank} {c c' : K}
    (e : yUnit TwistTag.E6.tag K i c = yUnit TwistTag.E6.tag K i c') : c = c' := by
  rw [← pinnedX_neg_single, ← pinnedX_neg_single] at e
  exact pinnedX_injective TwistTag.E6.tag K _ e

abbrev negSimpleSet (a : Fin TwistTag.E6.foldedTag.rank) : Set E6Vec :=
  (fun i => -(Pi.single i 1 : E6Vec)) '' ↑(TwistTag.E6.orbit a)

theorem simpleSet_isRoot (a : Fin TwistTag.E6.foldedTag.rank) :
    ∀ α ∈ simpleSet a, IsRoot TwistTag.E6.tag α := by
  rintro _ ⟨i, -, rfl⟩
  exact isRoot_single _ i

theorem negSimpleSet_isRoot (a : Fin TwistTag.E6.foldedTag.rank) :
    ∀ α ∈ negSimpleSet a, IsRoot TwistTag.E6.tag α := by
  rintro _ ⟨i, -, rfl⟩
  exact isRoot_neg_single _ i

theorem rootSpan_negSimpleSet
    (a : Fin TwistTag.E6.foldedTag.rank) :
    rootSpan TwistTag.E6.tag K (negSimpleSet a) =
      (rootSpan TwistTag.E6.tag K (simpleSet a)).map (MulAut.conj
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K
          (TwistTag.E6.orbitReflection a))).toMonoidHom := by
  rw [(canonical_weyl_root_transport TwistTag.E6.tag K).1 _ _ (simpleSet_isRoot a), Set.image_image]
  congr 1
  exact (image_orbitReflection_smul_single TwistTag.E6 a).symm

theorem canonicalRep_orbitReflection_conj_xUnit
    {a : Fin TwistTag.E6.foldedTag.rank}
    {k : Fin TwistTag.E6.tag.rank} (hk : k ∈ TwistTag.E6.orbit a) (d : K) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) *
        xUnit TwistTag.E6.tag K k d *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a))⁻¹ =
      yUnit TwistTag.E6.tag K k (-d) := by
  rw [canonicalRep_orbitReflection TwistTag.E6 a]
  exact list_prod_weylElt_conj_xUnit TwistTag.E6 (TwistTag.E6.orbitWord a)
    (TwistTag.E6.nodup_orbitWord a) (fun l hl => (TwistTag.E6.mem_orbitWord).1 hl)
    ((TwistTag.E6.mem_orbitWord).2 hk) d

theorem exists_eq_neg_pair
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i, j]) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (negSimpleSet a)) :
    ∃ c d : K, u = yUnit TwistTag.E6.tag K i c * yUnit TwistTag.E6.tag K j d := by
  have hi : i ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  have hj : j ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  rw [rootSpan_negSimpleSet] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := exists_eq_pair h hv
  refine ⟨-c, -d, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show ∀ p x y : ModGL TwistTag.E6.tag K, p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹)
    from fun p x y => by group, canonicalRep_orbitReflection_conj_xUnit hi,
    canonicalRep_orbitReflection_conj_xUnit hj]

theorem exists_eq_neg_single
    {a : Fin TwistTag.E6.foldedTag.rank} {i : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i]) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ rootSpan TwistTag.E6.tag K (negSimpleSet a)) :
    ∃ c : K, u = yUnit TwistTag.E6.tag K i c := by
  have hi : i ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  rw [rootSpan_negSimpleSet] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := exists_eq_single h hv
  exact ⟨-c, canonicalRep_orbitReflection_conj_xUnit hi c⟩

theorem neg_pair_eq_neg_pair
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.orbitWord a = [i, j]) (hij : i ≠ j) {c d c' d' : K}
    (e : yUnit TwistTag.E6.tag K i c * yUnit TwistTag.E6.tag K j d =
      yUnit TwistTag.E6.tag K i c' * yUnit TwistTag.E6.tag K j d') : c = c' ∧ d = d' := by
  have hi : i ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  have hj : j ∈ TwistTag.E6.orbit a := (TwistTag.E6.mem_orbitWord).1 (by rw [h]; simp)
  set N := canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a)
  have hconj : ∀ x y : K, yUnit TwistTag.E6.tag K i x * yUnit TwistTag.E6.tag K j y =
      N * (xUnit TwistTag.E6.tag K i (-x) * xUnit TwistTag.E6.tag K j (-y)) * N⁻¹ := fun x y => by
    rw [show N * (xUnit TwistTag.E6.tag K i (-x) * xUnit TwistTag.E6.tag K j (-y)) * N⁻¹ =
      (N * xUnit TwistTag.E6.tag K i (-x) * N⁻¹) * (N * xUnit TwistTag.E6.tag K j (-y) * N⁻¹)
        by group, canonicalRep_orbitReflection_conj_xUnit hi,
      canonicalRep_orbitReflection_conj_xUnit hj, neg_neg, neg_neg]
  rw [hconj, hconj] at e
  have e' := pair_eq_pair h hij (mul_left_cancel (mul_right_cancel e))
  exact ⟨neg_injective e'.1, neg_injective e'.2⟩

theorem coe_orbitImage
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    ((orbitImage w a : Finset E6Vec) : Set E6Vec) = (fun α => w • α) '' simpleSet a := by
  rw [orbitImage, Finset.coe_image, Set.image_image]

theorem coe_neg_orbitImage
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    (((orbitImage w a).image fun α => -α : Finset E6Vec) : Set E6Vec) =
      (fun α => w • α) '' negSimpleSet a := by
  rw [Finset.coe_image, coe_orbitImage]
  unfold simpleSet negSimpleSet
  rw [Set.image_image, Set.image_image, Set.image_image]
  exact Set.image_congr fun i _ => (smul_neg w _).symm

theorem rootSpan_orbitImage
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    rootSpan TwistTag.E6.tag K (orbitImage w a : Set E6Vec) =
      (rootSpan TwistTag.E6.tag K (simpleSet a)).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)).toMonoidHom := by
  rw [(canonical_weyl_root_transport TwistTag.E6.tag K).1 _ _ (simpleSet_isRoot a), coe_orbitImage]

theorem rootSpan_neg_orbitImage
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    rootSpan TwistTag.E6.tag K (((orbitImage w a).image fun α => -α : Finset E6Vec) : Set E6Vec) =
      (rootSpan TwistTag.E6.tag K (negSimpleSet a)).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)).toMonoidHom := by
  rw [(canonical_weyl_root_transport TwistTag.E6.tag K).1 _ _ (negSimpleSet_isRoot a),
    coe_neg_orbitImage]

theorem twistA_conj_canonicalRep_xUnit
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (k : Fin TwistTag.E6.tag.rank) (c : K) :
    twistA K * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * xUnit TwistTag.E6.tag K k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * (twistA K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          xUnit TwistTag.E6.tag K (TwistTag.E6.perm k)
            ((rootChar (signTuple K) (w • (Pi.single k 1 : E6Vec)) : K) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  have h := twistA_conj_canonicalRep_simpleRootSL2 hw k (uSL c)
  rwa [simpleRootSL2_uSL, diagConj_uSL, simpleRootSL2_uSL] at h

theorem twistA_conj_canonicalRep_yUnit
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (k : Fin TwistTag.E6.tag.rank) (c : K) :
    twistA K * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * yUnit TwistTag.E6.tag K k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) * (twistA K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          yUnit TwistTag.E6.tag K (TwistTag.E6.perm k)
            ((rootChar (signTuple K) (w • (Pi.single k 1 : E6Vec)) : K) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  have h := twistA_conj_canonicalRep_simpleRootSL2 hw k (vSL c)
  rwa [simpleRootSL2_vSL, diagConj_vSL, simpleRootSL2_vSL, rootChar_signTuple_inv] at h

theorem conj_mul {G : Type*} [Group G] (p x y : G) :
    p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by
  group

theorem conj_conj_mul {G : Type*} [Group G] (q p x y : G) :
    q * (p * (x * y) * p⁻¹) * q⁻¹ = (q * (p * x * p⁻¹) * q⁻¹) * (q * (p * y * p⁻¹) * q⁻¹) := by
  group

theorem conj_twistA_eq_of_mem {g : ModGL TwistTag.E6.tag K} (h : g ∈ fixedGroup K) :
    twistA K * g * (twistA K)⁻¹ = g :=
  mul_inv_eq_iff_eq_mul.2 (mem_fixedGroup.1 h).2.symm

theorem simpleRootSL2_nSL
    (k : Fin TwistTag.E6.tag.rank) (t : Kˣ) :
    simpleRootSL2 TwistTag.E6.tag K k (nSL t) = weylElt TwistTag.E6.tag K k t := by
  rw [nSL_eq_HSL_mul, map_mul, simpleRootSL2_HSL, simpleRootSL2_WSL,
    torusElt_mul_weylElt_one]

theorem orbitSL2_uSL_pair
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (c : K) :
    orbitSL2 K w a (uSL c) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      (xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c *
        xUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          ((orbitSign K w a : K) * c)) * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_ne h, diagConj_uSL, simpleRootSL2_uSL, simpleRootSL2_uSL]

theorem orbitSL2_uSL_single
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) (c : K) :
    orbitSL2 K w a (uSL c) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_eq h, simpleRootSL2_uSL]

theorem orbitSign_inv
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    (orbitSign K w a)⁻¹ = orbitSign K w a :=
  inv_eq_of_mul_eq_one_right (orbitSign_mul_self w a)

theorem orbitSL2_vSL_pair
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (c : K) :
    orbitSL2 K w a (vSL c) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      (yUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c *
        yUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          ((orbitSign K w a : K) * c)) * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_ne h, diagConj_vSL, simpleRootSL2_vSL, simpleRootSL2_vSL,
    orbitSign_inv]

theorem orbitSL2_vSL_single
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) (c : K) :
    orbitSL2 K w a (vSL c) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      yUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_eq h, simpleRootSL2_vSL]

theorem rootChar_smul_orbitMin_perm
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (a : Fin TwistTag.E6.foldedTag.rank) :
    rootChar (signTuple K) (w • (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 : E6Vec)) =
      orbitSign K w a := by
  rw [rootChar_smul_single_perm hw, orbitSign_eq_rootChar]

theorem orbitSign_eq_one_iff
    (hK : ringChar K ≠ 2) (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitSign K w a = 1 ↔ Even ((w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec))
      ⟨1, by decide⟩) := by
  rw [orbitSign]
  rcases Int.even_or_odd ((w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) ⟨1, by decide⟩)
    with he | ho
  · exact iff_of_true he.neg_one_zpow he
  · refine iff_of_false ?_ (Int.not_even_iff_odd.2 ho)
    rw [ho.neg_one_zpow]
    intro h1
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h1)

theorem orbitFixed_orbitImage_upper
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hs : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a →
      orbitSign K w a = 1) :
    Function.Injective (fun c => orbitSL2 K w a (uSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (uSL c)) = orbitFixed K (orbitImage w a) := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
  set i := TwistTag.E6.orbitMin a
  have hmem : ∀ c : K, orbitSL2 K w a (uSL c) ∈ orbitFixed K (orbitImage w a) := fun c => by
    refine Subgroup.mem_inf.2 ⟨?_, orbitSL2_mem_fixedGroup hw hs _⟩
    rw [rootSpan_orbitImage, orbitSL2_apply]
    refine Subgroup.mem_map.2 ⟨orbitBase K (orbitSign K w a) a (uSL c), ?_, rfl⟩
    have hx : ∀ (k : Fin TwistTag.E6.tag.rank), k ∈ TwistTag.E6.orbit a → ∀ d : K,
        xUnit TwistTag.E6.tag K k d ∈ rootSpan TwistTag.E6.tag K (simpleSet a) := fun k hk d => by
      rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan (S := simpleSet a) ⟨k, hk, rfl⟩ d
    by_cases h : TwistTag.E6.perm i = i
    · rw [orbitBase_of_eq h, simpleRootSL2_uSL]
      exact hx _ (TwistTag.E6.orbitMin_mem a) c
    · rw [orbitBase_of_ne h, diagConj_uSL, simpleRootSL2_uSL, simpleRootSL2_uSL]
      exact mul_mem (hx _ (TwistTag.E6.orbitMin_mem a) c)
        (hx _ (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a)) _)
  rcases orbit_pair_or_single a with ⟨h, -, hword⟩ | ⟨h, -, hword⟩
  ·
    refine ⟨fun c c' e => ?_, Set.Subset.antisymm ?_ fun g hg => ?_⟩
    · simp only [orbitSL2_uSL_pair w h] at e
      exact (pair_eq_pair hword (Ne.symm h) (mul_left_cancel (mul_right_cancel e))).1
    · rintro _ ⟨c, rfl⟩
      exact hmem c
    · obtain ⟨hU, hΓ⟩ := Subgroup.mem_inf.1 hg
      rw [rootSpan_orbitImage] at hU
      obtain ⟨u, hu, rfl⟩ := hU
      obtain ⟨c, d, rfl⟩ := exists_eq_pair hword hu
      have hfix := conj_twistA_eq_of_mem hΓ
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
      have hA : twistA K * (n * (xUnit TwistTag.E6.tag K i c *
          xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) d) * n⁻¹) * (twistA K)⁻¹ =
            n * (xUnit TwistTag.E6.tag K i ((orbitSign K w a : K) * d) *
              xUnit TwistTag.E6.tag K (TwistTag.E6.perm i) ((orbitSign K w a : K) * c)) * n⁻¹ := by
        rw [conj_conj_mul, twistA_conj_canonicalRep_xUnit hw,
          twistA_conj_canonicalRep_xUnit hw, perm_perm, rootChar_smul_orbitMin_perm hw,
          ← orbitSign_eq_rootChar, ← conj_mul,
          (commute_xUnit_xUnit K (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a))
            (TwistTag.E6.orbitMin_mem a) _ _).eq]
      have hfix' := hfix.symm
      rw [hA] at hfix'
      have e := (pair_eq_pair hword (Ne.symm h) (mul_left_cancel (mul_right_cancel hfix'))).2
      refine ⟨c, ?_⟩
      simp only [orbitSL2_uSL_pair w h]
      rw [← e]
  ·
    refine ⟨fun c c' e => ?_, Set.Subset.antisymm ?_ fun g hg => ?_⟩
    · simp only [orbitSL2_uSL_single w h] at e
      exact xUnit_inj (mul_left_cancel (mul_right_cancel e))
    · rintro _ ⟨c, rfl⟩
      exact hmem c
    · obtain ⟨hU, -⟩ := Subgroup.mem_inf.1 hg
      rw [rootSpan_orbitImage] at hU
      obtain ⟨u, hu, rfl⟩ := hU
      obtain ⟨c, rfl⟩ := exists_eq_single hword hu
      exact ⟨c, orbitSL2_uSL_single w h c⟩

theorem orbitFixed_orbitImage_lower
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hs : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a →
      orbitSign K w a = 1) :
    Function.Injective (fun c => orbitSL2 K w a (vSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (vSL c)) =
        orbitFixed K ((orbitImage w a).image fun α => -α) := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
  set i := TwistTag.E6.orbitMin a
  have hmem : ∀ c : K, orbitSL2 K w a (vSL c) ∈
      orbitFixed K ((orbitImage w a).image fun α => -α) := fun c => by
    refine Subgroup.mem_inf.2 ⟨?_, orbitSL2_mem_fixedGroup hw hs _⟩
    rw [rootSpan_neg_orbitImage, orbitSL2_apply]
    refine Subgroup.mem_map.2 ⟨orbitBase K (orbitSign K w a) a (vSL c), ?_, rfl⟩
    have hy : ∀ (k : Fin TwistTag.E6.tag.rank), k ∈ TwistTag.E6.orbit a → ∀ d : K,
        yUnit TwistTag.E6.tag K k d ∈ rootSpan TwistTag.E6.tag K (negSimpleSet a) :=
      fun k hk d => by
      rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan (S := negSimpleSet a) ⟨k, hk, rfl⟩ d
    by_cases h : TwistTag.E6.perm i = i
    · rw [orbitBase_of_eq h, simpleRootSL2_vSL]
      exact hy _ (TwistTag.E6.orbitMin_mem a) c
    · rw [orbitBase_of_ne h, diagConj_vSL, simpleRootSL2_vSL, simpleRootSL2_vSL]
      exact mul_mem (hy _ (TwistTag.E6.orbitMin_mem a) c)
        (hy _ (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a)) _)
  rcases orbit_pair_or_single a with ⟨h, -, hword⟩ | ⟨h, -, hword⟩
  · refine ⟨fun c c' e => ?_, Set.Subset.antisymm ?_ fun g hg => ?_⟩
    · simp only [orbitSL2_vSL_pair w h] at e
      exact (neg_pair_eq_neg_pair hword (Ne.symm h) (mul_left_cancel (mul_right_cancel e))).1
    · rintro _ ⟨c, rfl⟩
      exact hmem c
    · obtain ⟨hU, hΓ⟩ := Subgroup.mem_inf.1 hg
      rw [rootSpan_neg_orbitImage] at hU
      obtain ⟨u, hu, rfl⟩ := hU
      obtain ⟨c, d, rfl⟩ := exists_eq_neg_pair hword hu
      have hfix := conj_twistA_eq_of_mem hΓ
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
      have hA : twistA K * (n * (yUnit TwistTag.E6.tag K i c *
          yUnit TwistTag.E6.tag K (TwistTag.E6.perm i) d) * n⁻¹) * (twistA K)⁻¹ =
            n * (yUnit TwistTag.E6.tag K i ((orbitSign K w a : K) * d) *
              yUnit TwistTag.E6.tag K (TwistTag.E6.perm i) ((orbitSign K w a : K) * c)) * n⁻¹ := by
        rw [conj_conj_mul, twistA_conj_canonicalRep_yUnit hw,
          twistA_conj_canonicalRep_yUnit hw, perm_perm, rootChar_smul_orbitMin_perm hw,
          ← orbitSign_eq_rootChar, ← conj_mul,
          (commute_yUnit_yUnit K (TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a))
            (TwistTag.E6.orbitMin_mem a) h _ _).eq]
      have hfix' := hfix.symm
      rw [hA] at hfix'
      have e := (neg_pair_eq_neg_pair hword (Ne.symm h)
        (mul_left_cancel (mul_right_cancel hfix'))).2
      refine ⟨c, ?_⟩
      simp only [orbitSL2_vSL_pair w h]
      rw [← e]
  · refine ⟨fun c c' e => ?_, Set.Subset.antisymm ?_ fun g hg => ?_⟩
    · simp only [orbitSL2_vSL_single w h] at e
      exact yUnit_inj (mul_left_cancel (mul_right_cancel e))
    · rintro _ ⟨c, rfl⟩
      exact hmem c
    · obtain ⟨hU, -⟩ := Subgroup.mem_inf.1 hg
      rw [rootSpan_neg_orbitImage] at hU
      obtain ⟨u, hu, rfl⟩ := hU
      obtain ⟨c, rfl⟩ := exists_eq_neg_single hword hu
      exact ⟨c, orbitSL2_vSL_single w h c⟩

theorem orbitFixed_orbitImage_eq_bot
    (hK : ringChar K ≠ 2) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a)
    (hs : orbitSign K w a ≠ 1) : orbitFixed K (orbitImage w a) = ⊥ := by
  have hneg : orbitSign K w a = -1 := by
    rw [orbitSign] at hs ⊢
    rcases Int.even_or_odd ((w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec))
      ⟨1, by decide⟩) with he | ho
    · exact absurd he.neg_one_zpow hs
    · exact ho.neg_one_zpow
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hU, hΓ⟩ := Subgroup.mem_inf.1 hg
  rcases orbit_pair_or_single a with ⟨h', -, -⟩ | ⟨-, -, hword⟩
  · exact absurd h h'
  rw [rootSpan_orbitImage] at hU
  obtain ⟨u, hu, rfl⟩ := hU
  obtain ⟨c, rfl⟩ := exists_eq_single hword hu
  have hfix := conj_twistA_eq_of_mem hΓ
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
  rw [twistA_conj_canonicalRep_xUnit hw, h, ← orbitSign_eq_rootChar, hneg] at hfix
  have e := xUnit_inj (mul_left_cancel (mul_right_cancel hfix))
  have hc : c = 0 := by
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have : (2 : K) * c = 0 := by
      rw [Units.val_neg, Units.val_one] at e
      linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [hc, xUnit_zero, mul_one, mul_inv_cancel]
  exact Subgroup.mem_bot.2 rfl

end CFSG.LieType.Chevalley.E6SignedGraph
