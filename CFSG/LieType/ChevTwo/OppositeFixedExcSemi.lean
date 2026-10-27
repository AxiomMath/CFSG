module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLift

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def fieldAutHom : RingAut K →* MulAut (ModGL τ K) where
  toFun σ := exactEntrywiseAut τ σ
  map_one' := MulEquiv.ext fun g => Units.ext (by
    change entrywise ((1 : RingAut K) : K →+* K) _ = _
    exact entrywise_id _)
  map_mul' σ σ' := MulEquiv.ext fun g => Units.ext (by
    change entrywise ((σ * σ' : RingAut K) : K →+* K) _ =
      entrywise (σ : K →+* K) (entrywise (σ' : K →+* K) _)
    rw [entrywise_entrywise]
    rfl)

variable (τ K) in
abbrev GamL : Type := ModGL τ K ⋊[fieldAutHom τ K] RingAut K

theorem fieldAutHom_apply (σ : RingAut K) (g : ModGL τ K) :
    fieldAutHom τ K σ g = Units.map (entrywiseHom (σ : K →+* K)) g := rfl

@[expose] noncomputable def vtw (σ : RingAut K) (x : RootModule τ K) : RootModule τ K :=
  Finsupp.mapRange (σ : K → K) (map_zero σ) x

theorem vtw_apply (σ : RingAut K) (x : RootModule τ K) (b : Label τ) :
    vtw σ x b = σ (x b) := rfl

theorem vtw_add (σ : RingAut K) (x y : RootModule τ K) :
    vtw σ (x + y) = vtw σ x + vtw σ y := by
  ext b; simp [vtw_apply]

theorem vtw_zero (σ : RingAut K) : vtw σ (0 : RootModule τ K) = 0 := by
  ext b; simp [vtw_apply]

theorem vtw_one (x : RootModule τ K) : vtw (1 : RingAut K) x = x := by
  ext b; simp [vtw_apply]

theorem vtw_mul (σ σ' : RingAut K) (x : RootModule τ K) :
    vtw (σ * σ') x = vtw σ (vtw σ' x) := by
  ext b; simp [vtw_apply]

theorem vtw_apply_end (σ : RingAut K) (A : Module.End K (RootModule τ K)) (x : RootModule τ K) :
    vtw σ (A x) = entrywise (σ : K →+* K) A (vtw σ x) :=
  (entrywise_apply_mapRange (σ : K →+* K) A x).symm

noncomputable instance : MulAction (GamL τ K) (RootModule τ K) where
  smul s x := (s.left : Module.End K (RootModule τ K)) (vtw s.right x)
  one_smul x := by
    change ((1 : GamL τ K).left : Module.End K (RootModule τ K)) (vtw (1 : GamL τ K).right x) = x
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, vtw_one]
    rfl
  mul_smul s t x := by
    change ((s * t).left : Module.End K (RootModule τ K)) (vtw (s * t).right x) =
      (s.left : Module.End K (RootModule τ K)) (vtw s.right
        ((t.left : Module.End K (RootModule τ K)) (vtw t.right x)))
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, vtw_mul, vtw_apply_end,
      Units.val_mul, Module.End.mul_apply]
    rfl

theorem smul_def (s : GamL τ K) (x : RootModule τ K) :
    s • x = (s.left : Module.End K (RootModule τ K)) (vtw s.right x) := rfl

theorem smul_add' (s : GamL τ K) (x y : RootModule τ K) : s • (x + y) = s • x + s • y := by
  rw [smul_def, smul_def, smul_def, vtw_add, map_add]

theorem smul_zero' (s : GamL τ K) : s • (0 : RootModule τ K) = 0 := by
  rw [smul_def, vtw_zero, map_zero]

theorem smul_sum' {ι : Type*} (s : GamL τ K) (t : Finset ι) (f : ι → RootModule τ K) :
    s • (∑ i ∈ t, f i) = ∑ i ∈ t, s • f i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [smul_zero']
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, smul_add', ih]

variable (τ K) in
@[expose] noncomputable def conjAct : GamL τ K →* MulAut (ModGL τ K) where
  toFun s := MulAut.conj s.left * fieldAutHom τ K s.right
  map_one' := by
    refine MulEquiv.ext fun g => ?_
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, MulAut.mul_apply,
      MulAut.one_apply, MulAut.conj_apply, inv_one, one_mul, mul_one]
  map_mul' s t := by
    refine MulEquiv.ext fun g => ?_
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, MulAut.mul_apply,
      MulAut.conj_apply, map_inv, mul_inv_rev, mul_assoc]

theorem conjAct_apply (s : GamL τ K) (g : ModGL τ K) :
    conjAct τ K s g = s.left * Units.map (entrywiseHom (s.right : K →+* K)) g * s.left⁻¹ := by
  change (MulAut.conj s.left * fieldAutHom τ K s.right) g = _
  rw [MulAut.mul_apply, MulAut.conj_apply]
  rfl

@[expose] noncomputable def trK (z : K) : K :=
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  algebraMap (ZMod (ringChar K)) K (Algebra.trace (ZMod (ringChar K)) K z)

theorem trK_add (x y : K) : trK (x + y) = trK x + trK y := by
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  simp only [trK, map_add]

theorem trK_zero : trK (0 : K) = 0 := by
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  simp only [trK, map_zero]

@[expose] noncomputable def trKHom : K →+ K where
  toFun := trK
  map_zero' := trK_zero
  map_add' := trK_add

theorem trK_ringAut (σ : RingAut K) (z : K) : trK (σ z) = trK z := by
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  have e : (σ.toRingHom.comp (algebraMap (ZMod (ringChar K)) K)) =
      algebraMap (ZMod (ringChar K)) K := RingHom.ext_zmod _ _
  let e' : K ≃ₐ[ZMod (ringChar K)] K :=
    AlgEquiv.ofRingEquiv (f := σ) (fun x => congrArg (fun f => f x) e)
  have h := Algebra.trace_eq_of_algEquiv e' z
  simp only [trK]
  exact congrArg _ h

theorem exists_trK_ne_zero [Finite K] {a : K} (ha : a ≠ 0) : ∃ b : K, trK (a * b) ≠ 0 := by
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate K ha
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  refine ⟨b, fun h => hb ?_⟩
  exact (algebraMap (ZMod (ringChar K)) K).injective (by simpa [trK] using h)

section Cert

theorem fieldAut_mem_levelRadical (σ : RingAut K) {J : Set (Fin τ.rank)} {d : ℤ} {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K J d) : fieldAutHom τ K σ u ∈ levelRadical τ K J d :=
  entrywise_mem_rootSpan (σ := σ) hu

theorem conjAct_mem_levelRadical {s : GamL τ K} {J : Set (Fin τ.rank)}
    (hs : s.left ∈ parabolicLevi τ K J) {d : ℤ} (hd : 1 ≤ d) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K J d) : conjAct τ K s u ∈ levelRadical τ K J d := by
  rw [conjAct_apply]
  exact (Subgroup.mem_normalizer_iff.1 (parabolicLevi_le_normalizer J hd hs) _).1
    (fieldAut_mem_levelRadical s.right hu)

theorem vtw_mem_graded (σ : RingAut K) {J : Set (Fin τ.rank)} {d : ℤ} {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J d) : vtw σ x ∈ parabolicGraded τ K J d := by
  rw [parabolicGraded_eq_supported] at hx ⊢
  rw [Finsupp.mem_supported K] at hx ⊢
  exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans hx

theorem smul_mem_graded {s : GamL τ K} {J : Set (Fin τ.rank)}
    (hs : s.left ∈ parabolicLevi τ K J) (d : ℤ) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J d) : s • x ∈ parabolicGraded τ K J d :=
  parabolicLevi_preserves hs d (vtw_mem_graded s.right hx)

@[expose] noncomputable def phiLayer (σ : RingAut K) (J : Set (Fin τ.rank)) (n : ℕ) :
    Layer τ K J n →* Layer τ K J n :=
  QuotientGroup.map _ _
    (((fieldAutHom τ K σ).toMonoidHom.comp (levelRadical τ K J (n + 1)).subtype).codRestrict
      (levelRadical τ K J (n + 1)) (fun u => fieldAut_mem_levelRadical σ u.2))
    (fun u hu => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact fieldAut_mem_levelRadical σ (Subgroup.mem_subgroupOf.1 hu))

theorem phiLayer_mk (σ : RingAut K) (J : Set (Fin τ.rank)) (n : ℕ)
    (u : levelRadical τ K J (n + 1)) :
    phiLayer σ J n (QuotientGroup.mk u) = QuotientGroup.mk
      (⟨fieldAutHom τ K σ u, fieldAut_mem_levelRadical σ u.2⟩ : levelRadical τ K J (n + 1)) :=
  rfl

theorem layerMap_vtw (σ : RingAut K) (J : Set (Fin τ.rank)) (n : ℕ) (x : RootModule τ K) :
    layerMap J n (vtw σ x) = phiLayer σ J n (layerMap J n x) := by
  classical
  unfold layerMap
  rw [map_prod]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [vtw_apply]
  unfold layerFactor
  split_ifs with h
  · exact congrArg QuotientGroup.mk (Subtype.ext (Units.ext
      (entrywise_pinnedX (σ : K →+* K) β.1 (x (Sum.inr β))).symm))
  · rw [map_one]

theorem layerMap_smul (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    (J : Set (Fin τ.rank)) (n : ℕ) {s : GamL τ K} (hs : s.left ∈ parabolicLevi τ K J)
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1))
    {u : ModGL τ K} (hu : u ∈ levelRadical τ K J (n + 1))
    (hxu : layerMap J n x = QuotientGroup.mk (⟨u, hu⟩ : levelRadical τ K J (n + 1))) :
    layerMap J n (s • x) = QuotientGroup.mk (⟨conjAct τ K s u,
      conjAct_mem_levelRadical hs (one_le_succ n) hu⟩ : levelRadical τ K J (n + 1)) := by
  rw [smul_def, layerMap_parabolicLevi hτ h2 J n hs (vtw_mem_graded s.right hx), layerMap_vtw,
    hxu, phiLayer_mk, levelConj_mk]
  congr 1

theorem exists_fixed_vector_semi [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, s.left ∈ parabolicLevi τ K J) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K J (n + 1)) (hu' : u ∉ levelRadical τ K J (n + 1 + 1))
    (hfix : ∀ s ∈ S, conjAct τ K s u = u) :
    ∃ x ∈ parabolicGraded τ K J (n + 1), x ≠ 0 ∧ ∀ s ∈ S, s • x = x := by
  obtain ⟨x, hx, hxu⟩ := exists_layerMap_eq J n
    ((⟨u, hu⟩ : levelRadical τ K J (n + 1)) : Layer τ K J n)
  refine ⟨x, hx, fun h0 => ?_, fun s hs => ?_⟩
  · rw [h0, layerMap_zero] at hxu
    exact hu' (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hxu.symm))
  · refine layerMap_injOn J n (smul_mem_graded (hS s hs) _ hx) hx ?_
    rw [layerMap_smul hτ h2 J n (hS s hs) hx hu hxu, hxu]
    congr 1
    exact Subtype.ext (hfix s hs)

theorem exists_invariant_coset_semi [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, s.left ∈ parabolicLevi τ K J) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0) (hfix : ∀ s ∈ S, s • x = x) :
    ∃ u ∈ levelRadical τ K J (n + 1), u ∉ levelRadical τ K J (n + 1 + 1) ∧
      ∀ s ∈ S, u⁻¹ * conjAct τ K s u ∈ levelRadical τ K J (n + 1 + 1) := by
  obtain ⟨⟨u, hu⟩, hux⟩ := QuotientGroup.mk_surjective (layerMap J n x)
  refine ⟨u, hu, fun hu' => hx0 ?_, fun s hs => ?_⟩
  · refine layerMap_injOn J n hx (Submodule.zero_mem _) ?_
    rw [layerMap_zero, ← hux]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu')
  · have h1 := layerMap_smul hτ h2 J n (hS s hs) hx hu hux.symm
    rw [hfix s hs, ← hux] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3

theorem rootPairing_vtw (σ : RingAut K) (x y : RootModule τ K) :
    rootPairing τ K (vtw σ x) (vtw σ y) = σ (rootPairing τ K x y) := by
  rw [rootPairing_apply, rootPairing_apply, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, vtw_apply, vtw_apply]

theorem pairing_smul (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    (J : Set (Fin τ.rank)) (n : ℕ) {s : GamL τ K} (hs : s.left ∈ parabolicLevi τ K J)
    {x y : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1))
    (hy : y ∈ parabolicGraded τ K J (-(n + 1))) :
    trK (rootPairing τ K (s • x) (s • y)) = trK (rootPairing τ K x y) := by
  rw [smul_def, smul_def, rootPairing_parabolicLevi hτ h2 J n hs (vtw_mem_graded _ hx)
    (vtw_mem_graded _ hy), rootPairing_vtw, trK_ringAut]

theorem exists_fixed_neg_semi [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, s.left ∈ parabolicLevi τ K J) (hodd : Odd (Nat.card S))
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0)
    (hfix : ∀ s ∈ S, s • x = x) :
    ∃ y ∈ parabolicGraded τ K J (-(n + 1)), y ≠ 0 ∧ ∀ s ∈ S, s • y = y := by
  classical
  have : Finite S := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne'
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Finsupp.ext h)
  have hbL : b ∈ gradedLabels τ J (n + 1) := by
    have hx' := hx
    rw [parabolicGraded_eq_supported] at hx'
    exact (Finsupp.mem_supported K x).1 hx' (Finsupp.mem_support_iff.2 hb)
  obtain ⟨α, hα, hbeq⟩ := mem_layerRoots_of_mem_gradedLabels hbL
  have hαr : IsRoot τ α := hα.1
  have hb' : x (Sum.inr ⟨α, hαr⟩) ≠ 0 := by rw [hbeq] at hb; exact hb
  obtain ⟨c, hc⟩ := exists_trK_ne_zero hb'
  have hy₀ : c • rootVec τ K (-α) ∈ parabolicGraded τ K J (-(n + 1)) :=
    Submodule.smul_mem _ _ (rootVec_mem_parabolicGraded (IsRoot.neg hαr)
      (by rw [parabolicDegree_neg, hα.2.2]))
  set y₀ : RootModule τ K := c • rootVec τ K (-α) with hy₀def
  set y : RootModule τ K := ∑ s : S, (s : GamL τ K) • y₀ with hy
  have hyG : y ∈ parabolicGraded τ K J (-(n + 1)) :=
    Submodule.sum_mem _ fun s _ => smul_mem_graded (hS s s.2) _ hy₀
  have hpr : rootPairing τ K x (rootVec τ K (-α)) = x (Sum.inr ⟨α, hαr⟩) :=
    rootPairing_rootVec_neg hαr x
  have hterm : ∀ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) =
      trK (x (Sum.inr ⟨α, hαr⟩) * c) := fun s => by
    conv_lhs => rw [← hfix s s.2]
    rw [pairing_smul hτ h2 J n (hS s s.2) hx hy₀, hy₀def, map_smul, hpr, smul_eq_mul, mul_comm]
  have hsum : rootPairing τ K x y = ∑ s : S, rootPairing τ K x ((s : GamL τ K) • y₀) := by
    rw [hy, map_sum]
  have htr : trK (rootPairing τ K x y) =
      ∑ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) := by
    rw [hsum]
    exact map_sum trKHom _ Finset.univ
  have hpair : trK (rootPairing τ K x y) = trK (x (Sum.inr ⟨α, hαr⟩) * c) := by
    rw [htr, Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card, natCast_eq_one_of_odd h2 hodd, one_mul]
  refine ⟨y, hyG, fun h0 => hc ?_, fun s hs => ?_⟩
  · rw [← hpair, h0, map_zero, trK_zero]
  · rw [hy, smul_sum']
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨s, hs⟩ : S)) _ _ fun t => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_smul]

theorem conjAct_inl (n : ModGL τ K) :
    conjAct τ K (SemidirectProduct.inl n) = MulAut.conj n := by
  change MulAut.conj (SemidirectProduct.inl n : GamL τ K).left *
    fieldAutHom τ K (SemidirectProduct.inl n : GamL τ K).right = _
  rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]

theorem inl_conj_left (n : ModGL τ K) (hn : ∀ σ : RingAut K, fieldAutHom τ K σ n = n)
    (s : GamL τ K) :
    ((SemidirectProduct.inl n : GamL τ K) * s * (SemidirectProduct.inl n)⁻¹).left =
      n * s.left * n⁻¹ := by
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_inv, one_mul, map_one, MulAut.one_apply, hn]

@[expose] noncomputable def actSub (B : Subgroup (GamL τ K)) (H : Subgroup (ModGL τ K))
    (hH : ∀ b ∈ B, ∀ x ∈ H, conjAct τ K b x ∈ H) : MulDistribMulAction B H :=
  { smul := fun b x => ⟨conjAct τ K b x, hH b b.2 x x.2⟩
    one_smul := fun x => Subtype.ext (by
      change conjAct τ K ((1 : B) : GamL τ K) x = x
      rw [Subgroup.coe_one, map_one]; rfl)
    mul_smul := fun a b x => Subtype.ext (by
      change conjAct τ K ((a * b : B) : GamL τ K) x = conjAct τ K a (conjAct τ K b x)
      rw [Subgroup.coe_mul, map_mul]; rfl)
    smul_mul := fun a x y => Subtype.ext (by
      change conjAct τ K a ((x * y : H) : ModGL τ K) = conjAct τ K a x * conjAct τ K a y
      rw [Subgroup.coe_mul, map_mul])
    smul_one := fun a => Subtype.ext (by
      change conjAct τ K a ((1 : H) : ModGL τ K) = 1
      rw [Subgroup.coe_one, map_one]) }

theorem exists_fixed_mem_oppRadical_semi [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {J : Set (Fin τ.rank)}
    {S : Subgroup (GamL τ K)} (hS : ∀ s ∈ S, s.left ∈ parabolicLevi τ K J)
    (hodd : Odd (Nat.card S)) {u : ModGL τ K} (hu : u ∈ parabolicRadical τ K J) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, conjAct τ K s u = u) :
    ∃ v ∈ oppRadical τ K J, v ≠ 1 ∧ ∀ s ∈ S, conjAct τ K s v = v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨n, hun, hun'⟩ := exists_level hu hu1
  obtain ⟨x, hx, hx0, hxS⟩ := exists_fixed_vector_semi hτ h2 J n hS hun hun' hfix
  obtain ⟨y, hy, hy0, hyS⟩ := exists_fixed_neg_semi hτ h2 J n hS hodd hx hx0 hxS
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := exists_longest τ
  set n₀ := canonicalRep (coxeterSystem τ) K w₀ with hn₀
  have hn₀σ : ∀ σ : RingAut K, fieldAutHom τ K σ n₀ = n₀ := fun σ =>
    entrywise_canonicalRep σ w₀
  set c₀ : GamL τ K := SemidirectProduct.inl n₀ with hc₀
  set S' : Subgroup (GamL τ K) := S.map (MulAut.conj c₀).toMonoidHom with hS'
  have hS'M : ∀ s' ∈ S', s'.left ∈ parabolicLevi τ K (δ '' J) := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc₀, inl_conj_left n₀ hn₀σ]
    exact map_conj_parabolicLevi_le hδ J (Subgroup.mem_map.2 ⟨s.left, hS s hs, rfl⟩)
  have hodd' : Odd (Nat.card S') := by
    rwa [hS', Subgroup.card_map_of_injective (MulAut.conj c₀).injective]
  have hx' : (n₀ : Module.End K (RootModule τ K)) y ∈
      parabolicGraded τ K (δ '' J) (n + 1) :=
    longest_mem_parabolicGraded hinj hδ J (n + 1) hy
  have hx'0 : (n₀ : Module.End K (RootModule τ K)) y ≠ 0 := fun h => hy0 (by
    rw [← units_inv_apply_apply n₀ y, h, map_zero])
  have hc₀y : c₀ • y = (n₀ : Module.End K (RootModule τ K)) y := by
    rw [smul_def, hc₀, SemidirectProduct.left_inl, SemidirectProduct.right_inl, vtw_one]
  have hx'S : ∀ s' ∈ S', s' • ((n₀ : Module.End K (RootModule τ K)) y) =
      (n₀ : Module.End K (RootModule τ K)) y := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc₀y, ← mul_smul, inv_mul_cancel_right, mul_smul, hyS s hs]
  obtain ⟨u', hu', hu'', hcos⟩ :=
    exists_invariant_coset_semi hτ h2 (δ '' J) n hS'M hx' hx'0 hx'S
  have hN1 : ∀ b ∈ S', ∀ z ∈ levelRadical τ K (δ '' J) (n + 1),
      conjAct τ K b z ∈ levelRadical τ K (δ '' J) (n + 1) := fun b hb z hz =>
    conjAct_mem_levelRadical (hS'M b hb) (one_le_succ n) hz
  have hN2 : ∀ b ∈ S', ∀ z ∈ levelRadical τ K (δ '' J) (n + 1 + 1),
      conjAct τ K b z ∈ levelRadical τ K (δ '' J) (n + 1 + 1) := fun b hb z hz =>
    conjAct_mem_levelRadical (hS'M b hb) (one_le_succ_succ n) hz
  letI : MulDistribMulAction S' (levelRadical τ K (δ '' J) (n + 1)) :=
    actSub S' _ hN1
  have hinv : CFSG.IsInvariant S' (levelRadical τ K (δ '' J) (n + 1))
      ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1))) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun a z hz => by
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact hN2 a a.2 z hz
  have hp : IsPGroup 2 ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) :=
    (isPGroup_levelRadical (δ '' J) (n + 1 + 1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (levelRadical_succ_le (δ '' J) (n + 1))).symm
  have hsolv : Group.IsSolvable ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) := by
    have := hp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card S')
      (Nat.card ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
        (levelRadical τ K (δ '' J) (n + 1)))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd')
  have : Finite S' := Nat.finite_of_card_ne_zero (by
    rintro h; rw [h] at hodd'; exact absurd hodd' (by decide))
  obtain ⟨c, hc, hcu⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1)))
    hinv hsolv hcop ⟨u', hu'⟩ fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact hcos b b.2
  have hcN : (c : ModGL τ K) ∉ levelRadical τ K (δ '' J) (n + 1 + 1) := fun h => hu'' (by
    have h' := Subgroup.mem_subgroupOf.1 hcu
    have e : u' = (c : ModGL τ K) * ((c⁻¹ * ⟨u', hu'⟩ : levelRadical τ K (δ '' J) (n + 1)) :
      ModGL τ K) := by simp
    rw [e]
    exact mul_mem h h')
  have hconjc : conjAct τ K c₀⁻¹ = MulAut.conj n₀⁻¹ := by
    rw [map_inv, hc₀, conjAct_inl, ← map_inv]
  refine ⟨n₀⁻¹ * c * n₀, ?_, fun h => hcN ?_, fun s hs => ?_⟩
  · have hcQ : (c : ModGL τ K) ∈ parabolicRadical τ K (δ '' J) :=
      levelRadical_le_parabolicRadical _ (one_le_succ n) c.2
    have := map_conj_longest_parabolicRadical_le (K := K) hinj hδ hsq h₀ J
      (Subgroup.mem_map_of_mem _ hcQ)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  · have e : (c : ModGL τ K) = n₀ * (n₀⁻¹ * c * n₀) * n₀⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel]
    exact one_mem _
  · have hcs := congrArg Subtype.val (hc ⟨c₀ * s * c₀⁻¹, ⟨s, hs, rfl⟩⟩)
    change conjAct τ K (c₀ * s * c₀⁻¹) (c : ModGL τ K) = c at hcs
    rw [map_mul, map_mul, hconjc, hc₀, conjAct_inl] at hcs
    simp only [MulAut.mul_apply, MulAut.conj_apply] at hcs
    calc conjAct τ K s (n₀⁻¹ * c * n₀) =
        n₀⁻¹ * (n₀ * conjAct τ K s (n₀⁻¹ * c * n₀) * n₀⁻¹) * n₀ := by group
      _ = n₀⁻¹ * c * n₀ := by rw [show n₀ * conjAct τ K s (n₀⁻¹ * c * n₀) * n₀⁻¹ = c from hcs]

end Cert

end CFSG.LieType.ChevTwo.Semi
