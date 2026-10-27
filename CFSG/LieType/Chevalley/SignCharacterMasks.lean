module

public import CFSG.LieType.Chevalley.SignKernelStabilizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

@[expose] def maskPairing (b : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, if b j then v j else 0

theorem maskPairing_add (b : Fin τ.rank → Bool) (u v : Fin τ.rank → ℤ) :
    maskPairing b (u + v) = maskPairing b u + maskPairing b v := by
  simp only [maskPairing, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

theorem maskPairing_zero (b : Fin τ.rank → Bool) : maskPairing b 0 = 0 := by
  simp [maskPairing]

@[expose] def maskChar (b : Fin τ.rank → Bool) : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ where
  toFun v := (-1) ^ maskPairing b (Multiplicative.toAdd v)
  map_one' := by simp [maskPairing_zero]
  map_mul' u v := by simp [maskPairing_add, _root_.zpow_add]

theorem maskChar_apply (b : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) :
    maskChar b (Multiplicative.ofAdd v) = (-1) ^ maskPairing b v :=
  rfl

theorem neg_one_zpow_eq_one_iff (n : ℤ) : ((-1 : ℤˣ) ^ n = 1) ↔ Even n := by
  rw [neg_one_zpow_eq_ite]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

theorem mem_kernelRoots_maskChar {b : Fin τ.rank → Bool} {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots (maskChar b) ↔ IsRoot τ α ∧ Even (maskPairing b α) := by
  rw [kernelRoots, Set.mem_ofPred_eq, maskChar_apply, neg_one_zpow_eq_one_iff]

theorem lattice_hom_ext {G : Type*} [CommGroup G] {f g : Multiplicative (Fin τ.rank → ℤ) →* G}
    (h : ∀ j, f (Multiplicative.ofAdd (Pi.single j 1)) = g (Multiplicative.ofAdd (Pi.single j 1))) :
    f = g := by
  refine MonoidHom.ext fun v => ?_
  have hv : Multiplicative.toAdd v = ∑ j, (Multiplicative.toAdd v) j •
      (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from rfl, hv, ofAdd_sum, map_prod,
    map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [ofAdd_zsmul, map_zpow, map_zpow, h]

theorem eq_maskChar (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    χ = maskChar fun j => decide (χ (Multiplicative.ofAdd (Pi.single j 1)) = -1) := by
  refine lattice_hom_ext fun j => ?_
  rw [maskChar_apply]
  have hp : ∀ b : Fin τ.rank → Bool, maskPairing b (Pi.single j 1) = if b j then 1 else 0 := by
    intro b
    rw [maskPairing, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [hp]
  rcases Int.units_eq_one_or (χ (Multiplicative.ofAdd (Pi.single j 1))) with h | h <;>
    rw [h] <;> decide

@[expose] def maskReflect (i : Fin τ.rank) (b : Fin τ.rank → Bool) : Fin τ.rank → Bool :=
  fun j => xor (b j) (b i && decide (τ.cartan i j % 2 ≠ 0))

theorem maskPairing_zsmul_single (b : Fin τ.rank → Bool) (c : ℤ) (k : Fin τ.rank) :
    maskPairing b (c • (Pi.single k 1 : Fin τ.rank → ℤ)) = c * if b k then 1 else 0 := by
  rw [maskPairing, Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  by_cases hb : b k <;> simp [hb]

@[expose] def maskCharComp
    (b : Fin τ.rank → Bool) (w : WeylGroup τ) :
    Multiplicative (Fin τ.rank → ℤ) →* ℤˣ :=
  (maskChar b).comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom _ w))

theorem maskCharComp_apply
    (b : Fin τ.rank → Bool) (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    maskCharComp b w (Multiplicative.ofAdd v) = maskChar b (Multiplicative.ofAdd (w • v)) :=
  rfl

theorem even_mask_aux (x y : Bool) (A : ℤ) :
    Even (1 * (if (x ^^ (y && decide (A % 2 ≠ 0))) = true then (1 : ℤ) else 0)) ↔
      Even ((1 * if x = true then (1 : ℤ) else 0) + -A * if y = true then 1 else 0) := by
  rcases Int.even_or_odd A with h | h
  · have h2 : A % 2 = 0 := Int.even_iff.1 h
    cases x <;> cases y <;> simp [h2, h]
  · have h2 : A % 2 = 1 := Int.odd_iff.1 h
    cases x <;> cases y <;> simp [h2, h, Int.not_even_iff_odd]

theorem maskChar_maskReflect
    (i : Fin τ.rank) (b : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) :
    maskChar (maskReflect i b) (Multiplicative.ofAdd v) =
      maskChar b (Multiplicative.ofAdd (simple τ i • v)) := by
  rw [← maskCharComp_apply]
  refine congrArg (fun f => f (Multiplicative.ofAdd v)) (lattice_hom_ext
    (f := maskChar (maskReflect i b)) (g := maskCharComp b (simple τ i)) fun j => ?_)
  rw [maskCharComp_apply, simple_smul, maskChar_apply, maskChar_apply]
  have hs : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  have hr : reflect τ i (Pi.single j 1) = (1 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) +
      (-τ.cartan i j) • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    rw [reflect, hs, one_smul, neg_smul, ← sub_eq_add_neg]
  rw [hr, maskPairing_add, maskPairing_zsmul_single, maskPairing_zsmul_single,
    show (Pi.single j 1 : Fin τ.rank → ℤ) = (1 : ℤ) • Pi.single j 1 from (one_smul _ _).symm,
    maskPairing_zsmul_single, neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
  simp only [maskReflect]
  exact if_congr (even_mask_aux (b j) (b i) (τ.cartan i j)) rfl rfl

@[expose] def maskAct (ω : List (Fin τ.rank)) (b : Fin τ.rank → Bool) : Fin τ.rank → Bool :=
  ω.foldr maskReflect b

theorem maskChar_maskAct
    (ω : List (Fin τ.rank)) (b : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) :
    maskChar (maskAct ω b) (Multiplicative.ofAdd v) =
      maskChar b (Multiplicative.ofAdd (((coxeterSystem τ).wordProd ω)⁻¹ • v)) := by
  induction ω generalizing v with
  | nil => simp [maskAct]
  | cons i ω ih =>
    change maskChar (maskReflect i (maskAct ω b)) (Multiplicative.ofAdd v) = _
    rw [maskChar_maskReflect, ih, CoxeterSystem.wordProd_cons, _root_.mul_inv_rev, mul_smul,
      (coxeterSystem τ).inv_simple]

variable {M : Type*} [CommGroup M]

@[expose] def IsCharConj
    (χ χ' : Multiplicative (Fin τ.rank → ℤ) →* M) (t : WeylGroup τ) : Prop :=
  ∀ v : Fin τ.rank → ℤ, χ' (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (t⁻¹ • v))

variable
    {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* M} {t : WeylGroup τ}

theorem kernelRoots_iff_of_isCharConj
    (h : IsCharConj χ χ' t) {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots χ' ↔ t⁻¹ • α ∈ kernelRoots χ := by
  rw [kernelRoots, kernelRoots, Set.mem_ofPred_eq, Set.mem_ofPred_eq, h, isRoot_smul_iff]

theorem charStabilizer_iff_of_isCharConj
    (h : IsCharConj χ χ' t) {w : WeylGroup τ} :
    w ∈ charStabilizer χ' ↔ t⁻¹ * w * t ∈ charStabilizer χ := by
  rw [mem_charStabilizer, mem_charStabilizer]
  constructor
  · intro hw v
    have := hw (t • v)
    rw [h, h, inv_smul_smul] at this
    rwa [mul_smul, mul_smul]
  · intro hw v
    have := hw (t⁻¹ • v)
    rw [mul_smul, mul_smul, smul_inv_smul] at this
    rw [h, h, this]

theorem charStabilizer_eq_map
    (h : IsCharConj χ χ' t) :
    charStabilizer χ' = (charStabilizer χ).map (MulAut.conj t).toMonoidHom := by
  ext w
  rw [charStabilizer_iff_of_isCharConj h, Subgroup.mem_map]
  constructor
  · intro hw
    exact ⟨t⁻¹ * w * t, hw, by simp [mul_assoc]⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx

theorem kernelWeylGroup_eq_map
    (h : IsCharConj χ χ' t) :
    kernelWeylGroup χ' = (kernelWeylGroup χ).map (MulAut.conj t).toMonoidHom := by
  rw [kernelWeylGroup, kernelWeylGroup, MonoidHom.map_closure]
  congr 1
  ext r
  constructor
  · rintro ⟨w, i, hα, rfl⟩
    refine ⟨t⁻¹ * w * simple τ i * (t⁻¹ * w)⁻¹, ⟨t⁻¹ * w, i, ?_, rfl⟩, ?_⟩
    · rw [mul_smul]
      exact (kernelRoots_iff_of_isCharConj h).1 hα
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨_, ⟨w, i, hα, rfl⟩, rfl⟩
    refine ⟨t * w, i, ?_, ?_⟩
    · rw [kernelRoots_iff_of_isCharConj h, mul_smul, inv_smul_smul]
      exact hα
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[expose] def charStabilizerMulEquiv
    (h : IsCharConj χ χ' t) :
    charStabilizer χ ≃* charStabilizer χ' :=
  ((MulAut.conj t).subgroupMap (charStabilizer χ)).trans
    (MulEquiv.subgroupCongr (charStabilizer_eq_map h).symm)

theorem coe_charStabilizerMulEquiv
    (h : IsCharConj χ χ' t) (x : charStabilizer χ) :
    ((charStabilizerMulEquiv h x : charStabilizer χ') : WeylGroup τ) = t * x * t⁻¹ :=
  rfl

theorem map_charStabilizerMulEquiv
    (h : IsCharConj χ χ' t) :
    ((kernelWeylGroup χ).subgroupOf (charStabilizer χ)).map
        (charStabilizerMulEquiv h).toMonoidHom =
      (kernelWeylGroup χ').subgroupOf (charStabilizer χ') := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, kernelWeylGroup_eq_map h]
  constructor
  · rintro ⟨⟨y, hy⟩, hyS, hyx⟩
    rw [Subgroup.mem_subgroupOf] at hyS
    have hx' : x = t * y * t⁻¹ := by
      have := congrArg Subtype.val hyx
      rw [MulEquiv.coe_toMonoidHom, coe_charStabilizerMulEquiv] at this
      exact this.symm
    change x ∈ _
    rw [hx']
    exact ⟨y, hyS, rfl⟩
  · rintro ⟨y, hyS, hyx⟩
    have hy : y ∈ charStabilizer χ := kernelWeylGroup_le hyS
    refine ⟨⟨y, hy⟩, by rwa [Subgroup.mem_subgroupOf], Subtype.ext ?_⟩
    rw [MulEquiv.coe_toMonoidHom, coe_charStabilizerMulEquiv]
    simpa using hyx

@[expose] def quotientMulEquivOfIsCharConj
    (h : IsCharConj χ χ' t) :
    charStabilizer χ ⧸ (kernelWeylGroup χ).subgroupOf (charStabilizer χ) ≃*
      charStabilizer χ' ⧸ (kernelWeylGroup χ').subgroupOf (charStabilizer χ') :=
  QuotientGroup.congr _ _ (charStabilizerMulEquiv h) (map_charStabilizerMulEquiv h)

theorem mk_eq_mk_iff_of_isCharConj
    (h : IsCharConj χ χ' t) {α γ : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ') (hγ : γ ∈ kernelRoots χ') :
    (⟦⟨α, hα⟩⟧ : KernelComponent χ') = ⟦⟨γ, hγ⟩⟧ ↔
      (⟦⟨t⁻¹ • α, (kernelRoots_iff_of_isCharConj h).1 hα⟩⟧ : KernelComponent χ) =
        ⟦⟨t⁻¹ • γ, (kernelRoots_iff_of_isCharConj h).1 hγ⟩⟧ := by
  have hf : ∀ {x y : kernelRoots χ'}, Relation.EqvGen (fun α β : kernelRoots χ' =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
      Relation.EqvGen (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
        ⟨t⁻¹ • (x : Fin τ.rank → ℤ), (kernelRoots_iff_of_isCharConj h).1 x.2⟩
        ⟨t⁻¹ • (y : Fin τ.rank → ℤ), (kernelRoots_iff_of_isCharConj h).1 y.2⟩ := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      refine Relation.EqvGen.rel _ _ ?_
      rw [dotProduct_mulVec_eq_iform] at hr ⊢
      rwa [iform_smul]
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hg : ∀ {x y : kernelRoots χ}, Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
      Relation.EqvGen (fun α β : kernelRoots χ' =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
        ⟨t • (x : Fin τ.rank → ℤ), (kernelRoots_iff_of_isCharConj h).2 (by
          rw [inv_smul_smul]; exact x.2)⟩
        ⟨t • (y : Fin τ.rank → ℤ), (kernelRoots_iff_of_isCharConj h).2 (by
          rw [inv_smul_smul]; exact y.2)⟩ := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      refine Relation.EqvGen.rel _ _ ?_
      rw [dotProduct_mulVec_eq_iform] at hr ⊢
      rwa [iform_smul]
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  constructor
  · intro e
    exact Quotient.sound (hf (Quotient.exact e))
  · intro e
    have := hg (Quotient.exact e)
    simp only [smul_inv_smul] at this
    exact Quotient.sound this

end CFSG.LieType.Chevalley
