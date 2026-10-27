module

public import CFSG.Adapters.TauCetiExceptional.BigCellPoints
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {L : Type} [Field L]

theorem xOp_single_inl (i j : Fin τ.rank) (c : L) :
    xOp τ L i c (Finsupp.single (Sum.inl j) 1) =
      hVec τ L j + (((τ.cartan j i).natAbs : L) * c) • rootVec τ L (Pi.single i 1) := by
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem rootVec_eq_single {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ L β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  rw [rootVec, dite_eq_left hβ]

theorem xOp_rootVec_neg_single'
    (i : Fin τ.rank) (c : L) :
    xOp τ L i c (rootVec τ L (-Pi.single i 1)) =
      rootVec τ L (-Pi.single i 1) + c • hVec τ L i + c ^ 2 • rootVec τ L (Pi.single i 1) := by
  rw [rootVec_eq_single (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem xOp_eq_quadratic
    (hτ : τ ≠ .G2) (i : Fin τ.rank) (c : L) :
    xOp τ L i c = 1 + c • xCoeff τ L i 1 + c ^ 2 • xCoeff τ L i 2 := by
  have h := xOp_eq_sum_xCoeff_entryDegreeBound (R := L) τ i c
  have h0 := xOp_eq_sum_xCoeff_entryDegreeBound (R := L) τ i 0
  simp only [entryDegreeBound, hτ, ↓reduceIte, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, one_smul, pow_one] at h h0
  rw [xOp_zero] at h0
  simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h0
  rw [h, ← h0]

theorem xOp_eq_quadratic_of
    {i : Fin τ.rank} (hA3 : xCoeff τ L i 3 = 0) (c : L) :
    xOp τ L i c = 1 + c • xCoeff τ L i 1 + c ^ 2 • xCoeff τ L i 2 := by
  have h := xOp_eq_sum_xCoeff (R := L) i c
  have h0 := xOp_eq_sum_xCoeff (R := L) i 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul,
    pow_one, hA3, smul_zero, add_zero] at h h0
  rw [xOp_zero] at h0
  simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h0
  rw [h, ← h0]

theorem eq_of_conj_xUnit_of
    (h2 : (2 : L) ≠ 0) (h : ModGL τ L) {i : Fin τ.rank}
    (hA3 : xCoeff τ L i 3 = 0) (h1 : h * xUnit τ L i 1 * h⁻¹ = xUnit τ L i 1)
    (hm1 : h * xUnit τ L i (-1) * h⁻¹ = xUnit τ L i (-1)) {c d : L}
    (hcd : h * xUnit τ L i c * h⁻¹ = xUnit τ L i d) : c = d := by
  set T : Module.End L (RootModule τ L) → Module.End L (RootModule τ L) := fun A =>
    (h : Module.End L (RootModule τ L)) * A * ((h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L))
    with hT
  have hTx : ∀ e : L, T (xOp τ L i e) =
      ((h * xUnit τ L i e * h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) := fun e => by
    simp only [hT, Units.val_mul, coe_xUnit]
  have hT1 : T 1 = 1 := by simp only [hT, mul_one, Units.mul_inv]
  have hTadd : ∀ A B, T (A + B) = T A + T B := fun A B => by
    simp only [hT, mul_add, add_mul]
  have hTsmul : ∀ (e : L) A, T (e • A) = e • T A := fun e A => by
    simp only [hT, mul_smul_comm, smul_mul_assoc]
  have e1 := hTx 1
  have em1 := hTx (-1)
  rw [h1, coe_xUnit, xOp_eq_quadratic_of hA3, hTadd, hTadd, hTsmul, hTsmul, hT1] at e1
  rw [hm1, coe_xUnit, xOp_eq_quadratic_of hA3, hTadd, hTadd, hTsmul, hTsmul, hT1] at em1
  simp only [one_smul, one_pow, neg_smul, even_two, Even.neg_pow] at e1 em1
  have hA₁ : T (xCoeff τ L i 1) = xCoeff τ L i 1 := by
    have e : (2 : L) • T (xCoeff τ L i 1) = (2 : L) • xCoeff τ L i 1 := by
      rw [two_smul, two_smul]
      linear_combination (norm := abel_nf) e1 - em1
    exact smul_right_injective _ h2 e
  have hA₂ : T (xCoeff τ L i 2) = xCoeff τ L i 2 := by
    have e : (2 : L) • T (xCoeff τ L i 2) = (2 : L) • xCoeff τ L i 2 := by
      rw [two_smul, two_smul]
      linear_combination (norm := abel_nf) e1 + em1
    exact smul_right_injective _ h2 e
  have hc := hTx c
  rw [hcd, coe_xUnit, xOp_eq_quadratic_of hA3, hTadd, hTadd, hTsmul, hTsmul, hT1, hA₁, hA₂,
    ← xOp_eq_quadratic_of hA3] at hc
  have hv := congrArg (fun A : Module.End L (RootModule τ L) =>
    A (Finsupp.single (Sum.inl i) 1) (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩)) hc
  simp only [xOp_single_inl, τ.cartan_self, rootVec_eq_single (isRoot_single τ i),
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    hVec] at hv
  rw [Finsupp.single_eq_of_ne (by simp), zero_add, zero_add] at hv
  norm_num at hv
  exact hv.resolve_right h2

theorem eq_of_conj_xUnit
    (hτ : τ ≠ .G2) (h2 : (2 : L) ≠ 0) (h : ModGL τ L) (i : Fin τ.rank)
    (h1 : h * xUnit τ L i 1 * h⁻¹ = xUnit τ L i 1)
    (hm1 : h * xUnit τ L i (-1) * h⁻¹ = xUnit τ L i (-1)) {c d : L}
    (hcd : h * xUnit τ L i c * h⁻¹ = xUnit τ L i d) : c = d :=
  eq_of_conj_xUnit_of h2 h (xCoeff_three_eq_zero hτ i) h1 hm1 hcd

@[expose] def pairBound (τ : Tag) : ℕ :=
  Finset.univ.sup fun x : Label τ × Label τ × Fin τ.rank =>
    (∑ k, τ.cartan x.2.2 k * (x.1.latticeWeight k - x.2.1.latticeWeight k)).natAbs

theorem natAbs_le_pairBound (a b : Label τ) (j : Fin τ.rank) :
    (∑ k, τ.cartan j k * (a.latticeWeight k - b.latticeWeight k)).natAbs ≤ pairBound τ :=
  Finset.le_sup (f := fun x : Label τ × Label τ × Fin τ.rank =>
    (∑ k, τ.cartan x.2.2 k * (x.1.latticeWeight k - x.2.1.latticeWeight k)).natAbs)
    (Finset.mem_univ (a, b, j))

theorem exists_exp_ne {a b : Label τ} (hab : a.latticeWeight ≠ b.latticeWeight) :
    ∃ j, ∑ k, τ.cartan j k * (a.latticeWeight k - b.latticeWeight k) ≠ 0 := by
  by_contra h
  push Not at h
  apply hab
  have hv : τ.cartan.mulVec (a.latticeWeight - b.latticeWeight) = 0 := by
    ext j
    simpa [Matrix.mulVec, dotProduct] using h j
  exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (det_cartan_pos τ).ne' hv)

theorem apply_single_eq_zero_of_commute
    {h : ModGL τ L} {t : Lˣ}
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1)
    (htor : ∀ j, h * torusElt τ L j t = torusElt τ L j t * h) {a b : Label τ}
    (hab : a.latticeWeight ≠ b.latticeWeight) :
    (h : Module.End L (RootModule τ L)) (Finsupp.single b 1) a = 0 := by
  obtain ⟨j, hj⟩ := exists_exp_ne hab
  have e := congrArg (fun g : ModGL τ L =>
    (g : Module.End L (RootModule τ L)) (Finsupp.single b 1) a) (htor j)
  simp only [Units.val_mul, Module.End.mul_apply] at e
  rw [torusElt_single_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, torusElt_apply_eq] at e
  set ma := ∑ k, τ.cartan j k * a.latticeWeight k
  set mb := ∑ k, τ.cartan j k * b.latticeWeight k
  have hm : ∑ k, τ.cartan j k * (a.latticeWeight k - b.latticeWeight k) = ma - mb := by
    simp only [ma, mb, mul_sub, Finset.sum_sub_distrib]
  have hne : ((t ^ ma : Lˣ) : L) ≠ ((t ^ mb : Lˣ) : L) := by
    intro heq
    apply ht _ hj (natAbs_le_pairBound a b j)
    rw [hm, zpow_sub, Units.ext heq, mul_inv_cancel]
  have h0 : (((t ^ ma : Lˣ) : L) - ((t ^ mb : Lˣ) : L)) *
      (h : Module.End L (RootModule τ L)) (Finsupp.single b 1) a = 0 := by
    rw [sub_mul, ← e, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

theorem diagonal_of_commute
    {h : ModGL τ L} {t : Lˣ}
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1)
    (htor : ∀ j, h * torusElt τ L j t = torusElt τ L j t * h)
    (hx : ∀ i, h * xUnit τ L i 1 = xUnit τ L i 1 * h) (b : Label τ) :
    (h : Module.End L (RootModule τ L)) (Finsupp.single b 1) =
      ((h : Module.End L (RootModule τ L)) (Finsupp.single b 1) b) • Finsupp.single b 1 := by
  have hroot : ∀ (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β) (a : Label τ),
      a ≠ Sum.inr ⟨β, hβ⟩ →
        (h : Module.End L (RootModule τ L)) (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1) a = 0 := by
    intro β hβ a ha
    refine apply_single_eq_zero_of_commute ht htor fun e => ha ?_
    rcases a with k | ⟨α, hα⟩
    · exact absurd e.symm hβ.ne_zero
    · exact congrArg Sum.inr (Subtype.ext e)
  ext a
  rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hab : b = a
  · subst hab
    rw [ite_eq_left rfl, mul_one]
  rw [ite_eq_right hab, mul_zero]
  rcases b with i | ⟨β, hβ⟩
  · rcases a with k | ⟨α, hα⟩
    ·
      have hk : i ≠ k := fun e => hab (congrArg Sum.inl e)
      have e := congrArg (fun g : ModGL τ L => (g : Module.End L (RootModule τ L))
        (rootVec τ L (-Pi.single i 1)) (Sum.inl k)) (hx i)
      simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit] at e
      have hm : (h : Module.End L (RootModule τ L)) (rootVec τ L (-Pi.single i 1)) =
          ((h : Module.End L (RootModule τ L)) (rootVec τ L (-Pi.single i 1))
            (Sum.inr ⟨-Pi.single i 1, isRoot_neg_single τ i⟩)) •
              rootVec τ L (-Pi.single i 1) := by
        rw [rootVec_eq_single (isRoot_neg_single τ i)]
        ext a
        rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        split_ifs with ha
        · subst ha
          rw [mul_one]
        · rw [mul_zero]
          exact hroot _ _ a (Ne.symm ha)
      have hr1 : (h : Module.End L (RootModule τ L)) (rootVec τ L (-Pi.single i 1))
          (Sum.inl k) = 0 := by
        rw [rootVec_eq_single (isRoot_neg_single τ i)]
        exact hroot _ _ _ (by simp)
      have hr2 : (h : Module.End L (RootModule τ L)) (rootVec τ L (Pi.single i 1))
          (Sum.inl k) = 0 := by
        rw [rootVec_eq_single (isRoot_single τ i)]
        exact hroot _ _ _ (by simp)
      have hv1 : rootVec τ L (-Pi.single i 1) (Sum.inl k) = 0 := by
        rw [rootVec_eq_single (isRoot_neg_single τ i)]
        simp
      have hv2 : rootVec τ L (Pi.single i 1) (Sum.inl k) = 0 := by
        rw [rootVec_eq_single (isRoot_single τ i)]
        simp
      have hv3 : hVec τ L i (Sum.inl k) = 0 := by
        rw [hVec, Finsupp.single_apply, ite_eq_right fun e => hk (Sum.inl_injective e)]
      rw [xOp_rootVec_neg_single', one_smul, one_pow, one_smul, map_add, map_add,
        Finsupp.add_apply, Finsupp.add_apply, hr1, hr2, zero_add, add_zero, hm, map_smul,
        xOp_rootVec_neg_single', one_smul, one_pow, one_smul, Finsupp.smul_apply,
        Finsupp.add_apply, Finsupp.add_apply, hv1, hv2, hv3, add_zero, add_zero,
        smul_zero] at e
      exact e
    · exact apply_single_eq_zero_of_commute ht htor fun e => hα.ne_zero e
  · exact hroot β hβ a fun e => hab e.symm

theorem bigCellDet_ne_zero_of_diagonal (h : ModGL τ L)
    (hd : ∀ b, (h : Module.End L (RootModule τ L)) (Finsupp.single b 1) =
      ((h : Module.End L (RootModule τ L)) (Finsupp.single b 1) b) • Finsupp.single b 1) :
    bigCellDet (natMat τ L (h : Module.End L (RootModule τ L))) ≠ 0 := by
  have hdiag : ∀ i j, i ≠ j → natMat τ L (h : Module.End L (RootModule τ L)) i j = 0 := by
    intro i j hij
    rw [natMat_apply, hd, Finsupp.smul_apply, Finsupp.single_eq_of_ne, smul_zero]
    exact fun e => hij ((posEquiv τ).symm.injective e)
  have hne : ∀ i, natMat τ L (h : Module.End L (RootModule τ L)) i i ≠ 0 := by
    intro i hi
    rw [natMat_apply] at hi
    have e := hd ((posEquiv τ).symm i)
    rw [hi, zero_smul] at e
    have e' := congrArg (fun v => ((h⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) v) e
    simp only [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, map_zero] at e'
    exact Finsupp.single_ne_zero.2 one_ne_zero e'
  have hldu : IsLDU (1 : Matrix (Fin (nLab τ)) (Fin (nLab τ)) L)
      (natMat τ L (h : Module.End L (RootModule τ L))) 1 :=
    ⟨fun _ => Matrix.one_apply_eq _, fun _ _ hij => Matrix.one_apply_ne (ne_of_lt hij), hdiag,
      fun _ => Matrix.one_apply_eq _, fun _ _ hji => Matrix.one_apply_ne (ne_of_gt hji)⟩
  have e : natMat τ L (h : Module.End L (RootModule τ L)) =
      1 * natMat τ L (h : Module.End L (RootModule τ L)) * 1 := by
    rw [one_mul, mul_one]
  rw [e, bigCellDet]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [hldu.leadMinor_eq]
  exact Finset.prod_ne_zero_iff.2 fun j _ => hne j

theorem mem_adjointGroup_of_conj_entrywise_of
    [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (i₀ : Fin τ.rank) (hA3 : xCoeff τ L i₀ 3 = 0) (E : Subfield L) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) (h : ModGL τ L)
    (hz : ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    (hσ : ∀ x ∈ adjointGroup τ E, h * baseChangeGL E.subtype x * h⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x)) :
    h ∈ adjointGroup τ L := by
  have hxc : ∀ i (c : E), h * xUnit τ L i (c : L) * h⁻¹ = xUnit τ L i ((σ c : E) : L) := by
    intro i c
    have e := hσ _ (xUnit_mem_adjointGroup i c)
    have e2 : Units.map (entrywiseHom σ.toRingHom) (xUnit τ E i c) = xUnit τ E i (σ c) :=
      Units.ext (entrywise_xOp σ.toRingHom i c)
    rw [e2, baseChangeGL_xUnit, baseChangeGL_xUnit] at e
    exact e
  have hσid : ∀ c : E, σ c = c := by
    intro c
    have h1 := hxc i₀ 1
    have hm1 := hxc i₀ (-1)
    rw [map_one, OneMemClass.coe_one] at h1
    rw [map_neg, map_one, NegMemClass.coe_neg, OneMemClass.coe_one] at hm1
    exact (Subtype.ext (eq_of_conj_xUnit_of h2 h hA3 h1 hm1 (hxc i₀ c))).symm
  have hσ' : σ.toRingHom = RingHom.id E := RingHom.ext hσid
  have hfix : ∀ x ∈ adjointGroup τ E,
      h * baseChangeGL E.subtype x = baseChangeGL E.subtype x * h := by
    intro x hx
    have e := hσ x hx
    rw [hσ', show Units.map (entrywiseHom (RingHom.id E)) x = x from
      Units.ext (entrywise_id _)] at e
    exact mul_inv_eq_iff_eq_mul.1 e
  set t' : Lˣ := Units.map E.subtype.toMonoidHom t
  have ht' : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t' ^ m ≠ 1 := by
    intro m hm hb e
    apply ht m hm hb
    have e' : Units.map E.subtype.toMonoidHom (t ^ m) = Units.map E.subtype.toMonoidHom 1 := by
      rw [map_zpow, e, map_one]
    exact Units.map_injective (f := E.subtype.toMonoidHom) E.subtype_injective e'
  have htor : ∀ j, h * torusElt τ L j t' = torusElt τ L j t' * h := by
    intro j
    have e := hfix _ (torusElt_mem_adjointGroup j t)
    rwa [baseChangeGL_torusElt] at e
  have hx1 : ∀ i, h * xUnit τ L i 1 = xUnit τ L i 1 * h := by
    intro i
    have e := hfix _ (xUnit_mem_adjointGroup i (1 : E))
    rwa [baseChangeGL_xUnit, map_one] at e
  exact mem_adjointGroup_of_isUnit_bigCellDet h hz
    (bigCellDet_ne_zero_of_diagonal h (diagonal_of_commute ht' htor hx1))

theorem mem_adjointGroup_of_conj_entrywise
    (hτ : τ ≠ .G2) [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (E : Subfield L) (σ : E ≃+* E) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1) (h : ModGL τ L)
    (hz : ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0)
    (hσ : ∀ x ∈ adjointGroup τ E, h * baseChangeGL E.subtype x * h⁻¹ =
      baseChangeGL E.subtype (Units.map (entrywiseHom σ.toRingHom) x)) :
    h ∈ adjointGroup τ L :=
  mem_adjointGroup_of_conj_entrywise_of h2 ⟨0, τ.rank_pos⟩ (xCoeff_three_eq_zero hτ _) E σ t ht h
    hz hσ

end CFSG.TauCetiBridge.BigCell
