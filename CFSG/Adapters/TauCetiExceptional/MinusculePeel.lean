module

public import CFSG.Adapters.TauCetiExceptional.MinusculeGenPoint
public import CFSG.LieType.Steinberg.Minuscule.Form

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : Type*} [CommRing R]

include hV in
theorem wt_eq_of_rootOp_single_apply_ne_zero
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x y : Fin D.d} (h : D.rootOp R γ (Finsupp.single x 1) y ≠ 0) :
    D.wt y = D.wt x + toWeight γ := by
  rcases hV.isSignedMap_rootOp (R := R) hγ x with h0 | ⟨b, hb, hs⟩
  · rw [h0, Finsupp.zero_apply] at h
    exact absurd rfl h
  · have hby : b = y := by
      by_contra hne
      rcases hs with hs | hs <;> rw [hs] at h <;> simp [hne] at h
    rw [← hby]
    exact hb

theorem rootOp_apply_eq_sum (γ : Fin τ.rank → ℤ) (w : Fin D.d →₀ R) (y : Fin D.d) :
    D.rootOp R γ w y = ∑ x ∈ w.support, w x * D.rootOp R γ (Finsupp.single x 1) y := by
  conv_lhs => rw [← Finsupp.sum_single w]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, Finsupp.smul_single, smul_eq_mul,
    mul_one]

include hV in
theorem exists_of_rootOp_apply_ne_zero
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {w : Fin D.d →₀ R} {y : Fin D.d} (h : D.rootOp R γ w y ≠ 0) :
    ∃ x, w x ≠ 0 ∧ D.wt y = D.wt x + toWeight γ := by
  by_contra hne
  push Not at hne
  refine h ((rootOp_apply_eq_sum γ w y).trans (Finset.sum_eq_zero fun x hx => ?_))
  by_cases hxy : D.rootOp R γ (Finsupp.single x 1) y = 0
  · rw [hxy, mul_zero]
  · exact absurd (wt_eq_of_rootOp_single_apply_ne_zero hV hγ hxy)
      (hne x (Finsupp.mem_support_iff.1 hx))

include hV in
theorem rootOp_apply_eq_of_unique
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {w : Fin D.d →₀ R}
    {a y : Fin D.d} (hu : ∀ x, w x ≠ 0 → D.wt y = D.wt x + toWeight γ → x = a) :
    D.rootOp R γ w y = w a * D.rootOp R γ (Finsupp.single a 1) y := by
  rw [rootOp_apply_eq_sum]
  by_cases ha : w a = 0
  · rw [ha, zero_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hxy : D.rootOp R γ (Finsupp.single x 1) y = 0
    · rw [hxy, mul_zero]
    · have hxa := hu x (Finsupp.mem_support_iff.1 hx)
        (wt_eq_of_rootOp_single_apply_ne_zero hV hγ hxy)
      subst hxa
      exact absurd ha (Finsupp.mem_support_iff.1 hx)
  · rw [Finset.sum_eq_single a]
    · intro x hx hxa
      by_cases hxy : D.rootOp R γ (Finsupp.single x 1) y = 0
      · rw [hxy, mul_zero]
      · exact absurd (hu x (Finsupp.mem_support_iff.1 hx)
          (wt_eq_of_rootOp_single_apply_ne_zero hV hγ hxy)) hxa
    · intro h
      exact absurd (Finsupp.mem_support_iff.2 ha) h

variable {ι : Type*} (γ : ι → Fin τ.rank → ℤ) (c : ι → R) (φ : (Fin τ.rank → ℤ) →+ ℤ)

@[expose] def listProd
    (l : List ι) : Module.End R (Fin D.d →₀ R) :=
  (((l.map fun j => rootUnit hV R (γ j) (c j)).prod : (Module.End R (Fin D.d →₀ R))ˣ) :
    Module.End R (Fin D.d →₀ R))

theorem listProd_cons
    (j : ι) (l : List ι) :
    listProd hV γ c (j :: l) = (1 + c j • D.rootOp R (γ j)) * listProd hV γ c l := by
  rw [listProd, listProd, List.map_cons, List.prod_cons, Units.val_mul, coe_rootUnit]

@[expose] def Shift (φ₀ : ℤ) (l : List ι) (β : Fin τ.rank → ℤ) : Prop :=
  β = 0 ∨ (∃ j ∈ l, β = γ j) ∨ 2 * φ₀ ≤ φ β

include hV in
theorem apply_list_prod_rootUnit_single
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {φ₀ : ℤ} (hφ₀ : 0 < φ₀) (l : List ι) (hl : ∀ j ∈ l, IsRoot τ (γ j) ∧ φ₀ ≤ φ (γ j))
    (a : Fin D.d) :
    listProd hV γ c l (Finsupp.single a 1) a = 1 ∧
      ∀ x, listProd hV γ c l (Finsupp.single a 1) x ≠ 0 →
        ∃ β, Shift γ φ φ₀ l β ∧ D.wt x = D.wt a + toWeight β := by
  induction l with
  | nil =>
    refine ⟨by simp [listProd], fun x hx => ⟨0, Or.inl rfl, ?_⟩⟩
    have hxa : x = a := by
      by_contra hne
      simp [listProd, Ne.symm hne] at hx
    have h00 : toWeight (0 : Fin τ.rank → ℤ) = 0 := by
      ext i
      simp [toWeight]
    rw [hxa, h00, add_zero]
  | cons j l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem j hk)
    obtain ⟨hj, hφj⟩ := hl j List.mem_cons_self
    set w := listProd hV γ c l (Finsupp.single a 1)
    have hshift : ∀ β, Shift γ φ φ₀ l β → 0 ≤ φ β := by
      rintro β (rfl | ⟨k, hk, rfl⟩ | h)
      · simp
      · exact le_trans hφ₀.le (hl k (List.mem_cons_of_mem j hk)).2
      · omega
    have hEa : D.rootOp R (γ j) w a = 0 := by
      by_contra hne
      obtain ⟨x, hx, hxa⟩ := exists_of_rootOp_apply_ne_zero hV hj hne
      obtain ⟨β, hβ, hxβ⟩ := ih2 x hx
      rw [hxβ, add_assoc, ← toWeight_add] at hxa
      have h00 : toWeight (0 : Fin τ.rank → ℤ) = 0 := by
        ext i
        simp [toWeight]
      have h0 : β + γ j = 0 := toWeight_injective hpd (by
        rw [h00]
        exact (add_eq_left.1 hxa.symm))
      have := hshift β hβ
      have h1 : φ β + φ (γ j) = 0 := by rw [← map_add, h0, map_zero]
      omega
    rw [listProd_cons]
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    refine ⟨by rw [ih1, hEa, mul_zero, add_zero], fun x hx => ?_⟩
    by_cases hwx : w x = 0
    · rw [hwx, zero_add] at hx
      have hEx : D.rootOp R (γ j) w x ≠ 0 := fun h => hx (by rw [h, mul_zero])
      obtain ⟨x', hx', hxx'⟩ := exists_of_rootOp_apply_ne_zero hV hj hEx
      obtain ⟨β, hβ, hx'β⟩ := ih2 x' hx'
      refine ⟨β + γ j, ?_, by rw [hxx', hx'β, add_assoc, toWeight_add]⟩
      rcases hβ with rfl | ⟨k, hk, rfl⟩ | h
      · exact Or.inr (Or.inl ⟨j, List.mem_cons_self, zero_add _⟩)
      · refine Or.inr (Or.inr ?_)
        rw [map_add]
        have := (hl k (List.mem_cons_of_mem j hk)).2
        omega
      · refine Or.inr (Or.inr ?_)
        rw [map_add]
        omega
    · obtain ⟨β, hβ, hxβ⟩ := ih2 x hwx
      refine ⟨β, ?_, hxβ⟩
      rcases hβ with h | ⟨k, hk, h⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, List.mem_cons_of_mem j hk, h⟩)
      · exact Or.inr (Or.inr h)

include hV in
theorem list_prod_rootUnit_single_apply_head
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (j₀ : ι) (l : List ι) (hφ₀ : 0 < φ (γ j₀)) (hroot : IsRoot τ (γ j₀))
    (hl : ∀ j ∈ l, IsRoot τ (γ j) ∧ φ (γ j₀) ≤ φ (γ j)) (hne : ∀ j ∈ l, γ j ≠ γ j₀)
    {a b : Fin D.d} (hab : D.wt b = D.wt a + toWeight (γ j₀)) :
    listProd hV γ c (j₀ :: l) (Finsupp.single a 1) b =
      c j₀ * D.rootOp R (γ j₀) (Finsupp.single a 1) b := by
  obtain ⟨h1, h2⟩ := apply_list_prod_rootUnit_single hV γ c φ hpd hφ₀ l hl a
  set w := listProd hV γ c l (Finsupp.single a 1)
  have hwb : w b = 0 := by
    by_contra hwb
    obtain ⟨β, hβ, hbβ⟩ := h2 b hwb
    have hβγ : β = γ j₀ := toWeight_injective hpd (add_left_cancel (hbβ.symm.trans hab))
    rcases hβ with h | ⟨k, hk, h⟩ | h
    · rw [h] at hβγ
      rw [← hβγ, map_zero] at hφ₀
      exact lt_irrefl 0 hφ₀
    · exact hne k hk (h.symm.trans hβγ)
    · rw [hβγ] at h
      omega
  have hE : D.rootOp R (γ j₀) w b = w a * D.rootOp R (γ j₀) (Finsupp.single a 1) b :=
    rootOp_apply_eq_of_unique hV hroot fun x _ hx =>
      hV.wt_injective (add_right_cancel (hx.symm.trans hab))
  rw [listProd_cons]
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  change w b + c j₀ * D.rootOp R (γ j₀) w b = _
  rw [hwb, hE, h1, zero_add, one_mul]

include hV in
theorem exists_rootOp_single_eq
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ a b : Fin D.d, D.wt b = D.wt a + toWeight γ ∧
      (D.rootOp R γ (Finsupp.single a 1) b = 1 ∨ D.rootOp R γ (Finsupp.single a 1) b = -1) := by
  have hne := hV.rootOp_ne_zero (R := ℤ) hγ
  obtain ⟨a, ha⟩ : ∃ a, D.rootOp ℤ γ (Finsupp.single a 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (ext_single fun a => by rw [h a, LinearMap.zero_apply])
  rcases hV.isSignedMap_rootOp (R := ℤ) hγ a with h0 | ⟨b, hb, hs⟩
  · exact absurd h0 ha
  · refine ⟨a, b, hb, ?_⟩
    rw [rootOp_single_apply_eq_cast]
    rcases hs with hs | hs <;> rw [hs] <;> simp

@[expose] def EntriesIn {n : ℕ} (T : Subring R) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, M i j ∈ T

theorem EntriesIn.mul {n : ℕ} {T : Subring R} {M N : Matrix (Fin n) (Fin n) R}
    (hM : EntriesIn T M) (hN : EntriesIn T N) : EntriesIn T (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact T.sum_mem fun k _ => T.mul_mem (hM i k) (hN k j)

include hV in
theorem entriesIn_natMat_rootUnit
    (T : Subring R) (δ : Fin τ.rank → ℤ) {x : R} (hx : x ∈ T) :
    EntriesIn T (natMat R (rootUnit hV R δ x : Module.End R (Fin D.d →₀ R))) := fun i j => by
  rw [natMat_rootUnit, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.one_apply]
  refine T.add_mem ?_ (T.mul_mem hx (intCast_mem T _))
  split_ifs
  exacts [T.one_mem, T.zero_mem]

include hV in
theorem mem_of_natMat_list_prod_rootUnit
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (T : Subring R) :
    ∀ l : List ι, (l.map γ).Nodup → (∀ j ∈ l, IsRoot τ (γ j) ∧ 0 < φ (γ j)) →
      l.Pairwise (fun j j' => φ (γ j) ≤ φ (γ j')) →
      EntriesIn T (natMat R (listProd hV γ c l)) → ∀ j ∈ l, c j ∈ T
  | [], _, _, _, _ => fun _ h => absurd h List.not_mem_nil
  | j₀ :: l, hnd, hroot, hsort, hP => by
    have hnd' := List.nodup_cons.1 (List.map_cons .. ▸ hnd)
    obtain ⟨hr₀, hφ₀⟩ := hroot j₀ List.mem_cons_self
    have hl : ∀ j ∈ l, IsRoot τ (γ j) ∧ φ (γ j₀) ≤ φ (γ j) := fun j hj =>
      ⟨(hroot j (List.mem_cons_of_mem _ hj)).1, (List.pairwise_cons.1 hsort).1 j hj⟩
    have hne : ∀ j ∈ l, γ j ≠ γ j₀ := fun j hj h => hnd'.1 (h ▸ List.mem_map_of_mem hj)
    obtain ⟨a, b, hab, hε⟩ := exists_rootOp_single_eq hV (R := R) hr₀
    have hlead := list_prod_rootUnit_single_apply_head hV γ c φ hpd j₀ l hφ₀ hr₀ hl hne hab
    have hc₀ : c j₀ ∈ T := by
      have hb := hP b a
      rw [natMat_apply, hlead] at hb
      rcases hε with h | h
      · rwa [h, mul_one] at hb
      · rw [h, mul_neg_one] at hb
        simpa using T.neg_mem hb
    have hrest : EntriesIn T (natMat R (listProd hV γ c l)) := by
      have e : listProd hV γ c l =
          (rootUnit hV R (γ j₀) (-c j₀) : Module.End R (Fin D.d →₀ R)) *
            listProd hV γ c (j₀ :: l) := by
        rw [listProd, listProd, List.map_cons, List.prod_cons, ← Units.val_mul, ← mul_assoc,
          ← rootUnit_add, neg_add_cancel, rootUnit_zero, one_mul]
      rw [e, map_mul]
      exact (entriesIn_natMat_rootUnit hV T _ (T.neg_mem hc₀)).mul hP
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hc₀
    · exact mem_of_natMat_list_prod_rootUnit hpd T l hnd'.2
        (fun k hk => hroot k (List.mem_cons_of_mem _ hk)) (List.pairwise_cons.1 hsort).2 hrest j hj

@[expose] def unitsIn (T : Subring R) : Subgroup Rˣ where
  carrier := {u | (u : R) ∈ T ∧ ((u⁻¹ : Rˣ) : R) ∈ T}
  one_mem' := ⟨T.one_mem, by simp⟩
  mul_mem' := fun {u v} hu hv => ⟨by simpa using T.mul_mem hu.1 hv.1, by
    simpa [mul_inv_rev] using T.mul_mem hv.2 hu.2⟩
  inv_mem' := fun {u} hu => ⟨hu.2, by simpa using hu.1⟩

include hV in
theorem mem_unitsIn_of_torusCharacter
    (T : Subring R) (t : Fin τ.rank → Rˣ)
    (h : ∀ a : Fin D.d, TauCeti.torusCharacter t (D.wt a) ∈ unitsIn T) (k : Fin τ.rank) :
    t k ∈ unitsIn T := by
  have hl : ∀ l : List (ℕ × ℤ), (∀ p ∈ l, p.1 < D.d) →
      TauCeti.torusCharacter t ((l.map fun p => p.2 • D.wt p.1).sum) ∈ unitsIn T := by
    intro l hl
    induction l with
    | nil => simp
    | cons p l ih =>
      rw [List.map_cons, List.sum_cons, TauCeti.torusCharacter_add,
        TauCeti.torusCharacter_zsmul]
      refine (unitsIn T).mul_mem ((unitsIn T).zpow_mem ?_ _)
        (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
      exact h ⟨p.1, hl p List.mem_cons_self⟩
  have := hl _ (hV.pgen_lt k)
  rwa [hV.pgen_sum k, TauCeti.torusCharacter_single, zpow_one] at this

@[expose] def htHom : (Fin τ.rank → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (ht (ι := Fin τ.rank)) fun u v => by
    simp only [ht, Pi.add_apply, Finset.sum_add_distrib]

theorem htHom_apply (v : Fin τ.rank → ℤ) : htHom v = ht v :=
  rfl

include hV in
theorem eq_top_of_minGenMat
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hord : DegOrdered D) (T : Subring (GenRing τ)) (hT : ∀ i j, minGenMat hV i j ∈ T)
    (hinv : ∃ y ∈ T, y * bigCellDet (minGenMat hV) = 1) : T = ⊤ := by
  have hLDU := isLDU_bigCellUnit hV (GenRing τ) hord (genCm τ) (genA τ) (genCp τ)
  rw [minGenMat, natMat_bigCellUnit] at hT hinv
  have hmem := hLDU.mem T hT hinv
  have hpos : ∀ j ∈ posList τ, IsRoot τ (posRootEnum τ j) ∧ 0 < htHom (posRootEnum τ j) :=
    fun j _ => posRootEnum_pos τ j
  have hcp : ∀ j, genCp τ j ∈ T := fun j =>
    mem_of_natMat_list_prod_rootUnit hV (posRootEnum τ) (genCp τ) htHom hpd T (posList τ)
      ((posList_nodup τ).map (posRootEnum_injective τ)) hpos (posList_sorted τ)
      (fun i j => (hmem i).2.2.2 j) j (mem_posList τ j)
  have hneg : ∀ j ∈ posList τ, IsRoot τ (-posRootEnum τ j) ∧ 0 < (-htHom) (-posRootEnum τ j) :=
    fun j _ => ⟨CFSG.LieType.Chevalley.IsRoot.neg (posRootEnum_pos τ j).1, by
      rw [AddMonoidHom.neg_apply, map_neg, neg_neg]
      exact (posRootEnum_pos τ j).2⟩
  have hcm : ∀ j, genCm τ j ∈ T := fun j =>
    mem_of_natMat_list_prod_rootUnit hV (fun j => -posRootEnum τ j) (genCm τ) (-htHom) hpd T
      (posList τ) ((posList_nodup τ).map (neg_injective.comp (posRootEnum_injective τ))) hneg
      ((posList_sorted τ).imp fun h => by
        rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, map_neg, neg_neg, neg_neg]
        exact h)
      (fun i j => (hmem j).2.2.1 i) j (mem_posList τ j)
  have hdiag : ∀ a : Fin D.d, TauCeti.torusCharacter (genA τ) (D.wt a) ∈ unitsIn T := by
    intro a
    obtain ⟨⟨y, hy, hyd⟩, hd, -, -⟩ := hmem a
    rw [dT, natMat_diagUnit, Matrix.diagonal_apply_eq] at hyd hd
    refine ⟨hd, ?_⟩
    have e : y = ((TauCeti.torusCharacter (genA τ) (D.wt a))⁻¹ : (GenRing τ)ˣ) := by
      calc y = y * ((TauCeti.torusCharacter (genA τ) (D.wt a) : GenRing τ) *
            (((TauCeti.torusCharacter (genA τ) (D.wt a))⁻¹ : (GenRing τ)ˣ) : GenRing τ)) := by
            rw [Units.mul_inv, mul_one]
        _ = _ := by rw [← mul_assoc, hyd, one_mul]
    rw [← e]
    exact hy
  exact eq_top_of_mem_gen T hcm hcp fun k => mem_unitsIn_of_torusCharacter hV T (genA τ) hdiag k

end CFSG.TauCetiBridge.Minuscule
