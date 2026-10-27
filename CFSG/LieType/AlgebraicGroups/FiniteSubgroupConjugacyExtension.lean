module

public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
public import CFSG.LieType.AlgebraicGroups.FiniteAffineEquations
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open TensorProduct

private def unitEntry {τ : Tag} {R : Type} [CommRing R]
    (u : (Module.End R (RootModule τ R))ˣ) (a b : Label τ) : R :=
  (u : Module.End R (RootModule τ R)) (Finsupp.single b 1) a

private theorem unit_eq_of_entries {τ : Tag} {R : Type} [CommRing R]
    {u v : (Module.End R (RootModule τ R))ˣ}
    (h : ∀ a b, unitEntry u a b = unitEntry v a b) : u = v := by
  apply Units.ext
  exact Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    exact Finsupp.ext fun a => h a b)

private theorem map_unitEntry {τ : Tag} {R S : Type} [CommRing R] [CommRing S]
    {f : R →+* S} {u : (Module.End R (RootModule τ R))ˣ}
    {v : (Module.End S (RootModule τ S))ˣ}
    (h : BaseChange f (u : Module.End R (RootModule τ R))
      (v : Module.End S (RootModule τ S))) (a b : Label τ) :
    f (unitEntry u a b) = unitEntry v a b := by
  exact congrArg (fun x : RootModule τ S => x a) (h b)

section RingBaseChange

variable {τ : Tag} {R S : Type} [CommRing R] [CommRing S]

private def baseChangeEndRing (f : R →+* S)
    (A : Module.End R (RootModule τ R)) : Module.End S (RootModule τ S) :=
  Finsupp.linearCombination S fun b =>
    Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1))

private theorem baseChangeEndRing_single (f : R →+* S)
    (A : Module.End R (RootModule τ R)) (b : Label τ) :
    baseChangeEndRing f A (Finsupp.single b 1) =
      Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1)) := by
  simp [baseChangeEndRing]

private theorem baseChange_baseChangeEndRing (f : R →+* S)
    (A : Module.End R (RootModule τ R)) :
    BaseChange f A (baseChangeEndRing f A) := fun b =>
  (baseChangeEndRing_single f A b).symm

private def baseChangeEndHomRing (f : R →+* S) :
    Module.End R (RootModule τ R) →* Module.End S (RootModule τ S) where
  toFun := baseChangeEndRing f
  map_one' := (baseChange_baseChangeEndRing f 1).unique (BaseChange.one (τ := τ) (f := f))
  map_mul' A B := (baseChange_baseChangeEndRing f (A * B)).unique
    ((baseChange_baseChangeEndRing f A).mul (baseChange_baseChangeEndRing f B))

private def baseChangeGLRing (f : R →+* S) :
    (Module.End R (RootModule τ R))ˣ →* (Module.End S (RootModule τ S))ˣ :=
  Units.map (baseChangeEndHomRing f)

private theorem coe_baseChangeGLRing (f : R →+* S)
    (g : (Module.End R (RootModule τ R))ˣ) :
    ((baseChangeGLRing f g : (Module.End S (RootModule τ S))ˣ) :
        Module.End S (RootModule τ S)) =
      baseChangeEndRing f (g : Module.End R (RootModule τ R)) := rfl

end RingBaseChange

section RingEqField

variable {τ : Tag} {R S : Type} [Field R] [Field S]

private theorem baseChangeGLRing_eq_baseChangeGL (f : R →+* S)
    (u : (Module.End R (RootModule τ R))ˣ) :
    baseChangeGLRing f u = baseChangeGL f u := by
  apply Units.ext
  exact (baseChange_baseChangeEndRing f (u : Module.End R (RootModule τ R))).unique
    (baseChange_baseChangeEnd f (u : Module.End R (RootModule τ R)))

end RingEqField

namespace FiniteConjugacy

variable {τ : Tag} {Γ k L : Type} [Group Γ] [Fintype Γ] [Field k] [Field L] [Algebra k L]

private abbrev SepPair (Γ : Type) [Group Γ] := {p : Γ × Γ // p.1 ≠ p.2}

private abbrev Param (n : Γ → ℕ) := (Σ a : Γ, Fin (n a)) ⊕ SepPair Γ

private abbrev Relations (Γ : Type) (τ : Tag) [Group Γ] :=
  (Γ × Γ × Label τ × Label τ) ⊕ (Label τ × Label τ) ⊕ SepPair Γ

private def paramWord (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ) (a : Γ) :
    List (Letter τ × MvPolynomial (Param n) k) :=
  List.ofFn fun i => (ℓ a i, MvPolynomial.X (Sum.inl ⟨a, i⟩))

private def paramUnit (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ) (a : Γ) :
    (Module.End (MvPolynomial (Param n) k)
      (RootModule τ (MvPolynomial (Param n) k)))ˣ :=
  wordUnit τ _ (paramWord n ℓ a)

private def relation (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) : Relations Γ τ → MvPolynomial (Param n) k
  | .inl (a, b, i, j) =>
      unitEntry (paramUnit n ℓ (a * b)) i j - unitEntry (paramUnit n ℓ a * paramUnit n ℓ b) i j
  | .inr (.inl (i, j)) => unitEntry (paramUnit n ℓ 1) i j - unitEntry 1 i j
  | .inr (.inr p) =>
      (unitEntry (paramUnit n ℓ p.1.1) (sep p).1 (sep p).2 -
        unitEntry (paramUnit n ℓ p.1.2) (sep p).1 (sep p).2) * MvPolynomial.X (.inr p) - 1

private abbrev Coord (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) :=
  MvPolynomial (Param n) k ⧸ Ideal.span (Set.range (relation n ℓ sep))

omit [Fintype Γ] in
private theorem point_relation_zero (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L)
    (r : Relations Γ τ) :
    (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (relation n ℓ sep r) = 0 := by
  have h : Ideal.Quotient.mkₐ k (Ideal.span (Set.range (relation (k := k) n ℓ sep)))
      (relation n ℓ sep r) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨r, rfl⟩)
  exact (congrArg y h).trans (map_zero y)

private def pointUnit (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L)
    (a : Γ) : ModGL τ L :=
  wordUnit τ L (mapWord (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (paramWord n ℓ a))

omit [Fintype Γ] in
private theorem pointUnit_entry (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L)
    (a : Γ) (i j : Label τ) :
    (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (unitEntry (paramUnit n ℓ a) i j) =
      unitEntry (pointUnit n ℓ sep y a) i j :=
  map_unitEntry (u := paramUnit n ℓ a) (v := pointUnit n ℓ sep y a)
    (baseChange_wordUnit (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (paramWord n ℓ a)) i j

omit [Fintype Γ] in
private theorem pointUnit_product_entry (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L)
    (a b : Γ) (i j : Label τ) :
    (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (unitEntry (paramUnit n ℓ a * paramUnit n ℓ b) i j) =
      unitEntry (pointUnit n ℓ sep y a * pointUnit n ℓ sep y b) i j := by
  apply map_unitEntry (u := paramUnit n ℓ a * paramUnit n ℓ b)
    (v := pointUnit n ℓ sep y a * pointUnit n ℓ sep y b)
  simpa only [Units.val_mul, paramUnit, pointUnit] using
    (baseChange_wordUnit (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom
      (paramWord n ℓ a)).mul (baseChange_wordUnit
        (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (paramWord n ℓ b))

private theorem map_unitEntry_one {τ : Tag} {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (i j : Label τ) :
    f (unitEntry (1 : (Module.End R (RootModule τ R))ˣ) i j) =
      unitEntry (1 : (Module.End S (RootModule τ S))ˣ) i j := by
  apply map_unitEntry (u := 1) (v := 1)
  simpa only [Units.val_one] using (BaseChange.one (τ := τ) (f := f))

omit [Fintype Γ] in
private theorem pointUnit_one (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L) :
    pointUnit n ℓ sep y 1 = 1 := by
  apply unit_eq_of_entries
  intro i j
  have h := point_relation_zero n ℓ sep y (.inr (.inl (i, j)))
  simp only [relation, map_sub] at h
  rw [pointUnit_entry, map_unitEntry_one] at h
  exact sub_eq_zero.mp h

omit [Fintype Γ] in
private theorem pointUnit_mul (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L)
    (a b : Γ) : pointUnit n ℓ sep y (a * b) = pointUnit n ℓ sep y a * pointUnit n ℓ sep y b := by
  apply unit_eq_of_entries
  intro i j
  have h := point_relation_zero n ℓ sep y (.inl (a, b, i, j))
  simp only [relation, map_sub, pointUnit_entry, pointUnit_product_entry, sub_eq_zero] at h
  exact h

private def pointHom (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L) :
    Γ →* adjointGroup τ L where
  toFun a := wordElt τ
    (mapWord (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom (paramWord n ℓ a))
  map_one' := Subtype.ext (by
    simpa only [coe_wordElt, Subgroup.coe_one, pointUnit] using pointUnit_one n ℓ sep y)
  map_mul' a b := Subtype.ext (by
    simpa only [coe_wordElt, Subgroup.coe_mul, pointUnit] using pointUnit_mul n ℓ sep y a b)

omit [Fintype Γ] in
private theorem coe_pointHom (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L) (a : Γ) :
    (pointHom n ℓ sep y a : ModGL τ L) = pointUnit n ℓ sep y a :=
  coe_wordElt _

omit [Fintype Γ] in
private theorem pointHom_injective (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (y : Coord (k := k) n ℓ sep →ₐ[k] L) :
    Function.Injective (pointHom n ℓ sep y) := by
  intro a b hab
  by_contra hne
  let p : SepPair Γ := ⟨(a, b), hne⟩
  have h := point_relation_zero n ℓ sep y (.inr (.inr p))
  have hab' : pointUnit n ℓ sep y a = pointUnit n ℓ sep y b := by
    simpa only [coe_pointHom] using congrArg (fun x : adjointGroup τ L => (x : ModGL τ L)) hab
  have h' := congrArg (fun u : ModGL τ L => unitEntry u (sep p).1 (sep p).2) hab'
  simp only [relation, map_sub, map_mul, map_one, pointUnit_entry] at h
  change (unitEntry (pointUnit n ℓ sep y a) (sep p).1 (sep p).2 -
    unitEntry (pointUnit n ℓ sep y b) (sep p).1 (sep p).2) * _ - 1 = 0 at h
  rw [h', sub_self, zero_mul, zero_sub, neg_eq_zero] at h
  exact one_ne_zero h

omit [Fintype Γ] in
private theorem exists_point_eq (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (c : ∀ a, Fin (n a) → L) (f : Γ →* adjointGroup τ L)
    (hf : Function.Injective f)
    (hc : ∀ a, wordUnit τ L (List.ofFn fun i => (ℓ a i, c a i)) = (f a : ModGL τ L)) :
    ∃ sep : SepPair Γ → Label τ × Label τ,
      ∃ y : Coord (k := k) n ℓ sep →ₐ[k] L, ∀ a, pointHom n ℓ sep y a = f a := by
  classical
  have hsep : ∀ p : SepPair Γ, ∃ ij : Label τ × Label τ,
      unitEntry (f p.1.1 : ModGL τ L) ij.1 ij.2 ≠
        unitEntry (f p.1.2 : ModGL τ L) ij.1 ij.2 := by
    intro p
    by_contra h
    apply p.2
    apply hf
    apply Subtype.ext
    apply unit_eq_of_entries
    simpa only [not_exists, Prod.forall, not_not] using h
  choose sep hsep using hsep
  let values : Param n → L := Sum.elim (fun ai => c ai.1 ai.2)
    (fun p => (unitEntry (f p.1.1 : ModGL τ L) (sep p).1 (sep p).2 -
      unitEntry (f p.1.2 : ModGL τ L) (sep p).1 (sep p).2)⁻¹)
  let z : MvPolynomial (Param n) k →ₐ[k] L := MvPolynomial.aeval values
  have hw : ∀ a, mapWord z.toRingHom (paramWord (k := k) n ℓ a) =
      List.ofFn fun i => (ℓ a i, c a i) := by
    intro a
    simp only [paramWord, mapWord, List.map_ofFn, Function.comp_def, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, z, MvPolynomial.aeval_X, values, Sum.elim_inl]
  have hbc : ∀ a, BaseChange z.toRingHom
      (paramUnit (k := k) n ℓ a : Module.End _ (RootModule τ _))
      ((f a : ModGL τ L) : Module.End L (RootModule τ L)) := by
    intro a
    have h := baseChange_wordUnit z.toRingHom (paramWord (k := k) n ℓ a)
    rw [hw a, hc a] at h
    exact h
  have hz : ∀ r : Relations Γ τ, z.toRingHom (relation n ℓ sep r) = 0 := by
    rintro (⟨a, b, i, j⟩ | (⟨i, j⟩ | p))
    · have hm : BaseChange z.toRingHom
          ((paramUnit (k := k) n ℓ a * paramUnit (k := k) n ℓ b :
            (Module.End (MvPolynomial (Param n) k) (RootModule τ (MvPolynomial (Param n) k)))ˣ) :
              Module.End (MvPolynomial (Param n) k) (RootModule τ (MvPolynomial (Param n) k)))
          (((f a : ModGL τ L) * (f b : ModGL τ L)) : Module.End L (RootModule τ L)) := by
        simpa only [Units.val_mul] using (hbc a).mul (hbc b)
      simp only [relation, map_sub,
        map_unitEntry (u := paramUnit n ℓ (a * b)) (v := (f (a * b) : ModGL τ L)) (hbc (a * b)),
        map_unitEntry (u := paramUnit n ℓ a * paramUnit n ℓ b)
          (v := (f a : ModGL τ L) * (f b : ModGL τ L)) hm,
        map_mul, Subgroup.coe_mul, sub_self]
    · simp only [relation, map_sub,
        map_unitEntry (u := paramUnit n ℓ 1) (v := (f 1 : ModGL τ L)) (hbc 1),
        map_unitEntry_one, map_one, Subgroup.coe_one, sub_self]
    · have hne : unitEntry (f p.1.1 : ModGL τ L) (sep p).1 (sep p).2 -
          unitEntry (f p.1.2 : ModGL τ L) (sep p).1 (sep p).2 ≠ 0 :=
        sub_ne_zero.mpr (hsep p)
      simp only [relation, map_sub, map_mul, map_one,
        map_unitEntry (u := paramUnit n ℓ p.1.1) (v := (f p.1.1 : ModGL τ L)) (hbc p.1.1),
        map_unitEntry (u := paramUnit n ℓ p.1.2) (v := (f p.1.2 : ModGL τ L)) (hbc p.1.2)]
      change _ * z.toRingHom (MvPolynomial.X (.inr p)) - 1 = 0
      have hzX : z.toRingHom (MvPolynomial.X (.inr p)) =
          (unitEntry (f p.1.1 : ModGL τ L) (sep p).1 (sep p).2 -
            unitEntry (f p.1.2 : ModGL τ L) (sep p).1 (sep p).2)⁻¹ :=
        MvPolynomial.aeval_X values (.inr p)
      rw [hzX, mul_inv_cancel₀ hne, sub_self]
  have hker : Ideal.span (Set.range (relation (k := k) n ℓ sep)) ≤ RingHom.ker z := by
    rw [Ideal.span_le]
    rintro _ ⟨r, rfl⟩
    exact hz r
  let y : Coord (k := k) n ℓ sep →ₐ[k] L :=
    Ideal.Quotient.liftₐ _ z fun p hp => hker hp
  have hy : y.comp (Ideal.Quotient.mkₐ k _) = z := Ideal.Quotient.liftₐ_comp _ _ _
  refine ⟨sep, y, fun a => Subtype.ext ?_⟩
  rw [coe_pointHom]
  change wordUnit τ L (mapWord (y.comp (Ideal.Quotient.mkₐ k _)).toRingHom
    (paramWord n ℓ a)) = _
  rw [hy, hw a, hc a]

private abbrev FamilyCoord (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (N m : ℕ) :=
  Coord (k := k) n ℓ sep ⊗[k] TorusAffine k τ.rank (N + m)

private instance familyCoordCommRing (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (N m : ℕ) :
    CommRing (FamilyCoord (k := k) n ℓ sep N m) :=
  Algebra.TensorProduct.instCommRing

private def familyWord (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) (N m : ℕ) (a : Γ) :
    List (Letter τ × FamilyCoord (k := k) n ℓ sep N m) :=
  mapWord (Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ k _)).toRingHom
    (paramWord n ℓ a)

private def familyConjugator (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N m : ℕ}
    (w : WeylGroup τ) (α : Fin N → Fin τ.rank → ℤ) (β : Fin m → Fin τ.rank → ℤ) :
    List (Letter τ × FamilyCoord (k := k) n ℓ sep N m) :=
  mapWord Algebra.TensorProduct.includeRight.toRingHom (bruhatParamWord τ k w α β)

private def familyEquations {J : Type} (t : J → Γ → ModGL τ k)
    (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (m : WeylGroup τ → ℕ)
    (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ) (jw : J × WeylGroup τ)
    (r : Γ × Label τ × Label τ) : FamilyCoord (k := k) n ℓ sep N (m jw.2) :=
  unitEntry (wordUnit τ _ (familyConjugator n ℓ sep jw.2 α (β jw.2)) *
      wordUnit τ _ (familyWord n ℓ sep N (m jw.2) r.1) *
        (wordUnit τ _ (familyConjugator n ℓ sep jw.2 α (β jw.2)))⁻¹) r.2.1 r.2.2 -
    algebraMap k _ (unitEntry (t jw.1 r.1) r.2.1 r.2.2)

private def familyConjUnit (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (w : WeylGroup τ) {m : ℕ}
    (β : Fin m → Fin τ.rank → ℤ) (a : Γ) :
    (Module.End (FamilyCoord (k := k) n ℓ sep N m)
      (RootModule τ (FamilyCoord (k := k) n ℓ sep N m)))ˣ :=
  wordUnit τ _ (familyConjugator n ℓ sep w α β) *
    wordUnit τ _ (familyWord n ℓ sep N m a) *
      (wordUnit τ _ (familyConjugator n ℓ sep w α β))⁻¹

private def pointConjUnit (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (w : WeylGroup τ) {m : ℕ}
    (β : Fin m → Fin τ.rank → ℤ)
    (x : FamilyCoord (k := k) n ℓ sep N m →ₐ[k] L) (a : Γ) :
    (Module.End L (RootModule τ L))ˣ :=
  wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
      (bruhatParamWord τ k w α β)) *
    (pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a : ModGL τ L) *
      (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
        (bruhatParamWord τ k w α β)))⁻¹

private def centralizerEquations (z : ModGL τ k)
    (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (m : WeylGroup τ → ℕ)
    (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ) (w : WeylGroup τ)
    (r : Γ × Label τ × Label τ) : FamilyCoord (k := k) n ℓ sep N (m w) :=
  unitEntry
    (familyConjUnit n ℓ sep α w (β w) r.1 *
      baseChangeGLRing (algebraMap k (FamilyCoord (k := k) n ℓ sep N (m w))) z)
      r.2.1 r.2.2 -
  unitEntry
    (baseChangeGLRing (algebraMap k (FamilyCoord (k := k) n ℓ sep N (m w))) z *
      familyConjUnit n ℓ sep α w (β w) r.1) r.2.1 r.2.2

private theorem mapWord_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (w : List (Letter τ × R)) :
    mapWord g (mapWord f w) = mapWord (g.comp f) w := by
  simp only [mapWord, List.map_map, Function.comp_def, RingHom.coe_comp]

omit [Fintype Γ] in
private theorem mapWord_familyWord (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N m : ℕ}
    (x : FamilyCoord (k := k) n ℓ sep N m →ₐ[k] L) (a : Γ) :
    mapWord x.toRingHom (familyWord n ℓ sep N m a) =
      mapWord ((x.comp Algebra.TensorProduct.includeLeft).comp
        (Ideal.Quotient.mkₐ k _)).toRingHom (paramWord n ℓ a) := by
  rw [familyWord, mapWord_comp]
  rfl

omit [Fintype Γ] in
private theorem mapWord_familyConjugator (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N m : ℕ}
    (w : WeylGroup τ) (α : Fin N → Fin τ.rank → ℤ) (β : Fin m → Fin τ.rank → ℤ)
    (x : FamilyCoord (k := k) n ℓ sep N m →ₐ[k] L) :
    mapWord x.toRingHom (familyConjugator n ℓ sep w α β) =
      mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
        (bruhatParamWord τ k w α β) := by
  rw [familyConjugator, mapWord_comp]
  rfl

private theorem baseChange_familyConjUnit (n : Γ → ℕ)
    (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (w : WeylGroup τ) {m : ℕ}
    (β : Fin m → Fin τ.rank → ℤ)
    (x : FamilyCoord (k := k) n ℓ sep N m →ₐ[k] L) (a : Γ) :
    BaseChange x.toRingHom
      (Units.val (familyConjUnit n ℓ sep α w β a) :
        Module.End (FamilyCoord (k := k) n ℓ sep N m)
          (RootModule τ (FamilyCoord (k := k) n ℓ sep N m)))
      (Units.val (pointConjUnit n ℓ sep α w β x a) : Module.End L (RootModule τ L)) := by
  have hg := baseChange_wordUnit x.toRingHom (familyConjugator n ℓ sep w α β)
  have ha := baseChange_wordUnit x.toRingHom (familyWord n ℓ sep N m a)
  have hc := (hg.mul ha).mul hg.units_inv
  simpa only [familyConjUnit, pointConjUnit, mapWord_familyWord, mapWord_familyConjugator,
    Units.val_mul, Units.val_inv_eq_inv_val, coe_pointHom, pointUnit] using hc

omit [Fintype Γ] in
private theorem familyEquations_zero_iff {J : Type} (t : J → Γ → ModGL τ k)
    (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (m : WeylGroup τ → ℕ)
    (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ) (jw : J × WeylGroup τ)
    (x : FamilyCoord (k := k) n ℓ sep N (m jw.2) →ₐ[k] L) :
    (∀ r, x (familyEquations t n ℓ sep α m β jw r) = 0) ↔
      ∀ a, wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
          (bruhatParamWord τ k jw.2 α (β jw.2))) *
        (pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a : ModGL τ L) *
          (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
            (bruhatParamWord τ k jw.2 α (β jw.2))))⁻¹ =
              baseChangeGL (algebraMap k L) (t jw.1 a) := by
  have h : ∀ a i j, x (familyEquations t n ℓ sep α m β jw (a, i, j)) = 0 ↔
      unitEntry (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
          (bruhatParamWord τ k jw.2 α (β jw.2))) *
        (pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a : ModGL τ L) *
          (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
            (bruhatParamWord τ k jw.2 α (β jw.2))))⁻¹) i j =
              unitEntry (baseChangeGL (algebraMap k L) (t jw.1 a)) i j := by
    intro a i j
    have hg := baseChange_wordUnit x.toRingHom
      (familyConjugator (k := k) n ℓ sep jw.2 α (β jw.2))
    have ha := baseChange_wordUnit x.toRingHom (familyWord (k := k) n ℓ sep N (m jw.2) a)
    have hc := (hg.mul ha).mul hg.units_inv
    simp only [mapWord_familyWord, mapWord_familyConjugator] at hc
    have hc' : BaseChange x.toRingHom
        ((wordUnit τ _ (familyConjugator (k := k) n ℓ sep jw.2 α (β jw.2)) *
          wordUnit τ _ (familyWord (k := k) n ℓ sep N (m jw.2) a) *
            (wordUnit τ _ (familyConjugator (k := k) n ℓ sep jw.2 α (β jw.2)))⁻¹) :
              Module.End _ (RootModule τ _))
        ((wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
            (bruhatParamWord τ k jw.2 α (β jw.2))) *
          (pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a : ModGL τ L) *
            (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
              (bruhatParamWord τ k jw.2 α (β jw.2))))⁻¹) :
                Module.End L (RootModule τ L)) := by
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, coe_pointHom, pointUnit] using hc
    rw [familyEquations, map_sub, AlgHom.commutes]
    change x.toRingHom (unitEntry _ i j) - algebraMap k L (unitEntry _ i j) = 0 ↔ _
    rw [map_unitEntry
      (u := wordUnit τ _ (familyConjugator (k := k) n ℓ sep jw.2 α (β jw.2)) *
        wordUnit τ _ (familyWord (k := k) n ℓ sep N (m jw.2) a) *
          (wordUnit τ _ (familyConjugator (k := k) n ℓ sep jw.2 α (β jw.2)))⁻¹)
      (v := wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
          (bruhatParamWord τ k jw.2 α (β jw.2))) *
        (pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a : ModGL τ L) *
          (wordUnit τ L (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
            (bruhatParamWord τ k jw.2 α (β jw.2))))⁻¹) hc', sub_eq_zero]
    have hb : algebraMap k L (unitEntry (t jw.1 a) i j) =
        unitEntry (baseChangeGL (algebraMap k L) (t jw.1 a)) i j :=
      congrArg (fun v : RootModule τ L => v i)
        (baseChangeGL_apply_single (algebraMap k L) (t jw.1 a) j).symm
    rw [hb]
  constructor
  · intro hx a
    apply unit_eq_of_entries
    intro i j
    exact (h a i j).mp (hx (a, i, j))
  · intro hx
    rintro ⟨a, i, j⟩
    apply (h a i j).mpr
    exact congrArg (fun u : ModGL τ L => unitEntry u i j) (hx a)

private theorem centralizerEquations_zero_iff (z : ModGL τ k)
    (n : Γ → ℕ) (ℓ : ∀ a, Fin (n a) → Letter τ)
    (sep : SepPair Γ → Label τ × Label τ) {N : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (m : WeylGroup τ → ℕ)
    (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ) (w : WeylGroup τ)
    (x : FamilyCoord (k := k) n ℓ sep N (m w) →ₐ[k] L) :
    (∀ r, x (centralizerEquations z n ℓ sep α m β w r) = 0) ↔
      ∀ a, pointConjUnit n ℓ sep α w (β w) x a *
          baseChangeGL (algebraMap k L) z =
        baseChangeGL (algebraMap k L) z *
          pointConjUnit n ℓ sep α w (β w) x a := by
  let A := FamilyCoord (k := k) n ℓ sep N (m w)
  let Z_A : (Module.End A (RootModule τ A))ˣ :=
    baseChangeGLRing (algebraMap k A) z
  let Z_L : (Module.End L (RootModule τ L))ˣ :=
    baseChangeGL (algebraMap k L) z
  have hZ_A : BaseChange (algebraMap k A) (z : Module.End k (RootModule τ k))
      (Z_A : Module.End A (RootModule τ A)) := by
    simpa only [Z_A, coe_baseChangeGLRing] using
      (baseChange_baseChangeEndRing (algebraMap k A) (z : Module.End k (RootModule τ k)))
  have hZ_ring : BaseChange x.toRingHom (Z_A : Module.End A (RootModule τ A))
      ((baseChangeGLRing (algebraMap k L) z : (Module.End L (RootModule τ L))ˣ) :
        Module.End L (RootModule τ L)) := by
    intro b
    rw [← hZ_A b]
    have hmap : Finsupp.mapRange x.toRingHom x.toRingHom.map_zero
        (Finsupp.mapRange (algebraMap k A) (algebraMap k A).map_zero
          ((z : Module.End k (RootModule τ k)) (Finsupp.single b 1))) =
        Finsupp.mapRange (algebraMap k L) (algebraMap k L).map_zero
          ((z : Module.End k (RootModule τ k)) (Finsupp.single b 1)) := by
      ext a
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply]
      exact x.commutes (((z : Module.End k (RootModule τ k)) (Finsupp.single b 1)) a)
    rw [hmap]
    exact (baseChange_baseChangeEndRing (algebraMap k L) z) b
  have hZ_eq : baseChangeGLRing (algebraMap k L) z = Z_L :=
    baseChangeGLRing_eq_baseChangeGL (algebraMap k L) z
  have hZ : BaseChange x.toRingHom (Z_A : Module.End A (RootModule τ A))
      (Z_L : Module.End L (RootModule τ L)) := by
    rw [← hZ_eq]
    exact hZ_ring
  have h_uZ : ∀ a, BaseChange x.toRingHom
      ((familyConjUnit n ℓ sep α w (β w) a * Z_A :
        (Module.End A (RootModule τ A))ˣ) : Module.End A (RootModule τ A))
      ((pointConjUnit n ℓ sep α w (β w) x a * Z_L :
        (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) := by
    intro a
    simpa only [Units.val_mul] using
      (baseChange_familyConjUnit n ℓ sep α w (β w) x a).mul hZ
  have h_Zu : ∀ a, BaseChange x.toRingHom
      ((Z_A * familyConjUnit n ℓ sep α w (β w) a :
        (Module.End A (RootModule τ A))ˣ) : Module.End A (RootModule τ A))
      ((Z_L * pointConjUnit n ℓ sep α w (β w) x a :
        (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) := by
    intro a
    simpa only [Units.val_mul] using hZ.mul
      (baseChange_familyConjUnit n ℓ sep α w (β w) x a)
  have h : ∀ a i j,
      x (centralizerEquations z n ℓ sep α m β w (a, i, j)) = 0 ↔
        unitEntry (pointConjUnit n ℓ sep α w (β w) x a * Z_L) i j =
          unitEntry (Z_L * pointConjUnit n ℓ sep α w (β w) x a) i j := by
    intro a i j
    rw [centralizerEquations, map_sub]
    change x.toRingHom (unitEntry (familyConjUnit n ℓ sep α w (β w) a * Z_A) i j) -
        x.toRingHom (unitEntry (Z_A * familyConjUnit n ℓ sep α w (β w) a) i j) = 0 ↔ _
    rw [map_unitEntry (h_uZ a) i j, map_unitEntry (h_Zu a) i j, sub_eq_zero]
  constructor
  · intro hx a
    apply unit_eq_of_entries
    intro i j
    exact (h a i j).mp (hx (a, i, j))
  · intro hx
    rintro ⟨a, i, j⟩
    exact (h a i j).mpr (congrArg (fun u => unitEntry u i j) (hx a))

end FiniteConjugacy

open FiniteConjugacy

theorem finite_subgroup_conjugacy_field_extension {τ : Tag} {Γ k L J : Type}
    [Group Γ] [Fintype Γ] [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L]
    [Finite J] (t : J → Γ → ModGL τ k)
    (hbase : ∀ f : Γ →* adjointGroup τ k, Function.Injective f →
      ∃ j, ∃ g ∈ adjointGroup τ k, ∀ a, g * (f a : ModGL τ k) * g⁻¹ = t j a)
    (f : Γ →* adjointGroup τ L) (hf : Function.Injective f) :
    ∃ j, ∃ g ∈ adjointGroup τ L,
      ∀ a, g * (f a : ModGL τ L) * g⁻¹ = baseChangeGL (algebraMap k L) (t j a) := by
  classical
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots τ)
  choose m β hβ hβr using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
  choose words hwords using fun a : Γ => exists_wordElt_eq (f a)
  let n : Γ → ℕ := fun a => (words a).length
  let ℓ : ∀ a, Fin (n a) → Letter τ := fun a i => ((words a).get i).1
  let c : ∀ a, Fin (n a) → L := fun a i => ((words a).get i).2
  have hc : ∀ a, wordUnit τ L (List.ofFn fun i => (ℓ a i, c a i)) = (f a : ModGL τ L) := by
    intro a
    have hword : (List.ofFn fun i => (ℓ a i, c a i)) = words a := by
      exact List.ofFn_get (words a)
    rw [hword, ← coe_wordElt, hwords a]
  obtain ⟨sep, y, hy⟩ := exists_point_eq (k := k) n ℓ c f hf hc
  let D : J × WeylGroup τ → Type := fun jw => FamilyCoord (k := k) n ℓ sep N (m jw.2)
  let φ : ∀ jw, Coord (k := k) n ℓ sep →ₐ[k] D jw :=
    fun _ => Algebra.TensorProduct.includeLeft
  have hsurj : ∀ y₀ : Coord (k := k) n ℓ sep →ₐ[k] k,
      ∃ jw : J × WeylGroup τ, ∃ x : D jw →ₐ[k] k,
        x.comp (φ jw) = y₀ ∧ ∀ r, x (familyEquations t n ℓ sep α m β jw r) = 0 := by
    intro y₀
    obtain ⟨j, g, hg, hfg⟩ := hbase (pointHom n ℓ sep y₀) (pointHom_injective n ℓ sep y₀)
    obtain ⟨w, z, hz⟩ := exists_bruhatParam ⟨g, hg⟩ α hα hαr m β hβ hβr
    let x : D (j, w) →ₐ[k] k := Algebra.TensorProduct.productMap y₀ z
    have hxL : x.comp (φ (j, w)) = y₀ := Algebra.TensorProduct.productMap_left y₀ z
    have hxR : x.comp Algebra.TensorProduct.includeRight = z :=
      Algebra.TensorProduct.productMap_right y₀ z
    refine ⟨(j, w), x, hxL, ?_⟩
    apply (familyEquations_zero_iff t n ℓ sep α m β (j, w) x).mpr
    intro a
    have hz' : wordUnit τ k (mapWord (z : _ →+* k) (bruhatParamWord τ k w α (β w))) = g := by
      simpa only [coe_wordElt] using congrArg (fun u : adjointGroup τ k => (u : ModGL τ k)) hz
    have hbc : baseChangeGL (algebraMap k k) (t j a) = t j a := by
      apply Units.ext
      apply Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      rw [baseChangeGL_apply_single]
      exact Finsupp.ext fun i => by simp
    rw [hxR, hxL, hbc]
    change wordUnit τ k (mapWord (z : _ →+* k) (bruhatParamWord τ k w α (β w))) *
      (pointHom n ℓ sep y₀ a : ModGL τ k) *
        (wordUnit τ k (mapWord (z : _ →+* k) (bruhatParamWord τ k w α (β w))))⁻¹ = t j a
    rw [hz']
    exact hfg a
  obtain ⟨jw, x, hxy, hx⟩ := exceptional_Lang_affine_equations_field_extension D φ
    (familyEquations t n ℓ sep α m β) hsurj y
  have hconj := (familyEquations_zero_iff t n ℓ sep α m β jw x).mp hx
  let g : adjointGroup τ L := wordElt τ
    (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
      (bruhatParamWord τ k jw.2 α (β jw.2)))
  refine ⟨jw.1, g, g.2, fun a => ?_⟩
  have ha : pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a = f a := by
    rw [show x.comp Algebra.TensorProduct.includeLeft = y from hxy]
    exact hy a
  simpa only [g, coe_wordElt, ha] using hconj a

theorem finite_subgroup_centralizer_field_extension {τ : Tag} {Γ k L : Type}
    [Group Γ] [Fintype Γ] [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L]
    (z : ModGL τ k)
    (hbase : ∀ f : Γ →* adjointGroup τ k, Function.Injective f →
      ∃ g ∈ adjointGroup τ k, ∀ a,
        (g * (f a : ModGL τ k) * g⁻¹) * z =
          z * (g * (f a : ModGL τ k) * g⁻¹))
    (f : Γ →* adjointGroup τ L) (hf : Function.Injective f) :
    ∃ g ∈ adjointGroup τ L, ∀ a,
      (g * (f a : ModGL τ L) * g⁻¹) * baseChangeGL (algebraMap k L) z =
        baseChangeGL (algebraMap k L) z * (g * (f a : ModGL τ L) * g⁻¹) := by
  classical
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots τ)
  choose m β hβ hβr using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
  choose words hwords using fun a : Γ => exists_wordElt_eq (f a)
  let n : Γ → ℕ := fun a => (words a).length
  let ℓ : ∀ a, Fin (n a) → Letter τ := fun a i => ((words a).get i).1
  let c : ∀ a, Fin (n a) → L := fun a i => ((words a).get i).2
  have hc : ∀ a, wordUnit τ L (List.ofFn fun i => (ℓ a i, c a i)) = (f a : ModGL τ L) := by
    intro a
    have hword : (List.ofFn fun i => (ℓ a i, c a i)) = words a := by
      exact List.ofFn_get (words a)
    rw [hword, ← coe_wordElt, hwords a]
  obtain ⟨sep, y, hy⟩ := exists_point_eq (k := k) n ℓ c f hf hc
  let D : WeylGroup τ → Type := fun w => FamilyCoord (k := k) n ℓ sep N (m w)
  let φ : ∀ w, Coord (k := k) n ℓ sep →ₐ[k] D w :=
    fun _ => Algebra.TensorProduct.includeLeft
  have hsurj : ∀ y₀ : Coord (k := k) n ℓ sep →ₐ[k] k,
      ∃ w : WeylGroup τ, ∃ x : D w →ₐ[k] k,
        x.comp (φ w) = y₀ ∧
          ∀ r, x (centralizerEquations z n ℓ sep α m β w r) = 0 := by
    intro y₀
    obtain ⟨g, hg, hgz⟩ := hbase (pointHom n ℓ sep y₀) (pointHom_injective n ℓ sep y₀)
    obtain ⟨w, zparam, hzparam⟩ := exists_bruhatParam ⟨g, hg⟩ α hα hαr m β hβ hβr
    let x : D w →ₐ[k] k := Algebra.TensorProduct.productMap y₀ zparam
    have hxL : x.comp Algebra.TensorProduct.includeLeft = y₀ :=
      Algebra.TensorProduct.productMap_left y₀ zparam
    have hxR : x.comp Algebra.TensorProduct.includeRight = zparam :=
      Algebra.TensorProduct.productMap_right y₀ zparam
    refine ⟨w, x, ?_, ?_⟩
    · simpa only [φ] using hxL
    · apply (centralizerEquations_zero_iff z n ℓ sep α m β w x).mpr
      intro a
      have hz' : (wordUnit τ k (mapWord (zparam : TorusAffine k τ.rank (N + m w) →+* k)
          (bruhatParamWord τ k w α (β w))) : (Module.End k (RootModule τ k))ˣ) =
          (g : (Module.End k (RootModule τ k))ˣ) := by
        have h := congrArg (fun u : adjointGroup τ k => (u : ModGL τ k)) hzparam
        rw [coe_wordElt] at h
        exact h
      have hbc : baseChangeGL (algebraMap k k) z = z := by
        apply Units.ext
        apply Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
        simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
        rw [baseChangeGL_apply_single]
        exact Finsupp.ext fun i => by simp
      simp only [pointConjUnit, hxL, hxR, AlgHom.toRingHom_eq_coe]
      rw [hz', hbc]
      exact hgz a
  obtain ⟨w, x, hxy, hx⟩ := exceptional_Lang_affine_equations_field_extension D φ
    (centralizerEquations z n ℓ sep α m β) hsurj y
  have hconj := (centralizerEquations_zero_iff z n ℓ sep α m β w x).mp hx
  let g : adjointGroup τ L := wordElt τ
    (mapWord (x.comp Algebra.TensorProduct.includeRight).toRingHom
      (bruhatParamWord τ k w α (β w)))
  refine ⟨g, g.2, fun a => ?_⟩
  have ha : pointHom n ℓ sep (x.comp Algebra.TensorProduct.includeLeft) a = f a := by
    rw [show x.comp Algebra.TensorProduct.includeLeft = y from hxy]
    exact hy a
  simpa only [g, coe_wordElt, ha, pointConjUnit] using hconj a

end CFSG.LieType.AlgebraicGroups
