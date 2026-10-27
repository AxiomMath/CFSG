module

public import CFSG.Adapters.TauCetiExceptional.BigCellOp
public import CFSG.Adapters.TauCetiExceptional.BigCellPeel

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint MvPolynomial

variable (τ : Tag)

abbrev BigCellParam : Type := Fin (nPos τ) ⊕ Fin (nPos τ) ⊕ Fin τ.rank

@[expose] def charMonomial : MvPolynomial (BigCellParam τ) ℤ :=
  ∏ i, X (Sum.inr (Sum.inr i))

abbrev GenRing : Type := Localization.Away (charMonomial τ)

@[expose] def genCm (j : Fin (nPos τ)) : GenRing τ :=
  algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) (X (Sum.inl j))

@[expose] def genCp (j : Fin (nPos τ)) : GenRing τ :=
  algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) (X (Sum.inr (Sum.inl j)))

theorem isUnit_genA (k : Fin τ.rank) :
    IsUnit (algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ)
      (X (Sum.inr (Sum.inr k)))) :=
  IsLocalization.Away.isUnit_of_dvd (x := charMonomial τ) (by
    rw [charMonomial]
    exact Finset.dvd_prod_of_mem (fun i => X (Sum.inr (Sum.inr i))) (Finset.mem_univ k))

@[expose] def genA (k : Fin τ.rank) : (GenRing τ)ˣ :=
  (isUnit_genA τ k).unit

@[expose] def genMat
    : Matrix (Fin (nLab τ)) (Fin (nLab τ)) (GenRing τ) :=
  bigCellMat (genCm τ) (genA τ) (genCp τ)

theorem isUnit_bigCellDet_genMat
    : IsUnit (bigCellDet (genMat τ)) :=
  isUnit_bigCellDet_bigCellMat _ _ _

variable {τ}

theorem isUnit_eval₂Hom_charMonomial {K : Type} [CommRing K] (cm cp : Fin (nPos τ) → K)
    (a : Fin τ.rank → Kˣ) :
    IsUnit (eval₂Hom (Int.castRingHom K) (Sum.elim cm (Sum.elim cp fun k => (a k : K)))
      (charMonomial τ)) := by
  rw [charMonomial, map_prod]
  exact IsUnit.prod_univ_iff.2 fun k => by
    rw [eval₂Hom_X']
    exact (a k).isUnit

@[expose] def specialize {K : Type} [CommRing K] (cm : Fin (nPos τ) → K) (a : Fin τ.rank → Kˣ)
    (cp : Fin (nPos τ) → K) : GenRing τ →+* K :=
  IsLocalization.Away.lift (charMonomial τ) (isUnit_eval₂Hom_charMonomial cm cp a)

variable {K : Type} [CommRing K] (cm : Fin (nPos τ) → K) (a : Fin τ.rank → Kˣ)
  (cp : Fin (nPos τ) → K)

theorem specialize_algebraMap (p : MvPolynomial (BigCellParam τ) ℤ) :
    specialize cm a cp (algebraMap _ _ p) =
      eval₂Hom (Int.castRingHom K) (Sum.elim cm (Sum.elim cp fun k => (a k : K))) p :=
  IsLocalization.Away.lift_eq _ _ _

theorem specialize_genCm (j : Fin (nPos τ)) : specialize cm a cp (genCm τ j) = cm j := by
  rw [genCm, specialize_algebraMap, eval₂Hom_X']
  rfl

theorem specialize_genCp (j : Fin (nPos τ)) : specialize cm a cp (genCp τ j) = cp j := by
  rw [genCp, specialize_algebraMap, eval₂Hom_X']
  rfl

theorem specialize_genA (k : Fin τ.rank) :
    Units.map (specialize cm a cp).toMonoidHom (genA τ k) = a k := by
  refine Units.ext ?_
  change specialize cm a cp (algebraMap _ _ (X (Sum.inr (Sum.inr k)))) = _
  rw [specialize_algebraMap, eval₂Hom_X']
  rfl

theorem mapMatrix_specialize_genMat :
    (specialize cm a cp).mapMatrix (genMat τ) = bigCellMat cm a cp := by
  rw [genMat, mapMatrix_bigCellMat]
  have h1 : (fun j => specialize cm a cp (genCm τ j)) = cm := funext (specialize_genCm cm a cp)
  have h2 : (fun k => Units.map (specialize cm a cp).toMonoidHom (genA τ k)) = a :=
    funext (specialize_genA cm a cp)
  have h3 : (fun j => specialize cm a cp (genCp τ j)) = cp := funext (specialize_genCp cm a cp)
  rw [h1, h2, h3]

theorem integralIn_canonicalRep
    {R : Type} [CommRing R] (S : Subring R) (w : WeylGroup τ) :
    IntegralIn S (canonicalRep (coxeterSystem τ) R w : Module.End R (RootModule τ R)) :=
  integralIn_of_baseChange S (baseChange_canonicalRep (Int.castRingHom R) w)

theorem integralIn_canonicalRep_inv
    {R : Type} [CommRing R] (S : Subring R) (w : WeylGroup τ) :
    IntegralIn S (((canonicalRep (coxeterSystem τ) R w)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) :=
  integralIn_of_baseChange S
    (BaseChange.units_inv (baseChange_canonicalRep (Int.castRingHom R) w))

theorem coe_genA (k : Fin τ.rank) :
    (genA τ k : GenRing τ) =
      algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) (X (Sum.inr (Sum.inr k))) :=
  IsUnit.unit_spec _

theorem eq_top_of_mem_gen (T : Subring (GenRing τ)) (hcm : ∀ j, genCm τ j ∈ T)
    (hcp : ∀ j, genCp τ j ∈ T)
    (ha : ∀ k, (genA τ k : GenRing τ) ∈ T ∧ (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ) ∈ T) :
    T = ⊤ := by
  have hpoly : ∀ q : MvPolynomial (BigCellParam τ) ℤ,
      algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) q ∈ T := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C z =>
      rw [show (C z : MvPolynomial (BigCellParam τ) ℤ) = (z : MvPolynomial (BigCellParam τ) ℤ)
        from eq_intCast C z, map_intCast]
      exact intCast_mem T z
    | add p q hp hq =>
      rw [map_add]
      exact T.add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine T.mul_mem hp ?_
      rcases v with j | j | k
      · exact hcm j
      · exact hcp j
      · rw [← coe_genA]
        exact (ha k).1
  have hM : algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) (charMonomial τ) *
      ∏ k, (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ) = 1 := by
    have hMp : algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) (charMonomial τ) =
        ∏ k, (genA τ k : GenRing τ) := by
      simp only [coe_genA]
      exact map_prod (algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ))
        (fun i => X (Sum.inr (Sum.inr i))) Finset.univ
    rw [hMp, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => Units.mul_inv _
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (charMonomial τ) x
  have hx : x = algebraMap (MvPolynomial (BigCellParam τ) ℤ) (GenRing τ) p *
      (∏ k, (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ)) ^ n := by
    rw [← hp, mul_assoc, ← mul_pow, hM, one_pow, mul_one]
  rw [hx]
  exact T.mul_mem (hpoly p) (T.pow_mem (T.prod_mem fun k _ => (ha k).2) n)

theorem eq_top_of_genMat
    (T : Subring (GenRing τ)) (hT : ∀ i j, genMat τ i j ∈ T)
    (hinv : ∃ y ∈ T, y * bigCellDet (genMat τ) = 1) : T = ⊤ := by
  have hmem := (isLDU_bigCellMat (genCm τ) (genA τ) (genCp τ)).mem T hT hinv
  have hcp : ∀ j, genCp τ j ∈ T := mem_of_integralIn_prod_ofFn_pinnedX T (posRootEnum τ)
    (posRootEnum_injective τ) (posRootEnum_pos τ) (genCp τ) fun i j => (hmem i).2.2.2 j
  have hl : IntegralIn T (((nLong (GenRing τ))⁻¹ * uProd (GenRing τ) (genCm τ) *
      nLong (GenRing τ) : (Module.End (GenRing τ) (RootModule τ (GenRing τ)))ˣ) :
        Module.End (GenRing τ) (RootModule τ (GenRing τ))) := fun i j => (hmem j).2.2.1 i
  have hu : IntegralIn T (uProd (GenRing τ) (genCm τ) :
      Module.End (GenRing τ) (RootModule τ (GenRing τ))) := by
    have e : uProd (GenRing τ) (genCm τ) = nLong (GenRing τ) *
        ((nLong (GenRing τ))⁻¹ * uProd (GenRing τ) (genCm τ) * nLong (GenRing τ)) *
          (nLong (GenRing τ))⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact ((integralIn_canonicalRep T _).mul hl).mul (integralIn_canonicalRep_inv T _)
  have hcm : ∀ j, genCm τ j ∈ T := mem_of_integralIn_prod_ofFn_pinnedX T (posRootEnum τ)
    (posRootEnum_injective τ) (posRootEnum_pos τ) (genCm τ) hu
  have ha : ∀ k, (genA τ k : GenRing τ) ∈ T ∧ (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ) ∈ T := by
    intro k
    obtain ⟨⟨y, hy, hyd⟩, hd, -, -⟩ :=
      hmem (posEquiv τ (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩))
    rw [charDiag_simple] at hyd hd
    refine ⟨hd, ?_⟩
    have e : y = (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ) := by
      calc y = y * ((genA τ k : GenRing τ) * (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ)) := by
            rw [Units.mul_inv, mul_one]
        _ = y * (genA τ k : GenRing τ) * (((genA τ k)⁻¹ : (GenRing τ)ˣ) : GenRing τ) := by ring
        _ = _ := by rw [hyd, one_mul]
    rw [← e]
    exact hy
  exact eq_top_of_mem_gen T hcm hcp ha

end CFSG.TauCetiBridge.BigCell
