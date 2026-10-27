module

public import CFSG.Adapters.TauCetiExceptional.MinusculeCell
public import CFSG.Adapters.TauCetiExceptional.BigCellGeneric

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell

variable (τ : Tag)

@[expose] def posList : List (Fin (nPos τ)) :=
  (List.finRange (nPos τ)).mergeSort fun j j' =>
    decide (height (posRootEnum τ j) ≤ height (posRootEnum τ j'))

theorem posList_perm : (posList τ).Perm (List.finRange (nPos τ)) :=
  List.mergeSort_perm _ _

theorem posList_nodup : (posList τ).Nodup :=
  (posList_perm τ).nodup_iff.2 (List.nodup_finRange _)

theorem mem_posList (j : Fin (nPos τ)) : j ∈ posList τ :=
  (posList_perm τ).mem_iff.2 (List.mem_finRange j)

theorem posList_sorted :
    (posList τ).Pairwise fun j j' => height (posRootEnum τ j) ≤ height (posRootEnum τ j') := by
  have h := List.pairwise_mergeSort (le := fun j j' : Fin (nPos τ) =>
    decide (height (posRootEnum τ j) ≤ height (posRootEnum τ j'))) (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc) (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) (List.finRange (nPos τ))
  exact h.imp fun hab => by simpa using hab

variable {τ}

variable {D : MinData τ} (hV : D.Valid) (R : Type*) [CommRing R]

@[expose] def uPos
    (c : Fin (nPos τ) → R) : (Module.End R (Fin D.d →₀ R))ˣ :=
  ((posList τ).map fun j => rootUnit hV R (posRootEnum τ j) (c j)).prod

@[expose] def uNeg
    (c : Fin (nPos τ) → R) : (Module.End R (Fin D.d →₀ R))ˣ :=
  ((posList τ).map fun j => rootUnit hV R (-posRootEnum τ j) (c j)).prod

variable {R} in
@[expose] def dT
    (D : MinData τ) (t : Fin τ.rank → Rˣ) : (Module.End R (Fin D.d →₀ R))ˣ :=
  diagUnit fun a => TauCeti.torusCharacter t (D.wt a)

@[expose] def bigCellUnit
    (cm : Fin (nPos τ) → R) (t : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) : (Module.End R (Fin D.d →₀ R))ˣ :=
  uNeg hV R cm * dT D t * uPos hV R cp

theorem natMat_list_prod (l : List (Module.End R (Fin D.d →₀ R))ˣ) :
    natMat R ((l.prod : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) =
      (l.map fun g : (Module.End R (Fin D.d →₀ R))ˣ =>
        natMat R (g : Module.End R (Fin D.d →₀ R))).prod := by
  induction l with
  | nil => simp
  | cons g l ih => rw [List.prod_cons, Units.val_mul, map_mul, ih, List.map_cons, List.prod_cons]

theorem isUpperUni_natMat_uPos
    (hord : DegOrdered D) (c : Fin (nPos τ) → R) :
    IsUpperUni (natMat R (uPos hV R c : Module.End R (Fin D.d →₀ R))) := by
  rw [uPos, natMat_list_prod, List.map_map]
  induction posList τ with
  | nil => exact isUpperUni_one
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (isUpperUni_natMat_rootUnit hV hord R (posRootEnum_pos τ j).1
      (posRootEnum_pos τ j).2 (c j)).mul ih

theorem isLowerUni_natMat_uNeg
    (hord : DegOrdered D) (c : Fin (nPos τ) → R) :
    IsLowerUni (natMat R (uNeg hV R c : Module.End R (Fin D.d →₀ R))) := by
  rw [uNeg, natMat_list_prod, List.map_map]
  induction posList τ with
  | nil => exact isLowerUni_one
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    have hneg : ht (-posRootEnum τ j) < 0 := by
      have := (posRootEnum_pos τ j).2
      simp only [ht, Pi.neg_apply, Finset.sum_neg_distrib, height] at this ⊢
      omega
    exact (isLowerUni_natMat_rootUnit hV hord R
      (CFSG.LieType.Chevalley.IsRoot.neg (posRootEnum_pos τ j).1) hneg
      (c j)).mul ih

theorem isLDU_bigCellUnit
    (hord : DegOrdered D) (cm : Fin (nPos τ) → R) (t : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) :
    IsLDU (natMat R (uNeg hV R cm : Module.End R (Fin D.d →₀ R)))
      (natMat R (dT D t : Module.End R (Fin D.d →₀ R)))
      (natMat R (uPos hV R cp : Module.End R (Fin D.d →₀ R))) where
  l_one := (isLowerUni_natMat_uNeg hV R hord cm).diag
  l_zero := (isLowerUni_natMat_uNeg hV R hord cm).upper
  d_zero i j hij := by
    rw [dT, natMat_diagUnit, Matrix.diagonal_apply_ne _ hij]
  u_one := (isUpperUni_natMat_uPos hV R hord cp).diag
  u_zero := (isUpperUni_natMat_uPos hV R hord cp).lower

theorem natMat_bigCellUnit
    (cm : Fin (nPos τ) → R) (t : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) :
    natMat R (bigCellUnit hV R cm t cp : Module.End R (Fin D.d →₀ R)) =
      natMat R (uNeg hV R cm : Module.End R (Fin D.d →₀ R)) *
        natMat R (dT D t : Module.End R (Fin D.d →₀ R)) *
          natMat R (uPos hV R cp : Module.End R (Fin D.d →₀ R)) := by
  rw [bigCellUnit, Units.val_mul, Units.val_mul, map_mul, map_mul]

theorem isUnit_bigCellDet_bigCellUnit
    (hord : DegOrdered D) (cm : Fin (nPos τ) → R)
    (t : Fin τ.rank → Rˣ) (cp : Fin (nPos τ) → R) :
    IsUnit (bigCellDet (natMat R (bigCellUnit hV R cm t cp : Module.End R (Fin D.d →₀ R)))) := by
  rw [natMat_bigCellUnit, bigCellDet]
  refine IsUnit.prod_univ_iff.2 fun i => ?_
  rw [(isLDU_bigCellUnit hV R hord cm t cp).leadMinor_eq]
  refine IsUnit.prod_iff.2 fun a _ => ?_
  rw [dT, natMat_diagUnit, Matrix.diagonal_apply_eq]
  exact Units.isUnit _

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

theorem mapMatrix_natMat_list_prod_rootUnit
    (l : List (Fin (nPos τ)))
    (γ : Fin (nPos τ) → Fin τ.rank → ℤ) (c : Fin (nPos τ) → R) :
    f.mapMatrix (natMat R ((((l.map fun j => rootUnit hV R (γ j) (c j)).prod :
        (Module.End R (Fin D.d →₀ R))ˣ)) : Module.End R (Fin D.d →₀ R))) =
      natMat S ((((l.map fun j => rootUnit hV S (γ j) (f (c j))).prod :
        (Module.End S (Fin D.d →₀ S))ˣ)) : Module.End S (Fin D.d →₀ S)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul, map_mul]
    rw [ih, mapMatrix_natMat_rootUnit]

theorem mapMatrix_natMat_dT
    (t : Fin τ.rank → Rˣ) :
    f.mapMatrix (natMat R (dT D t : Module.End R (Fin D.d →₀ R))) =
      natMat S (dT D (fun k => Units.map (f : R →* S) (t k)) : Module.End S (Fin D.d →₀ S)) := by
  rw [dT, dT, natMat_diagUnit, natMat_diagUnit]
  ext r s
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rw [← TauCeti.map_torusCharacter]
    rfl
  · exact map_zero f

theorem mapMatrix_natMat_bigCellUnit
    (cm : Fin (nPos τ) → R) (t : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) :
    f.mapMatrix (natMat R (bigCellUnit hV R cm t cp : Module.End R (Fin D.d →₀ R))) =
      natMat S (bigCellUnit hV S (fun j => f (cm j)) (fun k => Units.map (f : R →* S) (t k))
        (fun j => f (cp j)) : Module.End S (Fin D.d →₀ S)) := by
  rw [natMat_bigCellUnit, natMat_bigCellUnit, map_mul, map_mul, mapMatrix_natMat_dT, uNeg, uPos,
    uNeg, uPos, mapMatrix_natMat_list_prod_rootUnit, mapMatrix_natMat_list_prod_rootUnit]

@[expose] def minGenMat :
    Matrix (Fin D.d) (Fin D.d) (GenRing τ) :=
  natMat (GenRing τ)
    (bigCellUnit hV (GenRing τ) (genCm τ) (genA τ) (genCp τ) : Module.End _ (Fin D.d →₀ _))

theorem mapMatrix_specialize_minGenMat
    {K : Type} [CommRing K] (cm : Fin (nPos τ) → K)
    (a : Fin τ.rank → Kˣ) (cp : Fin (nPos τ) → K) :
    (specialize cm a cp).mapMatrix (minGenMat hV) =
      natMat K (bigCellUnit hV K cm a cp : Module.End K (Fin D.d →₀ K)) := by
  rw [minGenMat, mapMatrix_natMat_bigCellUnit]
  have h1 : (fun j => specialize cm a cp (genCm τ j)) = cm := funext (specialize_genCm cm a cp)
  have h2 : (fun k => Units.map (specialize cm a cp : GenRing τ →* K) (genA τ k)) = a :=
    funext (specialize_genA cm a cp)
  have h3 : (fun j => specialize cm a cp (genCp τ j)) = cp := funext (specialize_genCp cm a cp)
  rw [h1, h2, h3]

end CFSG.TauCetiBridge.Minuscule
