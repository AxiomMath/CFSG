module

public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.Adapters.TauCetiExceptional.BigCellLDU
public import CFSG.Adapters.TauCetiExceptional.BigCellNative
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (τ : Tag)

abbrev posRoots : Set (Fin τ.rank → ℤ) := {β | IsRoot τ β ∧ 0 < height β}

abbrev nPos : ℕ := (posRoots τ).ncard

theorem posRoots_finite : (posRoots τ).Finite :=
  finite_of_forall_isRoot_pos fun _ h => h

@[expose] def posRootEnum : Fin (nPos τ) → Fin τ.rank → ℤ :=
  (exists_rootEnum (posRoots_finite τ)).choose

theorem posRootEnum_injective : Function.Injective (posRootEnum τ) :=
  (exists_rootEnum (posRoots_finite τ)).choose_spec.1

theorem range_posRootEnum : Set.range (posRootEnum τ) = posRoots τ :=
  (exists_rootEnum (posRoots_finite τ)).choose_spec.2

theorem posRootEnum_pos (j : Fin (nPos τ)) :
    IsRoot τ (posRootEnum τ j) ∧ 0 < height (posRootEnum τ j) := by
  have h : posRootEnum τ j ∈ posRoots τ := range_posRootEnum τ ▸ Set.mem_range_self j
  exact h

@[expose] def longest : WeylGroup τ :=
  (Finite.exists_max (coxeterSystem τ).length).choose

theorem reversesSigns_longest :
    ReversesSigns (longest τ) :=
  reversesSigns_of_forall_length_le (Finite.exists_max (coxeterSystem τ).length).choose_spec

theorem image_longest_negRoots :
    (fun α => longest τ • α) '' {α | IsRoot τ α ∧ height α < 0} = posRoots τ := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hneg⟩, rfl⟩
    exact ⟨IsRoot.smul hα _, (reversesSigns_longest τ).height_smul_pos hα hneg⟩
  · rintro ⟨hβ, hpos⟩
    refine ⟨(longest τ)⁻¹ • β, ⟨IsRoot.smul hβ _, (reversesSigns_longest τ).inv β hβ hpos⟩, ?_⟩
    simp only [smul_inv_smul]

variable {τ} (R : Type) [CommRing R]

abbrev nLong
    : (Module.End R (RootModule τ R))ˣ :=
  canonicalRep (coxeterSystem τ) R (longest τ)

@[expose] def uProd
    (c : Fin (nPos τ) → R) : (Module.End R (RootModule τ R))ˣ :=
  (List.ofFn fun j => pinnedX τ R (posRootEnum τ j) (c j)).prod

variable {R}

theorem uProd_mem_posUnipotent
    (c : Fin (nPos τ) → R) : uProd R c ∈ posUnipotent τ R :=
  list_prod_mem fun _ hx => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    have hle : rootSubgroup τ R (posRootEnum τ j) ≤ posUnipotent τ R :=
      le_iSup₂_of_le (posRootEnum τ j) (posRootEnum_pos τ j) le_rfl
    exact hle (Subgroup.subset_closure ⟨c j, rfl⟩)

theorem conj_mem_negUnipotent
    {u : (Module.End R (RootModule τ R))ˣ}
    (hu : u ∈ posUnipotent τ R) : (nLong R)⁻¹ * u * nLong R ∈ negUnipotent τ R := by
  have h := (canonical_weyl_root_transport τ R).1 (longest τ) {α | IsRoot τ α ∧ height α < 0}
    fun α hα => hα.1
  rw [image_longest_negRoots] at h
  have hu' : u ∈ (rootSpan τ R {α | IsRoot τ α ∧ height α < 0}).map
      (MulAut.conj (nLong R)).toMonoidHom := by
    rw [h]
    exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  exact hv

theorem baseChange_list_prod
    {S : Type*} [CommRing S] {f : R →+* S} {ι : Type*}
    (A : ι → (Module.End R (RootModule τ R))ˣ) (B : ι → (Module.End S (RootModule τ S))ˣ)
    (h : ∀ i, BaseChange f (A i : Module.End R (RootModule τ R))
      (B i : Module.End S (RootModule τ S))) (L : List ι) :
    BaseChange f (((L.map A).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R))
      (((L.map B).prod : (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction L with
  | nil => simpa using BaseChange.one (τ := τ) (f := f)
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact (h i).mul ih

theorem baseChange_uProd
    {S : Type} [CommRing S] (f : R →+* S) (c : Fin (nPos τ) → R) :
    BaseChange f (uProd R c : Module.End R (RootModule τ R))
      (uProd S (fun j => f (c j)) : Module.End S (RootModule τ S)) := by
  rw [uProd, uProd, List.ofFn_eq_map, List.ofFn_eq_map]
  exact baseChange_list_prod _ _ (fun j => baseChange_pinnedX f _ _) _

theorem baseChange_canonicalRep
    {S : Type*} [CommRing S] (f : R →+* S) (w : WeylGroup τ) :
    BaseChange f (canonicalRep (coxeterSystem τ) R w : Module.End R (RootModule τ R))
      (canonicalRep (coxeterSystem τ) S w : Module.End S (RootModule τ S)) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, canonicalRep_wordProd hω]
  exact BaseChange.prod_weylElt ω

@[expose] def charDiag
    (a : Fin τ.rank → Rˣ) : Matrix (Fin (nLab τ)) (Fin (nLab τ)) R :=
  Matrix.diagonal fun i => ((∏ k, a k ^ labelWt τ ((posEquiv τ).symm i) k : Rˣ) : R)

theorem mapMatrix_charDiag
    {S : Type} [CommRing S] (f : R →+* S) (a : Fin τ.rank → Rˣ) :
    f.mapMatrix (charDiag a) = charDiag fun k => Units.map f.toMonoidHom (a k) := by
  ext i j
  simp only [charDiag, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [Units.coe_prod, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← map_zpow, Units.coe_map]
    rfl
  · exact map_zero f

theorem charDiag_simple (a : Fin τ.rank → Rˣ) (k : Fin τ.rank) :
    charDiag a (posEquiv τ (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩))
      (posEquiv τ (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩)) = (a k : R) := by
  rw [charDiag, Matrix.diagonal_apply_eq, Equiv.symm_apply_apply]
  congr 1
  change ∏ i, a i ^ (Pi.single k 1 : Fin τ.rank → ℤ) i = a k
  rw [Finset.prod_eq_single k (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zpow_zero])
    (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, zpow_one]

theorem natMat_rootDiagUnit
    {K : Type} [Field K] (a : Fin τ.rank → Kˣ) :
    natMat τ K (rootDiagUnit τ a : Module.End K (RootModule τ K)) = charDiag a := by
  ext i j
  rw [natMat_apply]
  change FourGroupChevalley.rootDiag a _ _ = _
  rw [FourGroupChevalley.rootDiag_single, Finsupp.smul_apply, charDiag, Matrix.diagonal_apply,
    Finsupp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
    rfl
  · have hne : (posEquiv τ).symm j ≠ (posEquiv τ).symm i := fun e => hij
      ((posEquiv τ).symm.injective e).symm
    rw [ite_eq_right hne, ite_eq_right hij, mul_zero]

@[expose] def bigCellMat
    (cm : Fin (nPos τ) → R) (a : Fin τ.rank → Rˣ) (cp : Fin (nPos τ) → R) :
    Matrix (Fin (nLab τ)) (Fin (nLab τ)) R :=
  natMat τ R (((nLong R)⁻¹ * uProd R cm * nLong R : (Module.End R (RootModule τ R))ˣ) :
    Module.End R (RootModule τ R)) * charDiag a * natMat τ R (uProd R cp)

theorem isLDU_bigCellMat
    (cm : Fin (nPos τ) → R) (a : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) :
    IsLDU (natMat τ R (((nLong R)⁻¹ * uProd R cm * nLong R :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)))
      (charDiag a) (natMat τ R (uProd R cp)) where
  l_one := (natMat_negUnipotent (conj_mem_negUnipotent (uProd_mem_posUnipotent cm))).1
  l_zero := (natMat_negUnipotent (conj_mem_negUnipotent (uProd_mem_posUnipotent cm))).2
  d_zero _ _ hij := Matrix.diagonal_apply_ne _ hij
  u_one := (natMat_posUnipotent (uProd_mem_posUnipotent cp)).1
  u_zero := (natMat_posUnipotent (uProd_mem_posUnipotent cp)).2

theorem isUnit_bigCellDet_bigCellMat
    (cm : Fin (nPos τ) → R) (a : Fin τ.rank → Rˣ)
    (cp : Fin (nPos τ) → R) : IsUnit (bigCellDet (bigCellMat cm a cp)) := by
  rw [bigCellMat, bigCellDet]
  refine IsUnit.prod_univ_iff.2 fun i => ?_
  rw [(isLDU_bigCellMat cm a cp).leadMinor_eq]
  refine IsUnit.prod_iff.2 fun j _ => ?_
  rw [charDiag, Matrix.diagonal_apply_eq]
  exact Units.isUnit _

theorem mapMatrix_bigCellMat
    {S : Type} [CommRing S] (f : R →+* S) (cm : Fin (nPos τ) → R)
    (a : Fin τ.rank → Rˣ) (cp : Fin (nPos τ) → R) :
    f.mapMatrix (bigCellMat cm a cp) =
      bigCellMat (fun j => f (cm j)) (fun k => Units.map f.toMonoidHom (a k))
        (fun j => f (cp j)) := by
  rw [bigCellMat, bigCellMat, map_mul, map_mul, mapMatrix_charDiag]
  have h1 := ((BaseChange.units_inv (baseChange_canonicalRep f (longest τ))).mul
    (baseChange_uProd f cm)).mul (baseChange_canonicalRep f (longest τ))
  rw [← natMat_of_baseChange (baseChange_uProd f cp)]
  simp only [Units.val_mul]
  rw [← natMat_of_baseChange h1]

theorem bigCellMat_eq_natMat
    {K : Type} [Field K] (cm : Fin (nPos τ) → K) (a : Fin τ.rank → Kˣ)
    (cp : Fin (nPos τ) → K) :
    bigCellMat cm a cp = natMat τ K (((nLong K)⁻¹ * uProd K cm * nLong K * rootDiagUnit τ a *
      uProd K cp : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) := by
  simp only [bigCellMat, Units.val_mul, map_mul, natMat_rootDiagUnit]

end CFSG.TauCetiBridge.BigCell
