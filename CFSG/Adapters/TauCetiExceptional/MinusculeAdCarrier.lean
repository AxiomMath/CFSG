module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdPoly
public import CFSG.Adapters.TauCetiExceptional.BigCellPoints
public import CFSG.Adapters.TauCetiExceptional.MinusculeCore
public import CFSG.Adapters.TauCetiExceptional.MinusculeDet

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData
open CFSG.TauCetiBridge.BigCell (evalMat VanishesOnRat evalMat_mapMatrix)

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
  {S : AdjSigns τ} (hS : S.check D = true) {n : ℕ} (lab : Fin n ≃ Fin D.d)

omit hV in
theorem natMat_symm_toMat
    {R : Type*} [CommRing R] (z : Matrix.GeneralLinearGroup (Fin n) R) :
    natMat R (((toMat lab R).symm z : (Module.End R (Fin D.d →₀ R))ˣ) :
      Module.End R (Fin D.d →₀ R)) =
        (z : Matrix (Fin n) (Fin n) R).submatrix lab.symm lab.symm := by
  ext r s
  rw [natMat_apply, Matrix.submatrix_apply]
  conv_rhs => rw [← (toMat lab R).apply_symm_apply z]
  rw [toMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[expose] def IsZeroOfIdentities
    {A : Type} [CommRing A] (M : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ P : MvPolynomial (Fin n × Fin n) ℤ,
    (∀ g : hV.minGroup ℚ, evalMat ((toMat lab ℚ g : Matrix.GeneralLinearGroup (Fin n) ℚ) :
      Matrix (Fin n) (Fin n) ℚ) P = 0) → evalMat M P = 0

variable {hV lab}

theorem IsZeroOfIdentities.submatrix
    {A : Type} [CommRing A] {M : Matrix (Fin n) (Fin n) A}
    (hM : IsZeroOfIdentities hV lab M) (P : MvPolynomial (Fin D.d × Fin D.d) ℤ)
    (hP : ∀ N ∈ ratMats hV, evalMat N P = 0) : evalMat (M.submatrix lab.symm lab.symm) P = 0 := by
  set f : Fin D.d × Fin D.d → Fin n × Fin n := fun ab => (lab.symm ab.1, lab.symm ab.2)
  have h1 := hM (MvPolynomial.rename f P) fun g => by
    rw [evalMat_rename, ← hP _ ⟨g, rfl⟩, ← submatrix_toMat hV lab ℚ g]
    rfl
  rw [evalMat_rename] at h1
  exact h1

theorem IsZeroOfIdentities.det_eq_one
    {A : Type} [CommRing A] {M : Matrix (Fin n) (Fin n) A}
    (hM : IsZeroOfIdentities hV lab M) : (M.submatrix lab.symm lab.symm).det = 1 := by
  refine sub_eq_zero.1 (natural_eq_zero (fun A _ N => N.det - 1) (fun A B _ _ f N => by
    rw [map_sub, RingHom.map_det, map_one]) (ratMats hV) ?_ _ hM.submatrix)
  rintro _ ⟨g, rfl⟩
  rw [det_natMat_eq_one hV ℚ g, sub_self]

include hpd in
theorem IsZeroOfIdentities.conjMat_eq
    {A : Type} [CommRing A] {M : Matrix (Fin n) (Fin n) A}
    (hM : IsZeroOfIdentities hV lab M) (hS : S.check D = true) (l : Label τ) :
    conjMat S (M.submatrix lab.symm lab.symm) l =
      projMat (S := S) (conjMat S (M.submatrix lab.symm lab.symm) l) := by
  ext r s
  refine sub_eq_zero.1 (natural_eq_zero
    (fun A _ N => conjMat S N l r s - projMat (S := S) (conjMat S N l) r s)
    (fun A B _ _ f N => ?_) (ratMats hV) ?_ _ hM.submatrix)
  · rw [map_sub, ← mapMatrix_conjMat S f N l, ← mapMatrix_projMat f]
    rfl
  · rintro _ ⟨g, rfl⟩
    rw [← conjMat_eq_projMat S hV hpd (minGroup_le_adjNormalizer hV hpd hS ℚ g.2)
      (det_natMat_eq_one hV ℚ g), sub_self]

include hpd in
theorem IsZeroOfIdentities.vanishes
    {A : Type} [CommRing A] {M : Matrix (Fin n) (Fin n) A}
    (hM : IsZeroOfIdentities hV lab M) (hS : S.check D = true)
    (P : MvPolynomial (Fin (BigCell.nLab τ) × Fin (BigCell.nLab τ)) ℤ) (hP : VanishesOnRat τ P) :
    evalMat (adMat S (M.submatrix lab.symm lab.symm)) P = 0 := by
  refine natural_eq_zero (fun A _ N => evalMat (adMat S N) P) (fun A B _ _ f N => ?_)
    (ratMats hV) ?_ _ hM.submatrix
  · rw [← mapMatrix_adMat S f N, evalMat_mapMatrix, RingHom.comp_apply]
  · rintro _ ⟨g, rfl⟩
    have h := adMat_natMat S hV hpd ⟨_, minGroup_le_adjNormalizer hV hpd hS ℚ g.2⟩
      (det_natMat_eq_one hV ℚ g)
    refine (congrArg (fun N => evalMat N P) h).trans (hP _ ?_)
    rw [← range_adMin hV hpd hS ℚ]
    exact ⟨g, rfl⟩

omit hV in
theorem natMat_eq_submatrix
    {R : Type*} [CommRing R] (g : (Module.End R (Fin D.d →₀ R))ˣ) :
    natMat R (g : Module.End R (Fin D.d →₀ R)) =
      ((toMat lab R g : Matrix.GeneralLinearGroup (Fin n) R) :
        Matrix (Fin n) (Fin n) R).submatrix lab.symm lab.symm := by
  have := natMat_symm_toMat lab (toMat lab R g)
  rwa [MulEquiv.symm_apply_apply] at this

variable {L : Type} [Field L]

include hpd hS in
theorem exists_conj_eq_adjMap
    (g : (Module.End L (Fin D.d →₀ L))ˣ)
    (hg : IsZeroOfIdentities hV lab ((toMat lab L g : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L)) (v : RootModule τ L) :
    ∃ w, (g : Module.End L (Fin D.d →₀ L)) * adjMap L S D v *
      ((g⁻¹ : (Module.End L (Fin D.d →₀ L))ˣ) : Module.End L (Fin D.d →₀ L)) = adjMap L S D w := by
  have hdet : (natMat L (g : Module.End L (Fin D.d →₀ L))).det = 1 := by
    rw [natMat_eq_submatrix (lab := lab)]
    exact hg.det_eq_one
  have hl : ∀ l, ∃ w, (g : Module.End L (Fin D.d →₀ L)) * adjMap L S D (Finsupp.single l 1) *
      ((g⁻¹ : (Module.End L (Fin D.d →₀ L))ˣ) : Module.End L (Fin D.d →₀ L)) =
        adjMap L S D w := by
    intro l
    refine ⟨adjInv L S D ((g : Module.End L (Fin D.d →₀ L)) * adjMap L S D (Finsupp.single l 1) *
      ((g⁻¹ : (Module.End L (Fin D.d →₀ L))ˣ) : Module.End L (Fin D.d →₀ L))), ?_⟩
    refine (natMat L).injective ?_
    rw [natMat_adjMap_adjInv, ← conjMat_natMat S g hdet, natMat_eq_submatrix (lab := lab)]
    exact hg.conjMat_eq hpd hS l
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [map_zero, mul_zero, zero_mul]⟩
  | add v w hv hw =>
    obtain ⟨a, ha⟩ := hv
    obtain ⟨b, hb⟩ := hw
    exact ⟨a + b, by rw [map_add, mul_add, add_mul, ha, hb, map_add]⟩
  | single l c =>
    obtain ⟨w, hw⟩ := hl l
    exact ⟨c • w, by
      rw [← Finsupp.smul_single_one, map_smul, mul_smul_comm, smul_mul_assoc, hw, map_smul]⟩

include hpd hS in
theorem mem_adjNormalizer_of_identities
    (g : (Module.End L (Fin D.d →₀ L))ˣ)
    (hg : IsZeroOfIdentities hV lab ((toMat lab L g : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L))
    (hg' : IsZeroOfIdentities hV lab ((toMat lab L g⁻¹ : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L)) : g ∈ adjNormalizer L S D :=
  ⟨exists_conj_eq_adjMap hpd hS g hg, fun v => by
    simpa only [inv_inv] using exists_conj_eq_adjMap hpd hS g⁻¹ hg' v⟩

variable (hV lab L) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L))
  (hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L))

include hpd hS hH in
theorem symm_toMat_mem (z : H) :
    (toMat lab L).symm (z : Matrix.GeneralLinearGroup (Fin n) L) ∈ adjNormalizer L S D :=
  mem_adjNormalizer_of_identities hpd hS _ (by rw [MulEquiv.apply_symm_apply]; exact hH _ z.2)
    (by rw [map_inv, MulEquiv.apply_symm_apply]; exact hH _ (H.inv_mem z.2))

@[expose] def adCarrier : H →* ModGL τ L :=
  (ad hV hpd S).comp ((((toMat lab L).symm : Matrix.GeneralLinearGroup (Fin n) L →*
    (Module.End L (Fin D.d →₀ L))ˣ).comp H.subtype).codRestrict (adjNormalizer L S D)
      (symm_toMat_mem hV hpd hS lab L H hH))

theorem adCarrier_apply (z : H) :
    adCarrier hV hpd hS lab L H hH z =
      ad hV hpd S ⟨(toMat lab L).symm z, symm_toMat_mem hV hpd hS lab L H hH z⟩ :=
  rfl

theorem adCarrier_rootUnit_single (i : Fin τ.rank) (c : L)
    (h : toMat lab L (rootUnit hV L (Pi.single i 1) c) ∈ H) :
    adCarrier hV hpd hS lab L H hH ⟨_, h⟩ = xUnit τ L i c := by
  rw [adCarrier_apply, ← ad_rootUnit_single hV hpd hS i c]
  congr 1
  exact Subtype.ext (MulEquiv.symm_apply_apply _ _)

theorem adCarrier_rootUnit_neg_single (i : Fin τ.rank) (c : L)
    (h : toMat lab L (rootUnit hV L (-Pi.single i 1) c) ∈ H) :
    adCarrier hV hpd hS lab L H hH ⟨_, h⟩ = yUnit τ L i c := by
  rw [adCarrier_apply, ← ad_rootUnit_neg_single hV hpd hS i c]
  congr 1
  exact Subtype.ext (MulEquiv.symm_apply_apply _ _)

theorem natMat_adCarrier (z : H) :
    BigCell.natMat τ L ((adCarrier hV hpd hS lab L H hH z : ModGL τ L) :
      Module.End L (RootModule τ L)) =
        adMat S (((z : Matrix.GeneralLinearGroup (Fin n) L) :
          Matrix (Fin n) (Fin n) L).submatrix lab.symm lab.symm) := by
  have hdet : (natMat L (((toMat lab L).symm (z : Matrix.GeneralLinearGroup (Fin n) L) :
      (Module.End L (Fin D.d →₀ L))ˣ) : Module.End L (Fin D.d →₀ L))).det = 1 := by
    rw [natMat_symm_toMat lab]
    exact (hH _ z.2).det_eq_one
  rw [adCarrier_apply, ← adMat_natMat S hV hpd
    ⟨(toMat lab L).symm z, symm_toMat_mem hV hpd hS lab L H hH z⟩ hdet, natMat_symm_toMat lab]

theorem vanishes_adCarrier
    (z : H)
    (P : MvPolynomial (Fin (BigCell.nLab τ) × Fin (BigCell.nLab τ)) ℤ) (hP : VanishesOnRat τ P) :
    evalMat (BigCell.natMat τ L ((adCarrier hV hpd hS lab L H hH z : ModGL τ L) :
      Module.End L (RootModule τ L))) P = 0 := by
  rw [natMat_adCarrier]
  exact (hH _ z.2).vanishes hpd hS P hP

end CFSG.TauCetiBridge.Minuscule
