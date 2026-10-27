module

public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
public import CFSG.CharacterTheory.Semidihedral.FixedFieldCentralizerGamma

public section

namespace CFSG.Semidihedral.FixedFieldCentralizer

noncomputable section

set_option maxHeartbeats 800000

open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.FixedFieldData
open CFSG.Semidihedral.OddFieldLift
open scoped MatrixGroups Pointwise

universe u v w

theorem pgl_map_injective {K : Type u} {F : Type v} [Field K] [Field F]
    (i : K →+* F) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk U =>
    rw [MonoidHom.mem_ker, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
    obtain ⟨c, hc⟩ := hg
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨U.val 0 0, Matrix.ext fun a b => i.injective ?_⟩
    have h00 : c = i (U.val 0 0) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_true,
        Matrix.GeneralLinearGroup.map_apply] using hh
    have hab : (if a = b then c else 0) = i (U.val a b) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M a b) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.GeneralLinearGroup.map_apply] using hh
    by_cases h : a = b
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_left h] using
        h00.symm.trans (by simpa only [ite_eq_left h] using hab)
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_right h, map_zero] using
        (by simpa only [ite_eq_right h] using hab : 0 = i (U.val a b))

theorem gl_mul_scalar_entry {F : Type u} [Field F]
    (U : Matrix.GeneralLinearGroup (Fin 2) F) (c : Fˣ) (i j : Fin 2) :
    (U * Matrix.GeneralLinearGroup.scalar (Fin 2) c).val i j = U.val i j * c := by
  simp [Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mul_diagonal]

theorem gl_exists_nonzero_entry {F : Type u} [Field F]
    (U : Matrix.GeneralLinearGroup (Fin 2) F) : ∃ i j, U.val i j ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : U.val = 0 := Matrix.ext h
  have hdet : Matrix.det U.val ≠ 0 := U.det.ne_zero
  exact hdet (by rw [hzero]; simp)

theorem pgl_normalized_representative {F : Type u} [Field F] (g : PGL2 F) :
    ∃ (V : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2),
      Matrix.ProjGenLinGroup.mk V = g ∧ V.val i j = 1 := by
  obtain ⟨U, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨i, j, hij⟩ := gl_exists_nonzero_entry U
  let c : Fˣ := Units.mk0 (U.val i j) hij
  refine ⟨U * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, i, j, ?_, ?_⟩
  · rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  · rw [gl_mul_scalar_entry]
    exact mul_inv_cancel₀ hij

theorem normalized_projective_fixed {F : Type u} [Field F]
    (V : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) (hij : V.val i j = 1)
    (sigma : F ≃+* F)
    (hfix : pgl2FieldAut F sigma (Matrix.ProjGenLinGroup.mk V) =
      Matrix.ProjGenLinGroup.mk V) : Matrix.GeneralLinearGroup.map sigma.toRingHom V = V := by
  have hmap : pgl2FieldAut F sigma (Matrix.ProjGenLinGroup.mk V) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom V) := by
    rw [pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk sigma V
  rw [hmap, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hfix
  obtain ⟨c, hc⟩ := hfix
  have hc1 : c = 1 := by
    apply Units.ext
    have hentry := congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) F => U.val i j) hc
    simpa only [gl_mul_scalar_entry, Matrix.GeneralLinearGroup.map_apply,
      RingEquiv.toRingHom_eq_coe, hij, map_one, one_mul, Units.val_one] using hentry
  simpa only [hc1, map_one, mul_one] using hc

abbrev F0 (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) := FixedPoints.subfield A F

@[expose] def pglInclusion (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    PGL2 (F0 F A) →* PGL2 F := Matrix.ProjGenLinGroup.map (F0 F A).subtype

theorem gl_descends {F : Type u} [Field F] (A : Subgroup (F ≃+* F))
    (V : Matrix.GeneralLinearGroup (Fin 2) F)
    (hfix : ∀ (sigma : A) i j, (sigma : F ≃+* F) (V.val i j) = V.val i j) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A),
      Matrix.GeneralLinearGroup.map (F0 F A).subtype U = V := by
  let W : Matrix (Fin 2) (Fin 2) (F0 F A) := fun i j => ⟨V.val i j, fun sigma => hfix sigma i j⟩
  have hmap : W.map (F0 F A).subtype = V.val := rfl
  have hdet : Matrix.det W ≠ 0 := by
    intro h
    have hh := congrArg (F0 F A).subtype h
    rw [map_zero] at hh
    have hmapdet : (F0 F A).subtype (Matrix.det W) = Matrix.det V.val := by
      simpa only [RingHom.mapMatrix_apply, hmap] using (F0 F A).subtype.map_det W
    exact V.det.ne_zero (hmapdet.symm.trans hh)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero W hdet, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem pgl_fixed_iff (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) (g : PGL2 F) :
    (∀ sigma : A, pgl2FieldAut F sigma g = g) ↔ g ∈ (pglInclusion F A).range := by
  constructor
  · intro hg
    obtain ⟨V, i, j, hV, hij⟩ := pgl_normalized_representative g
    have hfixed : ∀ (sigma : A) a b, (sigma : F ≃+* F) (V.val a b) = V.val a b := by
      intro sigma a b
      have h := normalized_projective_fixed V i j hij sigma (by rw [hV]; exact hg sigma)
      exact congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) F => U.val a b) h
    obtain ⟨U, hU⟩ := gl_descends A V hfixed
    refine ⟨Matrix.ProjGenLinGroup.mk U, ?_⟩
    rw [pglInclusion, Matrix.ProjGenLinGroup.map_mk, hU, hV]
  · rintro ⟨g0, rfl⟩ sigma
    induction g0 using Matrix.ProjGenLinGroup.induction_on with
    | mk U =>
      rw [pglInclusion, Matrix.ProjGenLinGroup.map_mk, pgl2FieldAut_apply]
      have hmap := pgl2RingEquiv_mk sigma.val (Matrix.GeneralLinearGroup.map (F0 F A).subtype U)
      apply hmap.trans
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact (U.val i j).property sigma

theorem coordinatePGLAction_field (F : Type u) [Field F] [Finite F]
    (sigma : F ≃+* F) (g : PGL2 F) :
    coordinatePGLAction F (pgl2FieldAut F sigma g) =
      fieldExtension F sigma * coordinatePGLAction F g * (fieldExtension F sigma)⁻¹ := by
  have h := congrArg (coordinateSemilinearAction F)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut F) sigma g)
  simpa only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] using h

theorem coordinatePGLAction_commute_iff (F : Type u) [Field F] [Finite F]
    (sigma : F ≃+* F) (g : PGL2 F) :
    Commute (coordinatePGLAction F g) (fieldExtension F sigma) ↔
      pgl2FieldAut F sigma g = g := by
  constructor
  · intro h
    apply coordinatePGLAction_injective F
    rw [coordinatePGLAction_field, h.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    have hh := coordinatePGLAction_field F sigma g
    rw [h] at hh
    exact eq_mul_inv_iff_mul_eq.mp hh

@[expose] def fixedGLAction (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Matrix.GeneralLinearGroup (Fin 2) (F0 F A) →* Equiv.Perm (Omega F) :=
  (coordinatePGLAction F).comp
    (Matrix.ProjGenLinGroup.mk.comp (Matrix.GeneralLinearGroup.map (F0 F A).subtype))

@[expose] def D0 (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Subgroup (Equiv.Perm (Omega F)) := (fixedGLAction F A).range

@[expose] def pglToCoordinateD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : PGL2 (F0 F A) →* coordinateD F :=
  (pglEquivCoordinateD F).toMonoidHom.comp (pglInclusion F A)

@[expose] def coordinateDInclusion (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD (F0 F A) →* coordinateD F :=
  (pglToCoordinateD F A).comp (pglEquivCoordinateD (F0 F A)).symm.toMonoidHom

@[expose] def D0InD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Subgroup (coordinateD F) := (pglToCoordinateD F A).range

theorem pglToCoordinateD_injective (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Function.Injective (pglToCoordinateD F A) :=
  (pglEquivCoordinateD F).injective.comp (pgl_map_injective (F0 F A).subtype)

@[expose] def pglEquivD0InD (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : PGL2 (F0 F A) ≃* D0InD F A :=
  MonoidHom.ofInjective (pglToCoordinateD_injective F A)

@[expose] def coordinateDEquivD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD (F0 F A) ≃* D0InD F A :=
  (pglEquivCoordinateD (F0 F A)).symm.trans (pglEquivD0InD F A)

theorem coordinateDEquivD0_matrix (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A)) :
    ((coordinateDEquivD0 F A (pglEquivCoordinateD (F0 F A)
      (Matrix.ProjGenLinGroup.mk U)) : coordinateD F) : Equiv.Perm (Omega F)) =
        fixedGLAction F A U := by
  change ((pglToCoordinateD F A ((pglEquivCoordinateD (F0 F A)).symm
    (pglEquivCoordinateD (F0 F A) (Matrix.ProjGenLinGroup.mk U)))) :
      Equiv.Perm (Omega F)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem D0InD_map_subtype (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (D0InD F A).map (coordinateD F).subtype = D0 F A := by
  rw [D0InD, ← MonoidHom.range_comp]
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨U, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    exact ⟨U, rfl⟩
  · rintro _ ⟨U, rfl⟩
    exact ⟨Matrix.ProjGenLinGroup.mk U, rfl⟩

theorem D0InD_mem_iff (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (g : coordinateD F) :
    g ∈ D0InD F A ↔ ∀ sigma : A, Commute (g : Equiv.Perm (Omega F)) (fieldExtension F sigma) := by
  let v := (pglEquivCoordinateD F).symm g
  have hv : coordinatePGLAction F v = (g : Equiv.Perm (Omega F)) :=
    congrArg Subtype.val ((pglEquivCoordinateD F).apply_symm_apply g)
  have hmem : g ∈ D0InD F A ↔ v ∈ (pglInclusion F A).range := by
    constructor
    · rintro ⟨g0, hg0⟩
      refine ⟨g0, ?_⟩
      apply (pglEquivCoordinateD F).injective
      exact hg0.trans ((pglEquivCoordinateD F).apply_symm_apply g).symm
    · rintro ⟨g0, hg0⟩
      exact ⟨g0, by
        change pglEquivCoordinateD F (pglInclusion F A g0) = g
        rw [hg0, MulEquiv.apply_symm_apply]⟩
  rw [hmem, ← pgl_fixed_iff]
  exact forall_congr' fun sigma => (coordinatePGLAction_commute_iff F sigma v).symm.trans
    (by rw [hv])

theorem fixed_field_projective_centralizer (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    (Subgroup.centralizer (ambientLiftedField F A : Set (Equiv.Perm (Omega F)))).comap
      (coordinateD F).subtype = D0InD F A := by
  ext g
  rw [D0InD_mem_iff]
  change (∀ a ∈ ambientLiftedField F A, a * (g : Equiv.Perm (Omega F)) =
      (g : Equiv.Perm (Omega F)) * a) ↔ _
  constructor
  · intro h sigma
    exact (h (fieldExtension F sigma)
      ((ambientLiftedField_mem F A _).mpr ⟨sigma, sigma.property, rfl⟩)).symm
  · intro h a ha
    obtain ⟨sigma, hsigma, rfl⟩ := (ambientLiftedField_mem F A a).mp ha
    exact (h ⟨sigma, hsigma⟩).eq.symm

theorem D0InD_card (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    Nat.card (D0InD F A) = Nat.card (F0 F A) * (Nat.card (F0 F A) ^ 2 - 1) := by
  rw [← Nat.card_congr (pglEquivD0InD F A).toEquiv]
  exact pgl2_card_formula (F0 F A)

theorem centralizer_preimage_odd {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hc : pi.ker ≤ Subgroup.center H)
    (h2 : ∀ k ∈ pi.ker, k ^ 2 = 1) (U : Subgroup H)
    (d : ℕ) (hd : Odd d) (hU : ∀ x ∈ U, x ^ d = 1) :
    Subgroup.centralizer (U : Set H) =
      (Subgroup.centralizer (U.map pi : Set Q)).comap pi := by
  ext h
  constructor
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨e, he, rfl⟩
    have hec := congrArg pi (Subgroup.mem_centralizer_iff.mp hh e he)
    simpa only [map_mul] using hec
  · intro hh
    let f : U →* H := (MulAut.conj h).toMonoidHom.comp U.subtype
    let g : U →* H := U.subtype
    have hfg : ∀ e : U, (f e)⁻¹ * g e ∈ pi.ker := by
      intro e
      have hh' := Subgroup.mem_centralizer_iff.mp hh (pi e) ⟨e, e.property, rfl⟩
      change pi ((h * (e : H) * h⁻¹)⁻¹ * e) = 1
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hh', mul_assoc,
        mul_inv_cancel, mul_one, inv_mul_cancel]
    let delta := CFSG.Semidihedral.CentralPrimeExtensions.centralDifference pi.ker hc f g hfg
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    let eU : U := ⟨e, he⟩
    have heUd : eU ^ d = 1 := Subtype.ext (hU e he)
    have hdeltad : (delta eU) ^ d = 1 := by rw [← map_pow, heUd, map_one]
    have hdelta2 : (delta eU) ^ 2 = 1 := Subtype.ext (h2 _ (delta eU).property)
    have hdelta1 : delta eU = 1 := by
      obtain ⟨n, hn⟩ := hd
      rw [hn, pow_succ, pow_mul, hdelta2, one_pow, one_mul] at hdeltad
      exact hdeltad
    have hefix : h * e * h⁻¹ = e := by
      have hh := congrArg (fun k : pi.ker => (k : H)) hdelta1
      exact inv_mul_eq_one.mp hh
    exact (mul_inv_eq_iff_eq_mul.mp hefix).symm

theorem kernel_exponent_two {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) : ∀ k ∈ pi.ker, k ^ 2 = 1 := by
  intro k hk
  have hcard : Nat.card pi.ker = 2 := by rw [hker, Nat.card_zpowers, hz]
  have hh := congrArg (fun x : pi.ker => (x : H))
    (pow_card_eq_one' (x := (⟨k, hk⟩ : pi.ker)))
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcard] using hh

theorem exists_sylow_le_of_odd_index {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) (hindex : Odd N.index) : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 N := Classical.choice inferInstance
  let U : Subgroup H := (P : Subgroup N).map N.subtype
  have hUp : IsPGroup 2 U := P.isPGroup'.map N.subtype
  have hUindex : Odd U.index := by
    rw [Subgroup.index_map_subtype]
    have hPodd : Odd (P : Subgroup N).index :=
      Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index h.two_dvd)
    exact hPodd.mul hindex
  refine ⟨hUp.toSylow hUindex.not_two_dvd_nat, ?_⟩
  change U ≤ N
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

theorem projective_card_odd_ratio {q0 d : ℕ} (hq0 : 3 ≤ q0)
    (hqodd : Odd q0) (hd : Odd d) :
    ∃ r : ℕ, Odd r ∧
      q0 ^ d * ((q0 ^ d) ^ 2 - 1) = r * (q0 * (q0 ^ 2 - 1)) := by
  let s := ∑ i ∈ Finset.range d, (q0 ^ 2) ^ i
  let r := q0 ^ (d - 1) * s
  have hdpos : 1 ≤ d := hd.pos
  have hq : q0 ^ d = q0 ^ (d - 1) * q0 := by rw [← pow_succ, Nat.sub_one_add_one (by omega)]
  have hgeom : (q0 ^ d) ^ 2 - 1 = s * (q0 ^ 2 - 1) := by
    have hh := geom_sum_mul_of_one_le (show 1 ≤ q0 ^ 2 by nlinarith) d
    simpa only [s, ← pow_mul, Nat.mul_comm 2 d] using hh.symm
  refine ⟨r, hqodd.pow.mul (odd_geometric_sum hqodd hd), ?_⟩
  rw [hgeom, hq]
  dsimp only [r]
  ring

theorem D0InD_index_odd (p f : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (F : Type u) [Field F] [Finite F]
    (hcard : Nat.card F = p ^ f) (A : Subgroup (F ≃+* F))
    (hd : Odd (Nat.card A)) : Odd (D0InD F A).index := by
  obtain ⟨_, _, hq0, hqodd, _, hfixed, hpower, _, _, _⟩ :=
    odd_fixed_field_data p f hp hpodd hf F hcard A hd
  obtain ⟨r, hr, hratio⟩ := projective_card_odd_ratio hq0 hqodd hd
  have hcardD : Nat.card (coordinateD F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr (pglEquivCoordinateD F).toEquiv]
    exact pgl2_card_formula F
  have hi := (D0InD F A).index_mul_card
  rw [D0InD_card, hcardD, hfixed, hpower] at hi
  have heq : (D0InD F A).index = r := by
    have hbase : 0 < (p ^ (f / Nat.card A)) ^ 2 - 1 := by
      have hh : 1 < (p ^ (f / Nat.card A)) ^ 2 := by nlinarith
      omega
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) hbase) (hi.trans hratio)
  rwa [heq]

@[expose] def dToGamma (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD F →* Gamma F A :=
  (linearInclusion F).codRestrict (Gamma F A)
    (CFSG.Semidihedral.FixedFieldCentralizerGamma.linearInclusion_mem_Gamma F A)

@[expose] def gammaAction (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Gamma F A →* Equiv.Perm (Omega F) :=
  (coordinateE F).subtype.comp (Gamma F A).subtype

theorem gammaAction_injective (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Function.Injective (gammaAction F A) :=
  (coordinateE F).subtype_injective.comp (Gamma F A).subtype_injective

theorem dToGamma_action (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (d : coordinateD F) :
    gammaAction F A (dToGamma F A d) = (d : Equiv.Perm (Omega F)) := by
  have e : ((dToGamma F A d : Gamma F A) : coordinateE F) = linearInclusion F d := rfl
  rw [gammaAction, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.coe_subtype, e, linearInclusion_coe]

theorem dToGamma_injective (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Function.Injective (dToGamma F A) := by
  intro x y h
  have hh := congrArg (gammaAction F A) h
  rw [dToGamma_action, dToGamma_action] at hh
  exact Subtype.ext hh

theorem dToGamma_range (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (dToGamma F A).range = gammaLinear F A := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    have e : ((dToGamma F A d : Gamma F A) : coordinateE F) = linearInclusion F d := rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, e, linearInclusion_coe]
    exact d.property
  · intro hx
    have hx' : gammaAction F A x ∈ coordinateD F := by
      rw [gammaAction, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_subtype]
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨⟨gammaAction F A x, hx'⟩, gammaAction_injective F A (dToGamma_action F A _)⟩

@[expose] def gammaD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Subgroup (Gamma F A) := (D0InD F A).map (dToGamma F A)

theorem gammaD0_le_linear (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : gammaD0 F A ≤ gammaLinear F A := by
  rw [← dToGamma_range]
  exact Subgroup.map_le_range _ _

theorem gammaD0_action_image (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (gammaD0 F A).map (gammaAction F A) = D0 F A := by
  have hcomp : (gammaAction F A).comp (dToGamma F A) = (coordinateD F).subtype :=
    MonoidHom.ext (dToGamma_action F A)
  rw [gammaD0, Subgroup.map_map, hcomp, D0InD_map_subtype]

@[expose] def coordinateDEquivGammaD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD (F0 F A) ≃* gammaD0 F A :=
  (coordinateDEquivD0 F A).trans
    (Subgroup.equivMapOfInjective (D0InD F A) (dToGamma F A) (dToGamma_injective F A))

theorem gammaD0_card (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    Nat.card (gammaD0 F A) = Nat.card (F0 F A) * (Nat.card (F0 F A) ^ 2 - 1) := by
  change Nat.card ((D0InD F A).map (dToGamma F A)) = _
  rw [← Nat.card_congr
    (Subgroup.equivMapOfInjective (D0InD F A) (dToGamma F A) (dToGamma_injective F A)).toEquiv]
  exact D0InD_card F A

theorem commute_iff_map {H : Type u} {Q : Type v} [Group H] [Group Q]
    (phi : H →* Q) (hphi : Function.Injective phi) (x y : H) :
    Commute x y ↔ Commute (phi x) (phi y) := by
  constructor
  · exact fun h => h.map phi
  · exact fun h => hphi (by simpa only [map_mul] using h.eq)

theorem dToGamma_centralizer_iff (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (d : coordinateD F) :
    dToGamma F A d ∈ Subgroup.centralizer (gammaField F A : Set (Gamma F A)) ↔
      d ∈ D0InD F A := by
  rw [D0InD_mem_iff]
  constructor
  · intro h sigma
    have hc := Subgroup.mem_centralizer_iff.mp h
      ((gammaFieldEquiv F A).symm sigma) ((gammaFieldEquiv F A).symm sigma).property
    have hh := congrArg (gammaAction F A) hc
    rw [map_mul, map_mul, dToGamma_action] at hh
    rw [show gammaAction F A ((gammaFieldEquiv F A).symm sigma : Gamma F A) =
      fieldExtension F sigma from gammaFieldEquiv_symm_coe F A sigma] at hh
    exact hh.symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let aU : gammaField F A := ⟨a, ha⟩
    let sigma := gammaFieldEquiv F A aU
    have heq : (gammaFieldEquiv F A).symm sigma = aU :=
      (gammaFieldEquiv F A).symm_apply_apply aU
    apply gammaAction_injective F A
    rw [map_mul, map_mul, dToGamma_action]
    have haction : gammaAction F A a = fieldExtension F sigma := by
      rw [← show ((gammaFieldEquiv F A).symm sigma : Gamma F A) = a from
        congrArg Subtype.val heq]
      exact gammaFieldEquiv_symm_coe F A sigma
    rw [haction]
    exact (h sigma).eq.symm

theorem gammaLinear_inf_centralizer (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    gammaLinear F A ⊓ Subgroup.centralizer (gammaField F A : Set (Gamma F A)) = gammaD0 F A := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨d, rfl⟩ := (dToGamma_range F A).symm ▸ hx
    exact ⟨d, (dToGamma_centralizer_iff F A d).mp hc, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(dToGamma_range F A) ▸ (show dToGamma F A d ∈ (dToGamma F A).range from ⟨d, rfl⟩),
      (dToGamma_centralizer_iff F A d).mpr hd⟩

theorem gammaField_le_centralizer (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    gammaField F A ≤ Subgroup.centralizer (gammaField F A : Set (Gamma F A)) := by
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let : IsCyclic (gammaField F A) := (gammaFieldEquiv F A).isCyclic.mpr inferInstance
  have hc : IsMulCommutative (gammaField F A) := inferInstance
  intro a ha
  apply Subgroup.mem_centralizer_iff.mpr
  intro b hb
  exact congrArg Subtype.val (hc.is_comm.comm (⟨b, hb⟩ : gammaField F A) ⟨a, ha⟩)

theorem centralizer_factorization {H : Type u} [Group H]
    (N U : Subgroup H) (hNU : N.IsComplement' U)
    (hcU : U ≤ Subgroup.centralizer (U : Set H))
    (x : H) (hx : x ∈ Subgroup.centralizer (U : Set H)) :
    ∃ n : (N ⊓ Subgroup.centralizer (U : Set H) : Subgroup H),
      ∃ a : U, x = (n : H) * a := by
  obtain ⟨na, hna⟩ := hNU.surjective x
  have hnC : (na.1 : H) ∈ Subgroup.centralizer (U : Set H) := by
    have hh := (Subgroup.centralizer (U : Set H)).mul_mem hx
      ((Subgroup.centralizer (U : Set H)).inv_mem (hcU na.2.property))
    simpa only [← hna, mul_assoc, mul_inv_cancel, mul_one] using hh
  exact ⟨⟨na.1, na.1.property, hnC⟩, na.2, hna.symm⟩

theorem gamma_centralizer_factorization (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (x : Gamma F A)
    (hx : x ∈ Subgroup.centralizer (gammaField F A : Set (Gamma F A))) :
    ∃ n : gammaD0 F A, ∃ a : gammaField F A, x = (n : Gamma F A) * a := by
  have h := centralizer_factorization (gammaLinear F A) (gammaField F A)
    (gamma_isComplement F A) (gammaField_le_centralizer F A) x hx
  rw [gammaLinear_inf_centralizer] at h
  exact h

theorem gamma_centralizer_eq_sup (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    Subgroup.centralizer (gammaField F A : Set (Gamma F A)) = gammaD0 F A ⊔ gammaField F A := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, h⟩ := gamma_centralizer_factorization F A x hx
    rw [h]
    exact (gammaD0 F A ⊔ gammaField F A).mul_mem
      ((show gammaD0 F A ≤ gammaD0 F A ⊔ gammaField F A from le_sup_left) n.property)
      ((show gammaField F A ≤ gammaD0 F A ⊔ gammaField F A from le_sup_right) a.property)
  · apply sup_le
    · rw [← gammaLinear_inf_centralizer]
      exact inf_le_right
    · exact gammaField_le_centralizer F A

abbrev M0 {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) := (gammaD0 F A).comap pi

theorem M0_mem_iff {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (h : H) :
    h ∈ M0 F A pi ↔ coordinateProjection F A pi h ∈ D0 F A := by
  change pi h ∈ gammaD0 F A ↔ gammaAction F A (pi h) ∈ D0 F A
  rw [← gammaD0_action_image]
  exact ⟨fun hx => ⟨pi h, hx, rfl⟩, fun ⟨x, hx, heq⟩ =>
    gammaAction_injective F A heq ▸ hx⟩


theorem E_map_pi {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    (E F A pi z hzc hker).map pi = gammaField F A := by
  ext a
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he.1
  · intro ha
    obtain ⟨e, he⟩ := (piOnE F A pi hpi z hz hzc hker hd).surjective ⟨a, ha⟩
    exact ⟨e, e.property, congrArg Subtype.val he⟩

theorem E_centralizer_preimage {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Subgroup.centralizer (E F A pi z hzc hker : Set H) =
      (Subgroup.centralizer (gammaField F A : Set (Gamma F A))).comap pi := by
  rw [centralizer_preimage_odd pi (kernel_central pi z hzc hker)
    (kernel_exponent_two pi z hz hker) (E F A pi z hzc hker)
    (Nat.card A) hd (fun _ he => he.2), E_map_pi F A pi hpi z hz hzc hker hd]

theorem M0_le_centralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    M0 F A pi ≤ Subgroup.centralizer (E F A pi z hzc hker : Set H) := by
  rw [E_centralizer_preimage F A pi hpi z hz hzc hker hd]
  apply Subgroup.comap_mono
  rw [← gammaLinear_inf_centralizer]
  exact inf_le_right

theorem E_le_centralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    E F A pi z hzc hker ≤ Subgroup.centralizer (E F A pi z hzc hker : Set H) := by
  rw [E_centralizer_preimage F A pi hpi z hz hzc hker hd]
  intro e he
  exact gammaField_le_centralizer F A he.1

theorem E_centralizer_factorization {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (h : H) (hh : h ∈ Subgroup.centralizer (E F A pi z hzc hker : Set H)) :
    ∃ m : M0 F A pi, ∃ e : E F A pi z hzc hker, h = (m : H) * e := by
  have hquot : pi h ∈ Subgroup.centralizer (gammaField F A : Set (Gamma F A)) := by
    have hh' := hh
    rw [E_centralizer_preimage F A pi hpi z hz hzc hker hd] at hh'
    exact hh'
  obtain ⟨n, a, hna⟩ := gamma_centralizer_factorization F A (pi h) hquot
  let e := (piOnE F A pi hpi z hz hzc hker hd).symm a
  have he : pi e = (a : Gamma F A) := congrArg Subtype.val
    ((piOnE F A pi hpi z hz hzc hker hd).apply_symm_apply a)
  have hm : h * (e : H)⁻¹ ∈ M0 F A pi := by
    change pi (h * (e : H)⁻¹) ∈ gammaD0 F A
    rw [map_mul, map_inv, he, hna, mul_assoc, mul_inv_cancel, mul_one]
    exact n.property
  exact ⟨⟨h * (e : H)⁻¹, hm⟩, e, by rw [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem M0_inf_E {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    M0 F A pi ⊓ E F A pi z hzc hker = ⊥ := by
  apply le_antisymm
  · rintro h ⟨hm, he⟩
    have hM : h ∈ M F A pi := gammaD0_le_linear F A hm
    exact (H_isComplement F A pi hpi z hz hzc hker hd).disjoint.le_bot ⟨hM, he⟩
  · exact bot_le

theorem E_centralizer_eq_sup {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Subgroup.centralizer (E F A pi z hzc hker : Set H) = M0 F A pi ⊔ E F A pi z hzc hker := by
  apply le_antisymm
  · intro h hh
    obtain ⟨m,e,hme⟩ := E_centralizer_factorization F A pi hpi z hz hzc hker hd h hh
    rw [hme]
    exact (M0 F A pi ⊔ E F A pi z hzc hker).mul_mem
      ((show M0 F A pi ≤ M0 F A pi ⊔ E F A pi z hzc hker from le_sup_left) m.property)
      ((show E F A pi z hzc hker ≤ M0 F A pi ⊔ E F A pi z hzc hker from le_sup_right) e.property)
  · exact sup_le (M0_le_centralizer F A pi hpi z hz hzc hker hd)
      (E_le_centralizer F A pi hpi z hz hzc hker hd)

@[expose] def ECentralizerDirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    M0 F A pi × E F A pi z hzc hker ≃*
      Subgroup.centralizer (E F A pi z hzc hker : Set H) := by
  apply Subgroup.mulEquivProdOfInternalDirect _ _ _
    (M0_le_centralizer F A pi hpi z hz hzc hker hd)
    (E_le_centralizer F A pi hpi z hz hzc hker hd)
    (fun hm he => (Subgroup.mem_centralizer_iff.mp
      (M0_le_centralizer F A pi hpi z hz hzc hker hd hm) _ he).symm)
    (M0_inf_E F A pi hpi z hz hzc hker hd)
  intro h hh
  obtain ⟨m,e,hme⟩ := E_centralizer_factorization F A pi hpi z hz hzc hker hd h hh
  exact ⟨m,m.property,e,e.property,hme.symm⟩

theorem ECentralizerDirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (x : M0 F A pi × E F A pi z hzc hker) :
    (ECentralizerDirectEquiv F A pi hpi z hz hzc hker hd x : H) = (x.1 : H) * x.2 := rfl

theorem gammaLinear_index (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : (gammaLinear F A).index = Nat.card A :=
  (gamma_isComplement F A).symm.index_eq_card.trans (gammaField_card F A)

theorem M0_index_odd {H : Type v} [Group H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (hd : Odd (Nat.card A))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi) : Odd (M0 F A pi).index := by
  rw [Subgroup.index_comap_of_surjective _ hpi]
  change Odd ((D0InD F A).map (dToGamma F A)).index
  rw [Subgroup.index_map_of_injective _ (dToGamma_injective F A), dToGamma_range, gammaLinear_index]
  exact (D0InD_index_odd p f hp hpodd hf F hcard A hd).mul hd

theorem exists_sylow_in_M0 {H : Type v} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (hd : Odd (Nat.card A))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) :
    ∃ S : Sylow 2 H, (S : Subgroup H) ≤ M0 F A pi ∧
      ⁅(S : Subgroup H), E F A pi z hzc hker⁆ = ⊥ := by
  obtain ⟨S,hS⟩ := exists_sylow_le_of_odd_index (M0 F A pi)
    (M0_index_odd p f hp hpodd hf F hcard A hd pi hpi)
  exact ⟨S,hS,Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (hS.trans (M0_le_centralizer F A pi hpi z hz hzc hker hd))⟩

theorem preimage_card {H : Type v} {Q : Type w} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (N : Subgroup Q) :
    Nat.card (N.comap pi) = Nat.card pi.ker * Nat.card N := by
  let f := preimageProjection pi N
  have hker : f.ker = pi.ker.subgroupOf (N.comap pi) := by
    ext x
    exact ⟨fun h => congrArg Subtype.val (show f x = 1 from h),
      fun h => Subtype.ext h⟩
  have hc : Nat.card f.ker = Nat.card pi.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pi.ker_le_comap N)).toEquiv
  have h := Subgroup.card_ker_mul_card_of_surjective (preimageProjection_surjective pi hpi N)
  rw [hc] at h
  exact h.symm

theorem M0_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hker : pi.ker = Subgroup.zpowers z) :
    Nat.card (M0 F A pi) = 2 * Nat.card (F0 F A) * (Nat.card (F0 F A)^2 - 1) := by
  rw [preimage_card pi hpi, hker, Nat.card_zpowers, hz, gammaD0_card, Nat.mul_assoc]


@[expose] def coordinateDEquivActualD0 (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : coordinateD (F0 F A) ≃* D0 F A :=
  (coordinateDEquivD0 F A).trans
    ((Subgroup.equivMapOfInjective (D0InD F A) (coordinateD F).subtype
      (coordinateD F).subtype_injective).trans (subgroupEquivOfEq (D0InD_map_subtype F A)))

theorem coordinateDEquivActualD0_matrix (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A)) :
    (coordinateDEquivActualD0 F A (pglEquivCoordinateD (F0 F A)
      (Matrix.ProjGenLinGroup.mk U)) : Equiv.Perm (Omega F)) = fixedGLAction F A U :=
  coordinateDEquivD0_matrix F A U

theorem E_centralizer_internal {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    ((M0 F A pi).subgroupOf (Subgroup.centralizer (E F A pi z hzc hker : Set H))).IsComplement'
      ((E F A pi z hzc hker).subgroupOf (Subgroup.centralizer (E F A pi z hzc hker : Set H))) :=
  factorization_isComplement _ _ _ (M0_le_centralizer F A pi hpi z hz hzc hker hd)
    (E_le_centralizer F A pi hpi z hz hzc hker hd)
    (disjoint_iff.mpr (M0_inf_E F A pi hpi z hz hzc hker hd))
    (fun x => E_centralizer_factorization F A pi hpi z hz hzc hker hd x x.property)

structure FixedCentralizerConclusions {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F) (p f d : ℕ) : Prop where
  degree_dvd : d ∣ f
  fixed_membership : ∀ x : F, x ∈ F0 F A ↔ ∀ sigma : A, (sigma : F ≃+* F) x = x
  fixed_card : Nat.card (F0 F A) = p ^ (f / d)
  field_power : Nat.card F = (p ^ (f / d)) ^ d
  fixed_odd : Odd (p ^ (f / d))
  fixed_ge_three : 3 ≤ p ^ (f / d)
  two_part : (Nat.card F ^ 2 - 1).factorization 2 = ((p ^ (f / d)) ^ 2 - 1).factorization 2
  actual_D0_image : D0 F A = (fixedGLAction F A).range
  D0_identification : (D0InD F A).map (coordinateD F).subtype = D0 F A
  natural : ∃ rho : coordinateD (F0 F A) ≃* D0 F A,
    ∀ U : Matrix.GeneralLinearGroup (Fin 2) (F0 F A),
      (rho (pglEquivCoordinateD (F0 F A) (Matrix.ProjGenLinGroup.mk U)) :
        Equiv.Perm (Omega F)) = fixedGLAction F A U
  D_centralizer : (Subgroup.centralizer (ambientLiftedField F A : Set (Equiv.Perm (Omega F)))).comap
    (coordinateD F).subtype = D0InD F A
  gamma_centralizer : Subgroup.centralizer (gammaField F A : Set (Gamma F A)) = gammaD0 F A ⊔ gammaField F A
  roots : ∀ b : H, b ∈ E F A pi z hzc hker ↔ b ∈ B F A pi ∧ b ^ d = 1
  actual_M0 : ∀ h : H, h ∈ M0 F A pi ↔ coordinateProjection F A pi h ∈ D0 F A
  centralizer_preimage : Subgroup.centralizer (E F A pi z hzc hker : Set H) =
    (Subgroup.centralizer (gammaField F A : Set (Gamma F A))).comap pi
  centralizer_join : Subgroup.centralizer (E F A pi z hzc hker : Set H) = M0 F A pi ⊔ E F A pi z hzc hker
  commuting : ∀ m : M0 F A pi, ∀ e : E F A pi z hzc hker, Commute (m : H) (e : H)
  disjoint : M0 F A pi ⊓ E F A pi z hzc hker = ⊥
  internal : ((M0 F A pi).subgroupOf (Subgroup.centralizer (E F A pi z hzc hker : Set H))).IsComplement'
    ((E F A pi z hzc hker).subgroupOf (Subgroup.centralizer (E F A pi z hzc hker : Set H)))
  direct : ∃ eps : M0 F A pi × E F A pi z hzc hker ≃* Subgroup.centralizer (E F A pi z hzc hker : Set H),
    ∀ x, (eps x : H) = (x.1 : H) * x.2
  odd_index : Odd (M0 F A pi).index
  sylow : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ M0 F A pi ∧
    ⁅(S : Subgroup H), E F A pi z hzc hker⁆ = ⊥ ∧
    ∀ s : S, ∀ e : E F A pi z hzc hker, Commute (s : H) (e : H)
  fixed_eta : ∃ eps : LambdaCentralizer F A pi z hzc hker ≃* Matrix.SpecialLinearGroup (Fin 2) (F0 F A),
    ∀ x, fixedSL2Inclusion F A (eps x) = eta x
  M0_card : Nat.card (M0 F A pi) = 2 * (p ^ (f / d)) * ((p ^ (f / d)) ^ 2 - 1)

theorem odd_field_lift_fixed_centralizer_and_Sylow {H : Type v} [Group H] [Finite H]
    (F : Type u) [Field F] [Finite F] {p f d : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (hAd : Nat.card A = d) (hd : Odd d)
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hetaz : eta (zInLambda F A pi z hker) = (-1 : Matrix.SpecialLinearGroup (Fin 2) F))
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    FixedCentralizerConclusions F A pi z hzc hker eta p f d := by
  have hdA : Odd (Nat.card A) := hAd.symm ▸ hd
  have hlift := central_double_cover_lifts_odd_field_action_exactly F hp hpodd hf hcard A hAd hd
    pi hpi z hz hzc hker eta hetaz heta
  obtain ⟨hdvd,_,hq0,hqodd,hmem,hfixed,hpower,_,htwo,_⟩ :=
    odd_fixed_field_data p f hp hpodd hf F hcard A hdA
  rw [hAd] at hdvd hq0 hqodd hfixed hpower htwo
  obtain ⟨S,hS,hcomm⟩ := exists_sylow_in_M0 p f hp hpodd hf F hcard A hdA pi hpi z hz hzc hker
  refine { degree_dvd := hdvd
           fixed_membership := hmem
           fixed_card := hfixed
           field_power := hpower
           fixed_odd := hqodd
           fixed_ge_three := hq0
           two_part := htwo
           actual_D0_image := rfl
           D0_identification := D0InD_map_subtype F A
           natural := ⟨coordinateDEquivActualD0 F A, coordinateDEquivActualD0_matrix F A⟩
           D_centralizer := fixed_field_projective_centralizer F A
           gamma_centralizer := gamma_centralizer_eq_sup F A
           roots := hlift.roots
           actual_M0 := M0_mem_iff F A pi
           centralizer_preimage := E_centralizer_preimage F A pi hpi z hz hzc hker hdA
           centralizer_join := E_centralizer_eq_sup F A pi hpi z hz hzc hker hdA
           commuting := ?_
           disjoint := M0_inf_E F A pi hpi z hz hzc hker hdA
           internal := E_centralizer_internal F A pi hpi z hz hzc hker hdA
           direct := ⟨ECentralizerDirectEquiv F A pi hpi z hz hzc hker hdA,
             ECentralizerDirectEquiv_coe F A pi hpi z hz hzc hker hdA⟩
           odd_index := M0_index_odd p f hp hpodd hf F hcard A hdA pi hpi
           sylow := ⟨S,hS,hcomm,?_⟩
           fixed_eta := hlift.fixed_equiv
           M0_card := ?_ }
  · intro m e
    exact (Subgroup.mem_centralizer_iff.mp
      (M0_le_centralizer F A pi hpi z hz hzc hker hdA m.property) e e.property).symm
  · intro s e
    exact (Subgroup.mem_centralizer_iff.mp
      (M0_le_centralizer F A pi hpi z hz hzc hker hdA (hS s.property)) e e.property).symm
  · rw [M0_card F A pi hpi z hz hker, hfixed]

theorem odd_field_lift_fixed_centralizer_and_Sylow_int {H : Type v} [Group H] [Finite H]
    (F : Type u) [Field F] [Finite F] {p d : ℕ} {f : ℤ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f.toNat)
    (A : Subgroup (F ≃+* F)) (hAd : Nat.card A = d) (hd : Odd d)
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hetaz : eta (zInLambda F A pi z hker) = (-1 : Matrix.SpecialLinearGroup (Fin 2) F))
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    FixedCentralizerConclusions F A pi z hzc hker eta p f.toNat d ∧
      (d : ℤ) ∣ f ∧ Nat.card (F0 F A) = p ^ (f / (d : ℤ)).toNat ∧
      Nat.card (M0 F A pi) = 2 * p ^ (f / (d : ℤ)).toNat * ((p ^ (f / (d : ℤ)).toNat)^2 - 1) := by
  have h := odd_field_lift_fixed_centralizer_and_Sylow F hp hpodd (by omega) hcard A hAd hd
    pi hpi z hz hzc hker eta hetaz heta
  have hf0 : 0 ≤ f := by omega
  have heq : (f / (d : ℤ)).toNat = f.toNat / d := by
    rw [← Int.toNat_of_nonneg hf0, ← Int.natCast_ediv]
    simp only [Int.toNat_natCast]
  refine ⟨h,?_,?_,?_⟩
  · rw [← Int.toNat_of_nonneg hf0]
    exact_mod_cast h.degree_dvd
  · rw [heq]
    exact h.fixed_card
  · rw [heq]
    exact h.M0_card


end

end CFSG.Semidihedral.FixedFieldCentralizer
