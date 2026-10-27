module

public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions
public import CFSG.CharacterTheory.Wreathed.OddLinearTwoAutomorphisms
public import CFSG.CharacterTheory.Wreathed.CyclicOddScalarQuotient

public noncomputable section

open scoped MatrixGroups
namespace CFSG.Wreathed.OddLinearThreeCentralizerCore
universe u v
variable (F : Type u) [Field F]
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) F

theorem center_cube_eq_one (g : SL3 F) (hg : g ∈ Subgroup.center (SL3 F)) :
    g ^ 3 = 1 := by
  obtain ⟨a, ha, hm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha3 : a ^ 3 = 1 := by simpa using ha
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hm]
  rw [← map_pow, ha3, map_one]

theorem scalar_kernel_odd [Finite F] (D : Subgroup (SL3 F))
    (hD : D ≤ Subgroup.center (SL3 F)) : Odd (Nat.card D) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 heven.two_dvd
  have hc : d ^ 3 = 1 := Subtype.ext (center_cube_eq_one F d (hD d.property))
  have hdiv : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  rw [hd] at hdiv
  omega

theorem unique_involution_lift [Finite F] (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) (t : SL3 F ⧸ D) (ht : orderOf t = 2) :
    ∃! z : SL3 F, orderOf z = 2 ∧ QuotientGroup.mk' D z = t := by
  have hodd := scalar_kernel_odd F D hD
  obtain ⟨z, hz, hzt⟩ := OddNormalQuotientInvolutions.exists_involution_lift D hodd t ht
  refine ⟨z, ⟨hz, hzt⟩, ?_⟩
  intro w hw
  obtain ⟨d, hd⟩ := OddNormalQuotientInvolutions.exists_kernel_conjugator D hodd
    z w hz hw.1 (hw.2.trans hzt.symm)
  have hcomm := Subgroup.mem_center_iff.mp (hD d.property) z
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one] at hd
  exact hd.symm

theorem two_ne_zero [Finite F] (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    have ho : Fintype.card F % 2 = 1 := by
      simpa only [← Nat.card_eq_fintype_card] using Nat.odd_iff.mp hF
    omega
  intro hzero
  exact hchar (CharP.ringChar_of_prime_eq_zero Nat.prime_two hzero)

section Eigenspaces
variable {F} {V : Type v} [AddCommGroup V] [Module F V]

@[expose] def minusSpace (f : Module.End F V) : Submodule F V := f.eigenspace (-1)
@[expose] def plusSpace (f : Module.End F V) : Submodule F V := f.eigenspace 1

theorem involution_spaces_isCompl (h2 : (2 : F) ≠ 0)
    (f : Module.End F V) (hf : Function.Involutive f) :
    IsCompl (minusSpace f) (plusSpace f) := by
  have hne : (-1 : F) ≠ 1 := by
    intro h
    have : (2 : F) = 0 := by linear_combination -h
    exact h2 this
  refine ⟨f.disjoint_genEigenspace hne 1 1, ?_⟩
  apply codisjoint_iff.mpr
  apply top_unique
  intro v hv
  let a := (2 : F)⁻¹ • (v - f v)
  let b := (2 : F)⁻¹ • (v + f v)
  have ha : a ∈ minusSpace f := by
    rw [minusSpace, Module.End.mem_eigenspace_iff]
    simp only [a, map_smul, map_sub, hf v, neg_one_smul]
    module
  have hb : b ∈ plusSpace f := by
    rw [plusSpace, Module.End.mem_eigenspace_iff]
    simp only [b, map_smul, map_add, hf v, one_smul]
    module
  have hab : a + b = v := by
    dsimp [a, b]
    rw [← smul_add]
    have hvec : (v - f v) + (v + f v) = (2 : F) • v := by module
    rw [hvec, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [← hab]
  exact Submodule.add_mem_sup ha hb

variable [FiniteDimensional F V]

theorem involution_det_eq (h2 : (2 : F) ≠ 0)
    (f : Module.End F V) (hf : Function.Involutive f) :
    LinearMap.det f = (-1 : F) ^ Module.finrank F (minusSpace f) := by
  let E := Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f)
    (involution_spaces_isCompl h2 f hf)
  have hconj : E.toLinearMap ∘ₗ
      LinearMap.prodMap ((-1 : F) • LinearMap.id) LinearMap.id ∘ₗ
        E.symm.toLinearMap = f := by
    ext v
    obtain ⟨⟨a, b⟩, rfl⟩ := E.surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply,
      LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change (-1 : F) • (a : V) + (b : V) = f ((a : V) + (b : V))
    rw [map_add, Module.End.mem_eigenspace_iff.mp a.property,
      Module.End.mem_eigenspace_iff.mp b.property, one_smul]
  calc
    LinearMap.det f = LinearMap.det (E.toLinearMap ∘ₗ
        LinearMap.prodMap ((-1 : F) • LinearMap.id) LinearMap.id ∘ₗ
          E.symm.toLinearMap) := congrArg LinearMap.det hconj.symm
    _ = (-1 : F) ^ Module.finrank F (minusSpace f) := by
      rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
        LinearMap.det_id, LinearMap.det_id, mul_one, mul_one]

theorem involution_finrank_sum (h2 : (2 : F) ≠ 0)
    (f : Module.End F V) (hf : Function.Involutive f) :
    Module.finrank F (minusSpace f) + Module.finrank F (plusSpace f) =
      Module.finrank F V := by
  simpa only [Module.finrank_prod] using
    (Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f)
      (involution_spaces_isCompl h2 f hf)).finrank_eq

omit [FiniteDimensional F V] in
theorem involution_eq_id_of_minus_bot (h2 : (2 : F) ≠ 0)
    (f : Module.End F V) (hf : Function.Involutive f) (hminus : minusSpace f = ⊥) :
    f = LinearMap.id := by
  have hplus : plusSpace f = ⊤ := by
    have hsup := (involution_spaces_isCompl h2 f hf).sup_eq_top
    simpa only [hminus, bot_sup_eq] using hsup
  ext v
  have hv : v ∈ plusSpace f := by rw [hplus]; trivial
  simpa only [one_smul, LinearMap.id_apply] using Module.End.mem_eigenspace_iff.mp hv

theorem involution_finrank_three (h2 : (2 : F) ≠ 0)
    (f : Module.End F V) (hf : Function.Involutive f)
    (hdim : Module.finrank F V = 3) (hdet : LinearMap.det f = 1)
    (hne : f ≠ LinearMap.id) :
    Module.finrank F (minusSpace f) = 2 ∧ Module.finrank F (plusSpace f) = 1 := by
  have hsum := involution_finrank_sum h2 f hf
  rw [hdim] at hsum
  have hpos : Module.finrank F (minusSpace f) ≠ 0 := by
    intro hz
    exact hne (involution_eq_id_of_minus_bot h2 f hf (Submodule.finrank_eq_zero.mp hz))
  have hpow : (-1 : F) ^ Module.finrank F (minusSpace f) = 1 :=
    (involution_det_eq h2 f hf).symm.trans hdet
  have hneq : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hm : Module.finrank F (minusSpace f) = 2 := by
    have hcases : Module.finrank F (minusSpace f) = 1 ∨
        Module.finrank F (minusSpace f) = 2 ∨ Module.finrank F (minusSpace f) = 3 := by
      omega
    rcases hcases with h | h | h
    · rw [h, pow_one] at hpow
      exact (hneq hpow).elim
    · exact h
    · rw [h] at hpow
      have hcube : (-1 : F) ^ 3 = -1 := by ring
      rw [hcube] at hpow
      exact (hneq hpow).elim
  exact ⟨hm, by omega⟩
end Eigenspaces

@[expose] def matrixAction (z : SL3 F) : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) :=
  Matrix.SpecialLinearGroup.toLin' z

theorem matrixAction_involutive (z : SL3 F) (hz : orderOf z = 2) :
    Function.Involutive (matrixAction F z) := by
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hlin : matrixAction F z * matrixAction F z = 1 := by
    change Matrix.SpecialLinearGroup.toLin' z * Matrix.SpecialLinearGroup.toLin' z = 1
    rw [← map_mul, ← pow_two, hz2, map_one]
  intro v
  exact congrArg (fun a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) => a v) hlin

theorem matrixAction_finrank [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2) :
    Module.finrank F (minusSpace (matrixAction F z).toLinearMap) = 2 ∧
      Module.finrank F (plusSpace (matrixAction F z).toLinearMap) = 1 := by
  apply involution_finrank_three (two_ne_zero F hF) _ (matrixAction_involutive F z hz)
  · simp
  · exact _root_.SpecialLinearGroup.det_eq_one (Matrix.SpecialLinearGroup.toLin'_equiv z)
  · intro h
    have he : Matrix.SpecialLinearGroup.toLin'_equiv z = 1 := by
      apply Subtype.ext
      exact LinearEquiv.toLinearMap_injective h
    have hz1 : z = 1 := Matrix.SpecialLinearGroup.toLin'_equiv.injective (by
      simpa only [map_one] using he)
    rw [hz1, orderOf_one] at hz
    omega
section BlockExtension
variable {F} {P : Type v} {Q : Type*} {V : Type*}
  [AddCommGroup P] [Module F P] [FiniteDimensional F P]
  [AddCommGroup Q] [Module F Q] [FiniteDimensional F Q]
  [AddCommGroup V] [Module F V]

@[expose] def blockExtension (E : (P × Q) ≃ₗ[F] V) (a : P ≃ₗ[F] P) : V ≃ₗ[F] V :=
  (E.symm.trans (a.prodCongr (LinearEquiv.smulOfUnit a.det⁻¹))).trans E

omit [FiniteDimensional F P] [FiniteDimensional F Q] in
theorem blockExtension_left (E : (P × Q) ≃ₗ[F] V) (a : P ≃ₗ[F] P) (x : P) :
    blockExtension E a (E (x, 0)) = E (a x, 0) := by
  simp [blockExtension]

omit [FiniteDimensional F P] [FiniteDimensional F Q] in
theorem blockExtension_right (E : (P × Q) ≃ₗ[F] V) (a : P ≃ₗ[F] P) (y : Q) :
    blockExtension E a (E (0, y)) = E (0, (a.det⁻¹ : Fˣ) • y) := by
  simp [blockExtension, LinearEquiv.smulOfUnit]

theorem blockExtension_det (hQ : Module.finrank F Q = 1)
    (E : (P × Q) ≃ₗ[F] V) (a : P ≃ₗ[F] P) :
    (blockExtension E a).det = 1 := by
  rw [blockExtension, LinearEquiv.det_conj]
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_one]
  change LinearMap.det (LinearMap.prodMap a.toLinearMap
    (LinearEquiv.smulOfUnit (M := Q) a.det⁻¹).toLinearMap) = (1 : F)
  have hs : (LinearEquiv.smulOfUnit (M := Q) a.det⁻¹).toLinearMap =
      ((a.det⁻¹ : Fˣ) : F) • LinearMap.id := by
    ext y
    rfl
  rw [hs, LinearMap.det_prodMap, LinearMap.det_smul, hQ, pow_one,
    LinearMap.det_id, mul_one, ← LinearEquiv.coe_det]
  exact congrArg Units.val (mul_inv_cancel a.det)

omit [FiniteDimensional F P] [FiniteDimensional F Q] in
theorem blockExtension_mul (E : (P × Q) ≃ₗ[F] V) (a b : P ≃ₗ[F] P) :
    blockExtension E (a * b) = blockExtension E a * blockExtension E b := by
  ext v
  obtain ⟨⟨x, y⟩, rfl⟩ := E.surjective v
  simp only [blockExtension, LinearEquiv.trans_apply, E.symm_apply_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.mul_apply]
  apply congrArg E
  apply Prod.ext
  · rfl
  · change ((a * b).det⁻¹ : Fˣ) • y = (a.det⁻¹ : Fˣ) • ((b.det⁻¹ : Fˣ) • y)
    rw [map_mul, mul_inv_rev, mul_comm, mul_smul]

@[expose] def blockSpecialLinear (hQ : Module.finrank F Q = 1)
    (E : (P × Q) ≃ₗ[F] V) : (P ≃ₗ[F] P) →* _root_.SpecialLinearGroup F V where
  toFun a := ⟨blockExtension E a, blockExtension_det hQ E a⟩
  map_one' := by
    apply Subtype.ext
    ext v
    obtain ⟨⟨x, y⟩, rfl⟩ := E.surjective v
    simp [blockExtension, LinearEquiv.smulOfUnit]
  map_mul' a b := Subtype.ext (blockExtension_mul E a b)
end BlockExtension
section CentralizerRestrictions
variable {F} {V : Type*} [AddCommGroup V] [Module F V]

theorem commuting_map_eigenspace (f : Module.End F V) (g : V ≃ₗ[F] V)
    (hc : ∀ v, f (g v) = g (f v)) (mu : F) :
    (f.eigenspace mu).map g.toLinearMap = f.eigenspace mu := by
  apply le_antisymm
  · rintro v ⟨x, hx, rfl⟩
    change x ∈ f.eigenspace mu at hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change f (g x) = mu • g x
    rw [hc, hx, map_smul]
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    refine Submodule.mem_map.mpr ⟨g.symm v, ?_, g.apply_symm_apply v⟩
    rw [Module.End.mem_eigenspace_iff]
    apply g.injective
    rw [← hc, g.apply_symm_apply, map_smul, g.apply_symm_apply, hv]

@[expose] def eigenspaceRestriction (f : Module.End F V) (mu : F) (g : V ≃ₗ[F] V)
    (hc : ∀ v, f (g v) = g (f v)) :
    f.eigenspace mu ≃ₗ[F] f.eigenspace mu :=
  g.ofSubmodules _ _ (commuting_map_eigenspace f g hc mu)

theorem eigenspaceRestriction_apply (f : Module.End F V) (mu : F) (g : V ≃ₗ[F] V)
    (hc : ∀ v, f (g v) = g (f v)) (x : f.eigenspace mu) :
    (eigenspaceRestriction f mu g hc x : V) = g x :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem commuting_eq_restriction_blocks (f : Module.End F V)
    (hcompl : IsCompl (minusSpace f) (plusSpace f)) (g : V ≃ₗ[F] V)
    (hc : ∀ v, f (g v) = g (f v)) :
    g = ((Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl).symm.trans
      ((eigenspaceRestriction f (-1) g hc).prodCongr
        (eigenspaceRestriction f 1 g hc))).trans
          (Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl) := by
  unfold minusSpace plusSpace at hcompl ⊢
  let E := Submodule.prodEquivOfIsCompl (f.eigenspace (-1)) (f.eigenspace 1) hcompl
  change g = (E.symm.trans ((eigenspaceRestriction f (-1) g hc).prodCongr
    (eigenspaceRestriction f 1 g hc))).trans E
  ext v
  obtain ⟨⟨x, y⟩, rfl⟩ := E.surjective v
  simp only [LinearEquiv.trans_apply, E.symm_apply_apply, LinearEquiv.prodCongr_apply]
  change g ((x : V) + (y : V)) =
    (eigenspaceRestriction f (-1) g hc x : V) +
      (eigenspaceRestriction f 1 g hc y : V)
  rw [map_add, eigenspaceRestriction_apply, eigenspaceRestriction_apply]

variable [FiniteDimensional F V]

theorem line_equiv_eq_smul_det {Q : Type*} [AddCommGroup Q] [Module F Q]
    (hQ : Module.finrank F Q = 1) (b : Q ≃ₗ[F] Q) :
    b = LinearEquiv.smulOfUnit b.det := by
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hQ b.toLinearMap
  have hdet : (b.det : F) = c := by
    rw [LinearEquiv.coe_det, hc, LinearMap.det_smul, hQ, pow_one,
      LinearMap.det_id, mul_one]
  apply LinearEquiv.toLinearMap_injective
  rw [hc, ← hdet]
  rfl

theorem prodCongr_det {P Q : Type*} [AddCommGroup P] [Module F P]
    [AddCommGroup Q] [Module F Q] [FiniteDimensional F P] [FiniteDimensional F Q]
    (a : P ≃ₗ[F] P) (b : Q ≃ₗ[F] Q) :
    (a.prodCongr b).det = a.det * b.det := by
  apply Units.ext
  simp only [Units.val_mul, LinearEquiv.coe_det]
  exact LinearMap.det_prodMap a.toLinearMap b.toLinearMap

theorem commuting_det_one_eq_block (f : Module.End F V)
    (hcompl : IsCompl (minusSpace f) (plusSpace f))
    (hplus : Module.finrank F (plusSpace f) = 1) (g : V ≃ₗ[F] V)
    (hc : ∀ v, f (g v) = g (f v)) (hdet : g.det = 1) :
    g = blockExtension
      (Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl)
      (eigenspaceRestriction f (-1) g hc) := by
  unfold minusSpace plusSpace at hcompl ⊢
  unfold plusSpace at hplus
  let E := Submodule.prodEquivOfIsCompl (f.eigenspace (-1)) (f.eigenspace 1) hcompl
  let a := eigenspaceRestriction f (-1) g hc
  let b := eigenspaceRestriction f 1 g hc
  have hblocks : g = (E.symm.trans (a.prodCongr b)).trans E :=
    commuting_eq_restriction_blocks f hcompl g hc
  have hbdet : b.det = a.det⁻¹ := by
    have hab : a.det * b.det = 1 := by
      rw [hblocks, LinearEquiv.det_conj, prodCongr_det] at hdet
      exact hdet
    exact eq_inv_of_mul_eq_one_right hab
  calc
    g = (E.symm.trans (a.prodCongr b)).trans E := hblocks
    _ = blockExtension E a := by
      rw [line_equiv_eq_smul_det hplus b, hbdet]
      rfl
end CentralizerRestrictions
section SpecialCentralizerEquivalence
variable {F} {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem blockExtension_commutes (f : Module.End F V)
    (hcompl : IsCompl (minusSpace f) (plusSpace f))
    (a : minusSpace f ≃ₗ[F] minusSpace f) :
    ∀ v, f (blockExtension
      (Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl) a v) =
      blockExtension (Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl)
        a (f v) := by
  let E := Submodule.prodEquivOfIsCompl (minusSpace f) (plusSpace f) hcompl
  intro v
  obtain ⟨⟨x, y⟩, rfl⟩ := E.surjective v
  change f (blockExtension E a ((x : V) + (y : V))) =
    blockExtension E a (f ((x : V) + (y : V)))
  have hx : f x = (-1 : F) • (x : V) := Module.End.mem_eigenspace_iff.mp x.property
  have hy : f y = (y : V) := by
    simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp y.property
  have hax : f (a x) = (-1 : F) • (a x : V) :=
    Module.End.mem_eigenspace_iff.mp (a x).property
  have hleft : blockExtension E a (x : V) = (a x : V) :=
    by
      have h := blockExtension_left E a x
      change blockExtension E a ((x : V) + (0 : V)) = (a x : V) + 0 at h
      simpa only [add_zero] using h
  have hright : blockExtension E a (y : V) = ((a.det⁻¹ : Fˣ) : F) • (y : V) :=
    by
      have h := blockExtension_right E a y
      change blockExtension E a ((0 : V) + (y : V)) =
        (0 : V) + ((a.det⁻¹ : Fˣ) : F) • (y : V) at h
      simpa only [zero_add] using h
  rw [map_add, hleft, hright, map_add, hax, f.map_smul, hy,
    map_add, hx, hy, map_add, LinearEquiv.map_smul, hleft, hright]

omit [FiniteDimensional F V] in
theorem centralizer_commutes (z : _root_.SpecialLinearGroup F V)
    (g : Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V))) :
    ∀ v, z.val (g.val.val v) = g.val.val (z.val v) := by
  have he := Subgroup.mem_centralizer_singleton_iff.mp g.property
  intro v
  exact (congrArg (fun k : _root_.SpecialLinearGroup F V => k v) he).symm

@[expose] def specialCentralizerRestriction (z : _root_.SpecialLinearGroup F V) :
    Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V)) →*
      (minusSpace z.val.toLinearMap ≃ₗ[F] minusSpace z.val.toLinearMap) where
  toFun g := eigenspaceRestriction z.val.toLinearMap (-1) g.val.val
    (centralizer_commutes z g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact eigenspaceRestriction_apply z.val.toLinearMap (-1) _ _ x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp only [eigenspaceRestriction_apply]
    rfl

theorem blockSpecialLinear_mem_centralizer (z : _root_.SpecialLinearGroup F V)
    (hcompl : IsCompl (minusSpace z.val.toLinearMap) (plusSpace z.val.toLinearMap))
    (hplus : Module.finrank F (plusSpace z.val.toLinearMap) = 1)
    (a : minusSpace z.val.toLinearMap ≃ₗ[F] minusSpace z.val.toLinearMap) :
    blockSpecialLinear hplus
      (Submodule.prodEquivOfIsCompl (minusSpace z.val.toLinearMap)
        (plusSpace z.val.toLinearMap) hcompl) a ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply _root_.SpecialLinearGroup.ext
  intro v
  exact (blockExtension_commutes z.val.toLinearMap hcompl a v).symm

@[expose] def specialCentralizerBlock (z : _root_.SpecialLinearGroup F V)
    (hcompl : IsCompl (minusSpace z.val.toLinearMap) (plusSpace z.val.toLinearMap))
    (hplus : Module.finrank F (plusSpace z.val.toLinearMap) = 1) :
    (minusSpace z.val.toLinearMap ≃ₗ[F] minusSpace z.val.toLinearMap) →*
      Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V)) where
  toFun a := ⟨blockSpecialLinear hplus
    (Submodule.prodEquivOfIsCompl (minusSpace z.val.toLinearMap)
      (plusSpace z.val.toLinearMap) hcompl) a,
        blockSpecialLinear_mem_centralizer z hcompl hplus a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

omit [FiniteDimensional F V] in
theorem specialCentralizerRestriction_apply (z : _root_.SpecialLinearGroup F V)
    (g : Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V)))
    (x : minusSpace z.val.toLinearMap) :
    (specialCentralizerRestriction z g x : V) = g.val.val x :=
  eigenspaceRestriction_apply z.val.toLinearMap (-1) g.val.val
    (centralizer_commutes z g) x

theorem specialCentralizerRestriction_block (z : _root_.SpecialLinearGroup F V)
    (hcompl : IsCompl (minusSpace z.val.toLinearMap) (plusSpace z.val.toLinearMap))
    (hplus : Module.finrank F (plusSpace z.val.toLinearMap) = 1)
    (a : minusSpace z.val.toLinearMap ≃ₗ[F] minusSpace z.val.toLinearMap) :
    specialCentralizerRestriction z (specialCentralizerBlock z hcompl hplus a) = a := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [specialCentralizerRestriction_apply]
  have h := blockExtension_left
    (Submodule.prodEquivOfIsCompl (minusSpace z.val.toLinearMap)
      (plusSpace z.val.toLinearMap) hcompl) a x
  change blockExtension _ a ((x : V) + (0 : V)) = (a x : V) + 0 at h
  simpa only [add_zero, specialCentralizerBlock, blockSpecialLinear, MonoidHom.coe_mk,
    OneHom.coe_mk] using h

theorem specialCentralizerBlock_restriction (z : _root_.SpecialLinearGroup F V)
    (hcompl : IsCompl (minusSpace z.val.toLinearMap) (plusSpace z.val.toLinearMap))
    (hplus : Module.finrank F (plusSpace z.val.toLinearMap) = 1)
    (g : Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V))) :
    specialCentralizerBlock z hcompl hplus (specialCentralizerRestriction z g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact (commuting_det_one_eq_block z.val.toLinearMap hcompl hplus g.val.val
    (centralizer_commutes z g) g.val.property).symm

@[expose] def specialCentralizerEquiv (z : _root_.SpecialLinearGroup F V)
    (hcompl : IsCompl (minusSpace z.val.toLinearMap) (plusSpace z.val.toLinearMap))
    (hplus : Module.finrank F (plusSpace z.val.toLinearMap) = 1) :
    (minusSpace z.val.toLinearMap ≃ₗ[F] minusSpace z.val.toLinearMap) ≃*
      Subgroup.centralizer ({z} : Set (_root_.SpecialLinearGroup F V)) where
  toFun := specialCentralizerBlock z hcompl hplus
  invFun := specialCentralizerRestriction z
  left_inv := specialCentralizerRestriction_block z hcompl hplus
  right_inv := specialCentralizerBlock_restriction z hcompl hplus
  map_mul' := (specialCentralizerBlock z hcompl hplus).map_mul
end SpecialCentralizerEquivalence
section MatrixCentralizer
@[expose] def matrixSpecialEquiv : SL3 F ≃* SpecialLinearGroup F (Fin 3 → F) :=
  Matrix.SpecialLinearGroup.toLin'_equiv

@[expose] def centralizerTransport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) :
    Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer ({e z} : Set H) where
  toFun g := ⟨e g, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp g.property))⟩
  invFun g := ⟨e.symm g, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul, e.symm_apply_apply] using
      congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp g.property))⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g)
  right_inv g := Subtype.ext (e.apply_symm_apply g)
  map_mul' g h := Subtype.ext (e.map_mul g h)

theorem centralizerTransport_apply {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) (g : Subgroup.centralizer ({z} : Set G)) :
    (centralizerTransport e z g : H) = e g := rfl

set_option maxHeartbeats 2000000 in
@[expose] def matrixCentralizerEquiv [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2) :
    (minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) ≃*
        Subgroup.centralizer ({z} : Set (SL3 F)) :=
  (specialCentralizerEquiv (matrixSpecialEquiv F z)
    (involution_spaces_isCompl (two_ne_zero F hF)
      (matrixAction F z).toLinearMap (matrixAction_involutive F z hz))
    (matrixAction_finrank F hF z hz).2).trans
      (centralizerTransport (matrixSpecialEquiv F) z).symm

theorem matrixCentralizerEquiv_action [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2)
    (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) :
    matrixAction F (matrixCentralizerEquiv F hF z hz a) =
      blockExtension (Submodule.prodEquivOfIsCompl
        (minusSpace (matrixAction F z).toLinearMap)
        (plusSpace (matrixAction F z).toLinearMap)
        (involution_spaces_isCompl (two_ne_zero F hF)
          (matrixAction F z).toLinearMap (matrixAction_involutive F z hz))) a := by
  change (matrixSpecialEquiv F ((matrixSpecialEquiv F).symm
    ((specialCentralizerBlock (matrixSpecialEquiv F z) _ _ a).val))).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem matrixCentralizerEquiv_minus [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2)
    (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap)
    (x : minusSpace (matrixAction F z).toLinearMap) :
    matrixAction F (matrixCentralizerEquiv F hF z hz a) (x : Fin 3 → F) = a x := by
  let E := Submodule.prodEquivOfIsCompl
    (minusSpace (matrixAction F z).toLinearMap)
    (plusSpace (matrixAction F z).toLinearMap)
    (involution_spaces_isCompl (two_ne_zero F hF)
      (matrixAction F z).toLinearMap (matrixAction_involutive F z hz))
  rw [matrixCentralizerEquiv_action]
  have h := blockExtension_left E a x
  change blockExtension E a ((x : Fin 3 → F) + (0 : Fin 3 → F)) =
    (a x : Fin 3 → F) + 0 at h
  simpa only [add_zero] using h

theorem matrixCentralizerEquiv_plus [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2)
    (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap)
    (y : plusSpace (matrixAction F z).toLinearMap) :
    matrixAction F (matrixCentralizerEquiv F hF z hz a) (y : Fin 3 → F) =
      ((a.det⁻¹ : Fˣ) : F) • (y : Fin 3 → F) := by
  let E := Submodule.prodEquivOfIsCompl
    (minusSpace (matrixAction F z).toLinearMap)
    (plusSpace (matrixAction F z).toLinearMap)
    (involution_spaces_isCompl (two_ne_zero F hF)
      (matrixAction F z).toLinearMap (matrixAction_involutive F z hz))
  rw [matrixCentralizerEquiv_action]
  have h := blockExtension_right E a y
  change blockExtension E a ((0 : Fin 3 → F) + (y : Fin 3 → F)) =
    (0 : Fin 3 → F) + ((a.det⁻¹ : Fˣ) : F) • (y : Fin 3 → F) at h
  simpa only [zero_add] using h

@[expose] def matrixQuotientCentralizer [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2) :
    (minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) →*
        Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) :=
  (OddNormalQuotientInvolutions.centralizerQuotient D z).comp
    (matrixCentralizerEquiv F hF z hz).toMonoidHom

theorem matrixQuotientCentralizer_surjective [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    Function.Surjective (matrixQuotientCentralizer F hF D z hz) :=
  (OddNormalQuotientInvolutions.centralizerQuotient_surjective D
    (scalar_kernel_odd F D hD) z hz).comp (matrixCentralizerEquiv F hF z hz).surjective

theorem matrixQuotientCentralizer_coe [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) :
    (matrixQuotientCentralizer F hF D z hz a : SL3 F ⧸ D) =
      QuotientGroup.mk' D (matrixCentralizerEquiv F hF z hz a) := rfl

end MatrixCentralizer
section MatrixScalarKernel
@[expose] def matrixScalar (c : Fˣ) (hc : c ^ 3 = 1) : SL3 F :=
  ⟨(c : F) • (1 : Matrix (Fin 3) (Fin 3) F), by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    simpa only [Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val hc⟩

theorem matrixScalar_center (c : Fˣ) (hc : c ^ 3 = 1) :
    matrixScalar F c hc ∈ Subgroup.center (SL3 F) := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(c : F), ?_, ?_⟩
  · simpa only [Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val hc
  · ext i j
    simp [matrixScalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem matrixScalar_action (c : Fˣ) (hc : c ^ 3 = 1) :
    matrixAction F (matrixScalar F c hc) = LinearEquiv.smulOfUnit c := by
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin' ((c : F) • (1 : Matrix (Fin 3) (Fin 3) F)) v = (c : F) • v
  rw [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem center_eq_matrixScalar (g : SL3 F) (hg : g ∈ Subgroup.center (SL3 F)) :
    ∃ (c : Fˣ) (hc : c ^ 3 = 1), matrixScalar F c hc = g := by
  obtain ⟨a, ha, hm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha3 : a ^ 3 = 1 := by simpa only [Fintype.card_fin] using ha
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 3 ≠ 0)] at ha3
    exact zero_ne_one ha3
  let c := Units.mk0 a ha0
  have hc : c ^ 3 = 1 := Units.ext ha3
  refine ⟨c, hc, ?_⟩
  apply Subtype.ext
  change (a : F) • (1 : Matrix (Fin 3) (Fin 3) F) = (g : Matrix _ _ F)
  rw [← hm]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem minus_scalar_det [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2) (c : Fˣ) :
    (LinearEquiv.smulOfUnit
      (M := minusSpace (matrixAction F z).toLinearMap) c).det = c ^ 2 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hs : (LinearEquiv.smulOfUnit
      (M := minusSpace (matrixAction F z).toLinearMap) c).toLinearMap =
      (c : F) • LinearMap.id := by ext x; rfl
  rw [hs, LinearMap.det_smul, (matrixAction_finrank F hF z hz).1,
    LinearMap.det_id, mul_one]
  rfl

theorem matrixCentralizerEquiv_scalar [Finite F] (hF : Odd (Nat.card F))
    (z : SL3 F) (hz : orderOf z = 2) (c : Fˣ) (hc : c ^ 3 = 1) :
    (matrixCentralizerEquiv F hF z hz
      (LinearEquiv.smulOfUnit c) : SL3 F) = matrixScalar F c hc := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  change matrixAction F _ = matrixAction F _
  rw [matrixCentralizerEquiv_action, matrixScalar_action]
  let E := Submodule.prodEquivOfIsCompl
    (minusSpace (matrixAction F z).toLinearMap)
    (plusSpace (matrixAction F z).toLinearMap)
    (involution_spaces_isCompl (two_ne_zero F hF)
      (matrixAction F z).toLinearMap (matrixAction_involutive F z hz))
  have hcinv : (c ^ 2)⁻¹ = c := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ] using hc
  apply LinearEquiv.ext
  intro v
  obtain ⟨⟨x, y⟩, rfl⟩ := E.surjective v
  change blockExtension E (LinearEquiv.smulOfUnit c) (E (x, y)) =
    (c : F) • E (x, y)
  simp only [blockExtension, LinearEquiv.trans_apply, E.symm_apply_apply,
    LinearEquiv.prodCongr_apply, minus_scalar_det F hF z hz c, hcinv]
  change E ((c : F) • x, (c : F) • y) = (c : F) • E (x, y)
  exact E.map_smul c (x, y)

variable {F} in
theorem matrixQuotientCentralizer_mem_ker_iff [Finite F] (hF : Odd (Nat.card F))
    {D : Subgroup (SL3 F)} [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    {z : SL3 F} (hz : orderOf z = 2)
    {a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap} :
    a ∈ (matrixQuotientCentralizer F hF D z hz).ker ↔
      ∃ (c : Fˣ) (hc : c ^ 3 = 1), matrixScalar F c hc ∈ D ∧
        a = LinearEquiv.smulOfUnit c := by
  constructor
  · intro ha
    have hd : (matrixCentralizerEquiv F hF z hz a : SL3 F) ∈ D :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ha)
    obtain ⟨c, hc, he⟩ := center_eq_matrixScalar F _ (hD hd)
    refine ⟨c, hc, he.symm ▸ hd, ?_⟩
    apply (matrixCentralizerEquiv F hF z hz).injective
    apply Subtype.ext
    rw [matrixCentralizerEquiv_scalar F hF z hz c hc, he]
  · rintro ⟨c, hc, hd, rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' D (matrixCentralizerEquiv F hF z hz
      (LinearEquiv.smulOfUnit c) : SL3 F) = 1
    rw [matrixCentralizerEquiv_scalar F hF z hz c hc]
    exact (QuotientGroup.eq_one_iff _).mpr hd


theorem D_le_matrixCentralizer (D : Subgroup (SL3 F))
    (hD : D ≤ Subgroup.center (SL3 F)) (z : SL3 F) :
    D ≤ Subgroup.centralizer ({z} : Set (SL3 F)) := by
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_center_iff.mp (hD hd) z).symm

@[expose] def matrixQuotientKernelEquiv [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    (matrixQuotientCentralizer F hF D z hz).ker ≃* D :=
  (MulEquiv.subgroupCongr (MonoidHom.ker_comp_mulEquiv
    (OddNormalQuotientInvolutions.centralizerQuotient D z)
      (matrixCentralizerEquiv F hF z hz))).trans
    (((matrixCentralizerEquiv F hF z hz).symm.subgroupMap
      (OddNormalQuotientInvolutions.centralizerQuotient D z).ker).symm.trans
      ((MulEquiv.subgroupCongr
        (OddNormalQuotientInvolutions.centralizerQuotient_ker D z)).trans
          (Subgroup.subgroupOfEquivOfLe (D_le_matrixCentralizer F D hD z))))

theorem matrixQuotientKernelEquiv_coe [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2)
    (a : (matrixQuotientCentralizer F hF D z hz).ker) :
    (matrixQuotientKernelEquiv F hF D hD z hz a : SL3 F) =
      (matrixCentralizerEquiv F hF z hz a : SL3 F) := by
  rfl

theorem matrixQuotientKernel_card [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    Nat.card (matrixQuotientCentralizer F hF D z hz).ker = Nat.card D :=
  Nat.card_congr (matrixQuotientKernelEquiv F hF D hD z hz).toEquiv

theorem matrixQuotientKernel_odd [Finite F] (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    Odd (Nat.card (matrixQuotientCentralizer F hF D z hz).ker) := by
  rw [matrixQuotientKernel_card F hF D hD z hz]
  exact scalar_kernel_odd F D hD

end MatrixScalarKernel
section FullCentralizerCore
open scoped Nat
variable [Finite F]

theorem matrixQuotientKernel_le_scalars (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    (matrixQuotientCentralizer F hF D z hz).ker ≤
      (OddLinearTwoAutomorphisms.scalarHom F
        (minusSpace (matrixAction F z).toLinearMap)).range := by
  intro a ha
  obtain ⟨c, _, _, he⟩ := (matrixQuotientCentralizer_mem_ker_iff hF hD hz).mp ha
  exact ⟨c, he.symm⟩

theorem matrixQuotientCentralizer_core_structure (hF : Odd (Nat.card F))
    (hq : 3 ≤ Nat.card F) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) (z : SL3 F) (hz : orderOf z = 2) :
    CFSG.oddCore (Subgroup.centralizer
      ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) =
      ((CyclicOddScalarQuotient.oddElements Fˣ).map
        (OddLinearTwoAutomorphisms.scalarHom F
          (minusSpace (matrixAction F z).toLinearMap))).map
            (matrixQuotientCentralizer F hF D z hz) ∧
      CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) ≤
          Subgroup.center (Subgroup.centralizer
            ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)))) =
          ordCompl[2] (Nat.card F - 1) / Nat.card D := by
  let P := minusSpace (matrixAction F z).toLinearMap
  have hP : Module.finrank F P = 2 := (matrixAction_finrank F hF z hz).1
  let : Finite (P ≃ₗ[F] P) := OddLinearTwoAutomorphisms.finite_automorphisms F P hP
  have h := CyclicOddScalarQuotient.quotient_oddCore_structure
    (OddLinearTwoAutomorphisms.scalarHom F P)
    (OddLinearTwoAutomorphisms.scalarHom_injective F P hP)
    (OddLinearTwoAutomorphisms.scalarHom_central F P)
    (matrixQuotientCentralizer F hF D z hz)
    (matrixQuotientCentralizer_surjective F hF D hD z hz)
    (matrixQuotientKernel_odd F hF D hD z hz)
    (matrixQuotientKernel_le_scalars F hF D hD z hz)
    (OddLinearTwoAutomorphisms.normal_odd_is_scalar F P hF hq hP)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  calc
    Nat.card (CFSG.oddCore (Subgroup.centralizer
      ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)))) =
        ordCompl[2] (Nat.card Fˣ) /
          Nat.card (matrixQuotientCentralizer F hF D z hz).ker := h.2.2.2
    _ = ordCompl[2] (Nat.card F - 1) / Nat.card D := by
      rw [Nat.card_units, matrixQuotientKernel_card F hF D hD z hz]

theorem matrixQuotientCentralizer_card (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer
      ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) =
        (Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1)) / Nat.card D := by
  have hc := Subgroup.card_ker_mul_card_of_surjective
    (matrixQuotientCentralizer_surjective F hF D hD z hz)
  rw [matrixQuotientKernel_card F hF D hD z hz,
    OddLinearTwoAutomorphisms.card_automorphisms F
      (minusSpace (matrixAction F z).toLinearMap) (matrixAction_finrank F hF z hz).1] at hc
  exact Nat.eq_div_of_mul_eq_right Nat.card_pos.ne' hc

@[expose] def targetCentralizerEquiv (D : Subgroup (SL3 F)) [D.Normal]
    (z : SL3 F) (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D)) ≃*
      Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)) :=
  MulEquiv.subgroupCongr (congrArg (fun x : SL3 F ⧸ D =>
    Subgroup.centralizer ({x} : Set (SL3 F ⧸ D))) hzt)

omit [Finite F] in
theorem targetCentralizerEquiv_coe (D : Subgroup (SL3 F)) [D.Normal]
    (z : SL3 F) (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (g : Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) :
    (targetCentralizerEquiv F D z t hzt g : SL3 F ⧸ D) = g :=
  MulEquiv.subgroupCongr_apply _ g

@[expose] def targetQuotientCentralizer (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    (minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) →*
        Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)) :=
  (targetCentralizerEquiv F D z t hzt).toMonoidHom.comp
    (matrixQuotientCentralizer F hF D z hz)

theorem targetQuotientCentralizer_coe (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) :
    (targetQuotientCentralizer F hF D z hz t hzt a : SL3 F ⧸ D) =
      QuotientGroup.mk' D (matrixCentralizerEquiv F hF z hz a) := by
  exact (targetCentralizerEquiv_coe F D z t hzt _).trans
    (matrixQuotientCentralizer_coe F hF D z hz a)

theorem targetQuotientCentralizer_surjective (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D)
    (hzt : QuotientGroup.mk' D z = t) :
    Function.Surjective (targetQuotientCentralizer F hF D z hz t hzt) :=
  (targetCentralizerEquiv F D z t hzt).surjective.comp
    (matrixQuotientCentralizer_surjective F hF D hD z hz)

theorem targetQuotientCentralizer_ker (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    (targetQuotientCentralizer F hF D z hz t hzt).ker =
      (matrixQuotientCentralizer F hF D z hz).ker :=
  MonoidHom.ker_comp_of_injective _ _ (targetCentralizerEquiv F D z t hzt).injective

theorem targetQuotientCentralizer_core_structure (hF : Odd (Nat.card F))
    (hq : 3 ≤ Nat.card F) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) (z : SL3 F) (hz : orderOf z = 2)
    (t : SL3 F ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) =
      ((CyclicOddScalarQuotient.oddElements Fˣ).map
        (OddLinearTwoAutomorphisms.scalarHom F
          (minusSpace (matrixAction F z).toLinearMap))).map
            (targetQuotientCentralizer F hF D z hz t hzt) ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) =
        ordCompl[2] (Nat.card F - 1) / Nat.card D := by
  let P := minusSpace (matrixAction F z).toLinearMap
  have hP : Module.finrank F P = 2 := (matrixAction_finrank F hF z hz).1
  let : Finite (P ≃ₗ[F] P) := OddLinearTwoAutomorphisms.finite_automorphisms F P hP
  have hk := targetQuotientCentralizer_ker F hF D z hz t hzt
  have h := CyclicOddScalarQuotient.quotient_oddCore_structure
    (OddLinearTwoAutomorphisms.scalarHom F P)
    (OddLinearTwoAutomorphisms.scalarHom_injective F P hP)
    (OddLinearTwoAutomorphisms.scalarHom_central F P)
    (targetQuotientCentralizer F hF D z hz t hzt)
    (targetQuotientCentralizer_surjective F hF D hD z hz t hzt)
    (by rw [hk]; exact matrixQuotientKernel_odd F hF D hD z hz)
    (by rw [hk]; exact matrixQuotientKernel_le_scalars F hF D hD z hz)
    (OddLinearTwoAutomorphisms.normal_odd_is_scalar F P hF hq hP)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  calc
    Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) =
      ordCompl[2] (Nat.card Fˣ) /
        Nat.card (targetQuotientCentralizer F hF D z hz t hzt).ker := h.2.2.2
    _ = ordCompl[2] (Nat.card F - 1) / Nat.card D := by
      rw [Nat.card_units, hk, matrixQuotientKernel_card F hF D hD z hz]

theorem targetQuotientCentralizer_card (hF : Odd (Nat.card F))
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ Subgroup.center (SL3 F))
    (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D)
    (hzt : QuotientGroup.mk' D z = t) :
    Nat.card (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) =
      (Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1)) / Nat.card D := by
  rw [← Nat.card_congr (targetCentralizerEquiv F D z t hzt).toEquiv]
  exact matrixQuotientCentralizer_card F hF D hD z hz

theorem mem_targetCentralizer_oddCore_iff {F : Type u} [Field F] [Finite F] {hF : Odd (Nat.card F)}
    {hq : 3 ≤ Nat.card F} {D : Subgroup (SL3 F)} [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) {z : SL3 F} (hz : orderOf z = 2)
    {t : SL3 F ⧸ D} (hzt : QuotientGroup.mk' D z = t)
    {g : Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))} :
    g ∈ CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) ↔
      ∃ c : Fˣ, Odd (orderOf c) ∧
        targetQuotientCentralizer F hF D z hz t hzt (LinearEquiv.smulOfUnit c) = g := by
  rw [(targetQuotientCentralizer_core_structure F hF hq D hD z hz t hzt).1]
  constructor
  · rintro ⟨a, ⟨c, hc, rfl⟩, hag⟩
    exact ⟨c, hc, hag⟩
  · rintro ⟨c, hc, hcg⟩
    exact Subgroup.mem_map.mpr ⟨LinearEquiv.smulOfUnit c,
      Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, hcg⟩

theorem odd_linear_three_involution_centralizer_core (hF : Odd (Nat.card F))
    (hq : 3 ≤ Nat.card F) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) (t : SL3 F ⧸ D) (ht : orderOf t = 2) :
    ∃ (z : SL3 F) (hz : orderOf z = 2) (hzt : QuotientGroup.mk' D z = t),
      (∀ w : SL3 F, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
      Module.finrank F (minusSpace (matrixAction F z).toLinearMap) = 2 ∧
      Module.finrank F (plusSpace (matrixAction F z).toLinearMap) = 1 ∧
      Function.Bijective (matrixCentralizerEquiv F hF z hz) ∧
      (∀ a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
        minusSpace (matrixAction F z).toLinearMap,
        (∀ x : minusSpace (matrixAction F z).toLinearMap,
          matrixAction F (matrixCentralizerEquiv F hF z hz a) x = a x) ∧
        (∀ y : plusSpace (matrixAction F z).toLinearMap,
          matrixAction F (matrixCentralizerEquiv F hF z hz a) y =
            ((a.det⁻¹ : Fˣ) : F) • (y : Fin 3 → F))) ∧
      (∀ a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
        minusSpace (matrixAction F z).toLinearMap,
        (targetQuotientCentralizer F hF D z hz t hzt a : SL3 F ⧸ D) =
          QuotientGroup.mk' D (matrixCentralizerEquiv F hF z hz a)) ∧
      Function.Surjective (targetQuotientCentralizer F hF D z hz t hzt) ∧
      (∀ a : minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
        minusSpace (matrixAction F z).toLinearMap,
        a ∈ (targetQuotientCentralizer F hF D z hz t hzt).ker ↔
          ∃ (c : Fˣ) (hc : c ^ 3 = 1), matrixScalar F c hc ∈ D ∧
            a = LinearEquiv.smulOfUnit c) ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) =
        ((CyclicOddScalarQuotient.oddElements Fˣ).map
          (OddLinearTwoAutomorphisms.scalarHom F
            (minusSpace (matrixAction F z).toLinearMap))).map
              (targetQuotientCentralizer F hF D z hz t hzt) ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D)))) =
        ordCompl[2] (Nat.card F - 1) / Nat.card D ∧
      Nat.card (Subgroup.centralizer ({t} : Set (SL3 F ⧸ D))) =
        (Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1)) / Nat.card D := by
  obtain ⟨z, ⟨hz, hzt⟩, huniq⟩ := unique_involution_lift F D hD t ht
  obtain ⟨hm, hp⟩ := matrixAction_finrank F hF z hz
  obtain ⟨hcore, hcenter, hcyclic, horder⟩ :=
    targetQuotientCentralizer_core_structure F hF hq D hD z hz t hzt
  refine ⟨z, hz, hzt, ?_, hm, hp, (matrixCentralizerEquiv F hF z hz).bijective, ?_,
    targetQuotientCentralizer_coe F hF D z hz t hzt,
    targetQuotientCentralizer_surjective F hF D hD z hz t hzt, ?_,
    hcore, hcenter, hcyclic, horder, targetQuotientCentralizer_card F hF D hD z hz t hzt⟩
  · intro w hw hwt
    exact huniq w ⟨hw, hwt⟩
  · intro a
    exact ⟨matrixCentralizerEquiv_minus F hF z hz a,
      matrixCentralizerEquiv_plus F hF z hz a⟩
  · intro a
    rw [targetQuotientCentralizer_ker]
    exact matrixQuotientCentralizer_mem_ker_iff hF hD hz


end FullCentralizerCore
end CFSG.Wreathed.OddLinearThreeCentralizerCore
