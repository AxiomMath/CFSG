module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquare

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary QuaternionMatrices UnitaryHigher Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Proj

variable (B : LinearMap.BilinForm K V)

theorem neg_one_mem_sesqUnitaryGroup :
    (-1 : LinearMap.GeneralLinearGroup K V) ∈ sesqUnitaryGroup B := fun v w => by
  simp

@[expose] def symplecticSignScalars : Subgroup (sesqUnitaryGroup B) where
  carrier := {g | (g : LinearMap.GeneralLinearGroup K V) = 1 ∨
    (g : LinearMap.GeneralLinearGroup K V) = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;>
      change (a : LinearMap.GeneralLinearGroup K V) * b = 1 ∨
        (a : LinearMap.GeneralLinearGroup K V) * b = -1 <;> rw [ha, hb] <;> simp
  inv_mem' := by
    rintro a (ha | ha) <;>
      change (a : LinearMap.GeneralLinearGroup K V)⁻¹ = 1 ∨
        (a : LinearMap.GeneralLinearGroup K V)⁻¹ = -1 <;> rw [ha] <;> simp

theorem mem_symplecticSignScalars {g : sesqUnitaryGroup B} :
    g ∈ symplecticSignScalars B ↔ (g : LinearMap.GeneralLinearGroup K V) = 1 ∨
      (g : LinearMap.GeneralLinearGroup K V) = -1 :=
  Iff.rfl

instance symplecticSignScalars_normal : (symplecticSignScalars B).Normal :=
  ⟨fun n hn g => by
    rcases hn with h | h
    · left
      simp [h]
    · right
      simp [h]⟩

abbrev SymplecticProj : Type _ :=
  sesqUnitaryGroup B ⧸ symplecticSignScalars B

@[expose] def symplecticProj : sesqUnitaryGroup B →* SymplecticProj B :=
  QuotientGroup.mk' (symplecticSignScalars B)

end Proj

section Model

variable {B : LinearMap.BilinForm K V} {A : LinearMap.GeneralLinearGroup K V}

theorem exists_four_of_pair {x y : LinearMap.GeneralLinearGroup K V}
    (hx : x ∈ similitudeCentralizer B A) (hy : y ∈ similitudeCentralizer B A)
    (hxx : x * x = 1 ∨ x * x = -1) (hyy : y * y = 1 ∨ y * y = -1)
    (hxy : x * y = y * x ∨ x * y = -(y * x)) (hx1 : x ≠ 1) (hxn : x ≠ -1) (hy1 : y ≠ 1)
    (hyn : y ≠ -1) (hxy1 : x * y ≠ 1) (hxyn : x * y ≠ -1) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let x' : sesqUnitaryGroup B := ⟨x, hx.1⟩
  let y' : sesqUnitaryGroup B := ⟨y, hy.1⟩
  have hπ : ∀ g : sesqUnitaryGroup B, symplecticProj B g = 1 ↔ g ∈ symplecticSignScalars B :=
    fun g => QuotientGroup.eq_one_iff g
  have hpx : symplecticProj B x' * symplecticProj B x' = 1 := by
    rw [← map_mul, hπ]
    exact hxx
  have hpy : symplecticProj B y' * symplecticProj B y' = 1 := by
    rw [← map_mul, hπ]
    exact hyy
  have hpxy : symplecticProj B x' * symplecticProj B y' =
      symplecticProj B y' * symplecticProj B x' := by
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.2 ?_
    rcases hxy with h | h
    · have : x' * y' = y' * x' := Subtype.ext h
      rw [this, inv_mul_cancel]
      exact (symplecticSignScalars B).one_mem
    · right
      change (x * y)⁻¹ * (y * x) = -1
      rw [h, inv_neg, neg_mul, inv_mul_cancel]
  have hpx1 : symplecticProj B x' ≠ 1 := fun h => by
    rcases (hπ x').1 h with h | h
    · exact hx1 h
    · exact hxn h
  have hpy1 : symplecticProj B y' ≠ 1 := fun h => by
    rcases (hπ y').1 h with h | h
    · exact hy1 h
    · exact hyn h
  have hpne : symplecticProj B x' ≠ symplecticProj B y' := fun h => by
    have h1 : symplecticProj B (x' * y') = 1 := by rw [map_mul, ← h, hpx]
    rcases (hπ _).1 h1 with h | h
    · exact hxy1 h
    · exact hxyn h
  obtain ⟨W, -, hWle, hW, hWcard⟩ := FourGroup.exists_kleinFour hpx hpy hpxy hpx1 hpy1 hpne
  exact ⟨W, hWle _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx.2))
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy.2)), hW, hWcard⟩

theorem neg_one_mem_similitudeCentralizer :
    (-1 : LinearMap.GeneralLinearGroup K V) ∈ similitudeCentralizer B A :=
  ⟨neg_one_mem_sesqUnitaryGroup B, Subgroup.mem_centralizer_singleton_iff.2 (by simp)⟩

theorem exists_four_of_mulEquiv {G : Type*} [Group G] (e : similitudeCentralizer B A ≃* G)
    {nn : G} (hnn : e ⟨-1, neg_one_mem_similitudeCentralizer⟩ = nn) {gx gy : G}
    (hxx : gx * gx = 1 ∨ gx * gx = nn) (hyy : gy * gy = 1 ∨ gy * gy = nn)
    (hxy : gx * gy = gy * gx ∨ gx * gy = nn * (gy * gx)) (hx1 : gx ≠ 1) (hxn : gx ≠ nn)
    (hy1 : gy ≠ 1) (hyn : gy ≠ nn) (hxy1 : gx * gy ≠ 1) (hxyn : gx * gy ≠ nn) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  set m1 : similitudeCentralizer B A := ⟨-1, neg_one_mem_similitudeCentralizer⟩
  have hsymm : e.symm nn = m1 := by rw [← hnn, MulEquiv.symm_apply_apply]
  have hcoe1 : ∀ g : G, e.symm g = 1 → g = 1 := fun g h => by
    rw [← e.apply_symm_apply g, h, map_one]
  have hcoen : ∀ g : G, e.symm g = m1 → g = nn := fun g h => by
    rw [← e.apply_symm_apply g, h, hnn]
  have hval : ∀ g : G, ((e.symm g : similitudeCentralizer B A) :
      LinearMap.GeneralLinearGroup K V) = 1 → g = 1 := fun g h =>
    hcoe1 g (Subtype.ext h)
  have hvaln : ∀ g : G, ((e.symm g : similitudeCentralizer B A) :
      LinearMap.GeneralLinearGroup K V) = -1 → g = nn := fun g h =>
    hcoen g (Subtype.ext h)
  have hsq : ∀ g : G, (g * g = 1 ∨ g * g = nn) →
      ((e.symm g : similitudeCentralizer B A) : LinearMap.GeneralLinearGroup K V) *
          ((e.symm g : similitudeCentralizer B A) : LinearMap.GeneralLinearGroup K V) = 1 ∨
        ((e.symm g : similitudeCentralizer B A) : LinearMap.GeneralLinearGroup K V) *
          ((e.symm g : similitudeCentralizer B A) : LinearMap.GeneralLinearGroup K V) = -1 := by
    rintro g (h | h)
    · left
      rw [← Subgroup.coe_mul, ← map_mul, h, map_one]
      rfl
    · right
      rw [← Subgroup.coe_mul, ← map_mul, h, hsymm]
  refine exists_four_of_pair (e.symm gx).2 (e.symm gy).2 (hsq gx hxx) (hsq gy hyy) ?_
    (fun h => hx1 (hval gx h)) (fun h => hxn (hvaln gx h)) (fun h => hy1 (hval gy h))
    (fun h => hyn (hvaln gy h)) (fun h => hxy1 (hval _ (by rw [map_mul]; exact h)))
    (fun h => hxyn (hvaln _ (by rw [map_mul]; exact h)))
  rcases hxy with h | h
  · left
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  · right
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h, map_mul, hsymm,
      Subgroup.coe_mul, neg_one_mul]

theorem ne_one_of_forall_ne_smul {W : Type*} [AddCommGroup W] [Module K W]
    {u : LinearMap.GeneralLinearGroup K W} (h : ∀ a : K, (u : Module.End K W) ≠ a • 1) :
    u ≠ 1 := fun hu => h 1 (by rw [hu, one_smul]; rfl)

theorem ne_neg_one_of_forall_ne_smul {W : Type*} [AddCommGroup W] [Module K W]
    {u : LinearMap.GeneralLinearGroup K W} (h : ∀ a : K, (u : Module.End K W) ≠ a • 1) :
    u ≠ -1 := fun hu => h (-1) (by rw [hu, neg_one_smul]; rfl)

theorem neg_one_of_restrict {W : Submodule K V} {u : LinearMap.GeneralLinearGroup K W}
    (h : W.subtype ∘ₗ (u : Module.End K W) =
      ((-1 : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ W.subtype) : u = -1 := by
  refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
  have := LinearMap.congr_fun h v
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]
  simp

end Model

section Cases

variable {B : LinearMap.BilinForm K V} {A : LinearMap.GeneralLinearGroup K V}

theorem exists_four_split [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V]
    {Vp Vm : Submodule K V} (hVp : Vp ≠ ⊥) (hVm : Vm ≠ ⊥)
    (hAp : (B.domRestrict₁₂ Vp Vp).IsAlt) (hAm : (B.domRestrict₁₂ Vm Vm).IsAlt)
    (hNp : (B.domRestrict₁₂ Vp Vp).Nondegenerate) (hNm : (B.domRestrict₁₂ Vm Vm).Nondegenerate)
    (e : similitudeCentralizer B A ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) × sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm))
    (he : ∀ g : similitudeCentralizer B A,
      Vp.subtype ∘ₗ (((e g).1 : LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vp.subtype ∧
        Vm.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup K Vm) : Module.End K Vm) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vm.subtype) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have : Nontrivial Vp := Submodule.nontrivial_iff_ne_bot.2 hVp
  have : Nontrivial Vm := Submodule.nontrivial_iff_ne_bot.2 hVm
  obtain ⟨ip, jp, hip, hjp, hipp, hjpp, hijp, hipn, hjpn, hijpn⟩ := exists_quat_sp hK _ hAp hNp
  obtain ⟨im, jm, him, hjm, himm, hjmm, hijm, himn, hjmn, hijmn⟩ := exists_quat_sp hK _ hAm hNm
  let np : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) := ⟨-1, neg_one_mem_sesqUnitaryGroup _⟩
  let nm : sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) := ⟨-1, neg_one_mem_sesqUnitaryGroup _⟩
  have hnn : e ⟨-1, neg_one_mem_similitudeCentralizer⟩ = (np, nm) :=
    Prod.ext (Subtype.ext (neg_one_of_restrict (he _).1))
      (Subtype.ext (neg_one_of_restrict (he _).2))
  let gx : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) × sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) :=
    (⟨ip, hip⟩, ⟨im, him⟩)
  let gy : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) × sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) :=
    (⟨jp, hjp⟩, ⟨jm, hjm⟩)
  have hfst : ∀ {g g' : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) ×
      sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm)}, g = g' →
      ((g.1 : sesqUnitaryGroup _) : LinearMap.GeneralLinearGroup K Vp) = g'.1 :=
    fun h => by rw [h]
  refine exists_four_of_mulEquiv e hnn (gx := gx) (gy := gy)
    (Or.inr (Prod.ext (Subtype.ext hipp) (Subtype.ext himm)))
    (Or.inr (Prod.ext (Subtype.ext hjpp) (Subtype.ext hjmm)))
    (Or.inr (Prod.ext (Subtype.ext (by
        change ip * jp = (-1) * (jp * ip)
        rw [hijp]
        exact (neg_one_mul (jp * ip)).symm))
      (Subtype.ext (by
        change im * jm = (-1) * (jm * im)
        rw [hijm]
        exact (neg_one_mul (jm * im)).symm))))
    (fun h => ne_one_of_forall_ne_smul hipn (hfst h))
    (fun h => ne_neg_one_of_forall_ne_smul hipn (hfst h))
    (fun h => ne_one_of_forall_ne_smul hjpn (hfst h))
    (fun h => ne_neg_one_of_forall_ne_smul hjpn (hfst h))
    (fun h => ne_one_of_forall_ne_smul hijpn (hfst h))
    (fun h => ne_neg_one_of_forall_ne_smul hijpn (hfst h))

theorem exists_four_paired (h2 : (2 : K) ≠ 0) [FiniteDimensional K V] {Vp : Submodule K V}
    {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K Vp = r)
    (e : similitudeCentralizer B A ≃* LinearMap.GeneralLinearGroup K Vp)
    (he : ∀ g : similitudeCentralizer B A,
      Vp.subtype ∘ₗ ((e g : LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vp.subtype) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have hnn : e ⟨-1, neg_one_mem_similitudeCentralizer⟩ = -1 := neg_one_of_restrict (he _)
  let c := Module.finBasisOfFinrankEq K Vp hdim
  obtain ⟨X, Y, hXX, hYY, hXY, hXn, hYn, hXYn, -, -, -, -⟩ := exists_sign_swap h2 hr
  have hsq : ∀ (M : Matrix (Fin r) (Fin r) K) (hM : M * M = 1),
      basisGL c (involGL M hM) * basisGL c (involGL M hM) = 1 := fun M hM => by
    rw [← map_mul, show involGL M hM * involGL M hM = 1 from Units.ext hM, map_one]
  have hmulc : ((basisGL c (involGL X hXX) * basisGL c (involGL Y hYY) :
      LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) = Matrix.toLin c c (X * Y) := by
    rw [← map_mul, coe_basisGL]
    rfl
  have hXYns : ∀ a : K, ((basisGL c (involGL X hXX) * basisGL c (involGL Y hYY) :
      LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) ≠ a • 1 := fun a h =>
    hXYn a (toLin_eq_smul_id c (by rw [← hmulc, h]; rfl))
  refine exists_four_of_mulEquiv e hnn (Or.inl (hsq X hXX)) (Or.inl (hsq Y hYY)) ?_
    (ne_one_of_forall_ne_smul (coe_basisGL_ne_smul c hXn))
    (ne_neg_one_of_forall_ne_smul (coe_basisGL_ne_smul c hXn))
    (ne_one_of_forall_ne_smul (coe_basisGL_ne_smul c hYn))
    (ne_neg_one_of_forall_ne_smul (coe_basisGL_ne_smul c hYn))
    (ne_one_of_forall_ne_smul hXYns) (ne_neg_one_of_forall_ne_smul hXYns)
  rcases hXY with h | h
  · left
    rw [← map_mul, ← map_mul, show involGL X hXX * involGL Y hYY = involGL Y hYY * involGL X hXX
      from Units.ext h]
  · right
    rw [← map_mul, ← map_mul, show involGL X hXX * involGL Y hYY =
      -(involGL Y hYY * involGL X hXX) from Units.ext (by rw [Units.val_neg]; exact h),
      basisGL_neg]
    exact (neg_one_mul (basisGL c (involGL Y hYY * involGL X hXX))).symm

section Field

variable {d : K}

theorem restrictGL_mem_centralizer [Nontrivial V]
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d)
    (u : LinearMap.GeneralLinearGroup (scalarSquareField (A : Module.End K V)) V) :
    let _ : Field (scalarSquareField (A : Module.End K V)) :=
      (isField_scalarSquareField hAA hd).toField
    restrictGL (K := K) u ∈ Subgroup.centralizer {A} := by
  let _ : Field (scalarSquareField (A : Module.End K V)) :=
    (isField_scalarSquareField hAA hd).toField
  have hmem : (A : Module.End K V) ∈ scalarSquareField (A : Module.End K V) :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext (LinearMap.ext fun v => ?_))
  change (u : Module.End (scalarSquareField (A : Module.End K V)) V) ((A : Module.End K V) v) =
    (A : Module.End K V) ((u : Module.End (scalarSquareField (A : Module.End K V)) V) v)
  have e1 : (A : Module.End K V) v = (⟨_, hmem⟩ : scalarSquareField (A : Module.End K V)) • v := rfl
  have e2 : (A : Module.End K V) ((u : Module.End (scalarSquareField (A : Module.End K V)) V) v) =
      (⟨_, hmem⟩ : scalarSquareField (A : Module.End K V)) •
        (u : Module.End (scalarSquareField (A : Module.End K V)) V) v := rfl
  rw [e1, e2, map_smul]

theorem finite_scalarSquareField [Finite K] [FiniteDimensional K V] :
    Finite (scalarSquareField (A : Module.End K V)) := by
  have : Finite (Module.End K V) := Module.finite_of_finite K
  exact Finite.of_injective _ Subtype.val_injective

theorem ringChar_scalarSquareField_ne_two [Nontrivial V]
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d)
    (hK : ringChar K ≠ 2) :
    let _ : Field (scalarSquareField (A : Module.End K V)) :=
      (isField_scalarSquareField hAA hd).toField
    ringChar (scalarSquareField (A : Module.End K V)) ≠ 2 := by
  intro _ h
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc := ringChar.Nat.cast_ringChar (R := scalarSquareField (A : Module.End K V))
  rw [h] at hc
  apply h2
  apply (algebraMap K (scalarSquareField (A : Module.End K V))).injective
  rw [map_zero, map_ofNat]
  exact_mod_cast hc

theorem exists_four_field_alt [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d)
    (hK : ringChar K ≠ 2)
    (BE : LinearMap.BilinForm (scalarSquareField (A : Module.End K V)) V) (hBEa : BE.IsAlt)
    (hBEn : BE.Nondegenerate)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, BE ((g : Module.End K V) v) ((g : Module.End K V) w) = BE v w) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let _ : Field (scalarSquareField (A : Module.End K V)) :=
    (isField_scalarSquareField hAA hd).toField
  have : FiniteDimensional (scalarSquareField (A : Module.End K V)) V :=
    Module.Finite.of_restrictScalars_finite K _ V
  have := finite_scalarSquareField (A := A)
  obtain ⟨i, j, hi, hj, hii, hjj, hij, hin, hjn, hijn⟩ :=
    exists_quat_sp (ringChar_scalarSquareField_ne_two hAA hd hK) BE hBEa hBEn
  have hmem : ∀ u ∈ sesqUnitaryGroup BE, restrictGL (K := K) u ∈ similitudeCentralizer B A :=
    fun u hu => (hiff _).2 ⟨restrictGL_mem_centralizer hAA hd u, fun v w => hu v w⟩
  have hsq : ∀ u : LinearMap.GeneralLinearGroup (scalarSquareField (A : Module.End K V)) V,
      u * u = -1 → restrictGL (K := K) u * restrictGL u = -1 := fun u hu => by
    rw [← map_mul, hu, restrictGL_neg, map_one]
  have hxyns : ∀ a : K, ((restrictGL (K := K) i * restrictGL j :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ a • 1 := by
    rw [← map_mul]
    exact coe_restrictGL_ne_smul hijn
  refine exists_four_of_pair (hmem i hi) (hmem j hj) (Or.inr (hsq i hii)) (Or.inr (hsq j hjj))
    (Or.inr (by rw [← map_mul, hij, restrictGL_neg, map_mul]))
    (ne_one_of_forall_ne_smul (coe_restrictGL_ne_smul hin))
    (ne_neg_one_of_forall_ne_smul (coe_restrictGL_ne_smul hin))
    (ne_one_of_forall_ne_smul (coe_restrictGL_ne_smul hjn))
    (ne_neg_one_of_forall_ne_smul (coe_restrictGL_ne_smul hjn))
    (ne_one_of_forall_ne_smul hxyns) (ne_neg_one_of_forall_ne_smul hxyns)

theorem exists_four_field_herm [FiniteDimensional K V] [Nontrivial V]
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d)
    (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf1 : 1 ≤ f)
    (hcardE : Nat.card (scalarSquareField (A : Module.End K V)) = (ℓ ^ f) ^ 2)
    (hrank : 2 ≤ finrank (scalarSquareField (A : Module.End K V)) V)
    (bar : scalarSquareField (A : Module.End K V) →+* scalarSquareField (A : Module.End K V))
    (hbar : ∀ x, bar x = x ^ (ℓ ^ f))
    (hf : V →ₛₗ[bar] V →ₗ[scalarSquareField (A : Module.End K V)]
      scalarSquareField (A : Module.End K V))
    (hsymm : hf.IsSymm) (hsep : hf.SeparatingLeft)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, hf ((g : Module.End K V) v) ((g : Module.End K V) w) = hf v w) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let _ : Field (scalarSquareField (A : Module.End K V)) :=
    (isField_scalarSquareField hAA hd).toField
  have : FiniteDimensional (scalarSquareField (A : Module.End K V)) V :=
    Module.Finite.of_restrictScalars_finite K _ V
  have hUF : UnitaryFieldData ℓ f (scalarSquareField (A : Module.End K V)) :=
    ⟨hℓ, hf1, by rw [hcardE, ← pow_mul, mul_comm]⟩
  have hbh : bar = hUF.bar := RingHom.ext fun x => by rw [hbar, hUF.bar_apply]
  subst hbh
  obtain ⟨ob, hob⟩ := hUF.exists_orthonormal_basis hsymm hsep
  have h2E : (2 : scalarSquareField (A : Module.End K V)) ≠ 0 :=
    Ring.two_ne_zero (ringChar_scalarSquareField_ne_two hAA hd hK)
  obtain ⟨X, Y, hXX, hYY, hXY, hXn, hYn, hXYn, hXt, hYt, hXσ, hYσ⟩ := exists_sign_swap h2E hrank
  have hG : ∀ i j,
      hf (ob i) (ob j) = (1 : Matrix _ _ (scalarSquareField (A : Module.End K V))) i j :=
    fun i j => by rw [hob, Matrix.one_apply]
  have hpres : ∀ (M : Matrix _ _ (scalarSquareField (A : Module.End K V))) (hM : M * M = 1),
      (∀ i j, hUF.bar (M i j) = M i j) → Mᵀ * M = 1 →
        restrictGL (K := K) (basisGL ob (involGL M hM)) ∈ similitudeCentralizer B A :=
    fun M hM hMσ hMt => (hiff _).2 ⟨restrictGL_mem_centralizer hAA hd _, fun v w =>
      toLin_preserves hf ob 1 hG hMσ (by rw [Matrix.mul_one, hMt]) v w⟩
  have hsq : ∀ (M : Matrix _ _ (scalarSquareField (A : Module.End K V))) (hM : M * M = 1),
      restrictGL (K := K) (basisGL ob (involGL M hM)) *
        restrictGL (basisGL ob (involGL M hM)) = 1 := fun M hM => by
    rw [← map_mul, ← map_mul, show involGL M hM * involGL M hM = 1 from Units.ext hM, map_one,
      map_one]
  have hns : ∀ (M : Matrix _ _ (scalarSquareField (A : Module.End K V))) (hM : M * M = 1),
      (∀ a, M ≠ a • 1) → ∀ a : K, ((restrictGL (K := K) (basisGL ob (involGL M hM)) :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ a • 1 := fun M hM hMn =>
    coe_restrictGL_ne_smul (coe_basisGL_ne_smul ob hMn)
  have hxyns : ∀ a : K, ((restrictGL (K := K) (basisGL ob (involGL X hXX)) *
      restrictGL (basisGL ob (involGL Y hYY)) : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) ≠ a • 1 := by
    rw [← map_mul, ← map_mul]
    refine coe_restrictGL_ne_smul fun a h => hXYn a (toLin_eq_smul_id ob ?_)
    have e : ((basisGL ob (involGL X hXX * involGL Y hYY) : LinearMap.GeneralLinearGroup
        (scalarSquareField (A : Module.End K V)) V) :
          Module.End (scalarSquareField (A : Module.End K V)) V) = Matrix.toLin ob ob (X * Y) :=
      rfl
    rw [← e, h]
    rfl
  refine exists_four_of_pair (hpres X hXX (hXσ _) hXt) (hpres Y hYY (hYσ _) hYt)
    (Or.inl (hsq X hXX)) (Or.inl (hsq Y hYY)) ?_
    (ne_one_of_forall_ne_smul (hns X hXX hXn)) (ne_neg_one_of_forall_ne_smul (hns X hXX hXn))
    (ne_one_of_forall_ne_smul (hns Y hYY hYn)) (ne_neg_one_of_forall_ne_smul (hns Y hYY hYn))
    (ne_one_of_forall_ne_smul hxyns) (ne_neg_one_of_forall_ne_smul hxyns)
  rcases hXY with h | h
  · left
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
      show involGL X hXX * involGL Y hYY = involGL Y hYY * involGL X hXX from Units.ext h]
  · right
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, show involGL X hXX * involGL Y hYY =
      -(involGL Y hYY * involGL X hXX) from Units.ext (by rw [Units.val_neg]; exact h),
      basisGL_neg, restrictGL_neg]

end Field

end Cases

theorem odd_symplectic_scalar_square_centralizer_projective_four_group [Finite K]
    (hK : ringChar K ≠ 2) [FiniteDimensional K V] {r : ℕ} (hr : 2 ≤ r)
    (hdim : finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    ∃ W : Subgroup (SymplecticProj B),
      W ≤ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hε, hsqcase, hnscase⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hK
    n.pos hK' (by omega : 1 ≤ r) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, h1, h2'⟩ := hsqcase l hl
    rcases hε with hε | hε
    · obtain ⟨-, hAp, hAm, hNp, hNm, e, he⟩ := h1 hε
      exact exists_four_split hK hP hM hAp hAm hNp hNm e he
    · obtain ⟨-, -, hrp, -, -, -, e, he, -⟩ := h2' hε
      exact exists_four_paired h2 hr hrp e he
  · push Not at hsq
    obtain ⟨-, -, hcardE, hrankE, bar, -, hbar, -, hc1, hc2⟩ := hnscase hsq
    rcases hε with hε | hε
    · obtain ⟨BE, -, hBEa, hBEn, -, hiff⟩ := hc1 hε
      exact exists_four_field_alt hAA hsq hK BE hBEa hBEn hiff
    · obtain ⟨hf, -, hsymm, hsep, hiff⟩ := hc2 hε
      exact exists_four_field_herm hAA hsq hK hℓ n.pos hcardE (by rw [hrankE]; exact hr) bar
        hbar hf hsymm hsep hiff

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
