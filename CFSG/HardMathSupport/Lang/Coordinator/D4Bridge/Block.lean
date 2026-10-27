module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Data
public import CFSG.LieType.Steinberg.Minuscule.Group
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Twisted
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable (F : Type) [Field F]

abbrev M := Fin d4tData.d →₀ F

abbrev V := Coord → F

@[expose] def nIdx (x : Coord) : Fin d4tData.d := ⟨(natIdx x : ℕ), (natIdx x).2⟩

theorem nIdx_injective : Function.Injective nIdx := fun _ _ h =>
  natIdx_injective (Fin.ext (congrArg Fin.val h))

@[expose] def phi : V F →ₗ[F] M F where
  toFun v := ∑ x : Coord, ((natSgn x : F) * v x) • Finsupp.single (nIdx x) 1
  map_add' v v' := by
    ext a
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  map_smul' c v := by
    ext a
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

@[expose] def psi : M F →ₗ[F] V F where
  toFun w x := (natSgn x : F) * w (nIdx x)
  map_add' w w' := funext fun x => by
    simp only [Finsupp.coe_add, Pi.add_apply, mul_add]
  map_smul' c w := funext fun x => by
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

variable {F}

theorem natSgn_cast_mul_self (x : Coord) : (natSgn x : F) * (natSgn x : F) = 1 := by
  rw [← Int.cast_mul, natSgn_mul_self, Int.cast_one]

theorem phi_single (x : Coord) (c : F) :
    phi F (Pi.single x c) = ((natSgn x : F) * c) • Finsupp.single (nIdx x) 1 := by
  rw [phi, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_eq_single x]
  · rw [Pi.single_eq_same]
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem phi_apply (v : V F) (a : Fin d4tData.d) :
    phi F v a = ∑ x : Coord, if nIdx x = a then (natSgn x : F) * v x else 0 := by
  rw [phi, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem psi_apply (w : M F) (x : Coord) :
    psi F w x = (natSgn x : F) * w (nIdx x) := rfl

theorem psi_phi (v : V F) : psi F (phi F v) = v := by
  funext x
  rw [psi_apply, phi_apply, Finset.sum_eq_single x]
  · rw [ite_eq_left rfl, ← mul_assoc, natSgn_cast_mul_self, one_mul]
  · intro y _ hyx
    rw [ite_eq_right fun h => hyx (nIdx_injective h)]
  · intro h
    exact absurd (Finset.mem_univ x) h

@[expose] def InBlock (w : M F) : Prop :=
  ∀ a : Fin d4tData.d, (∀ x : Coord, nIdx x ≠ a) → w a = 0

theorem inBlock_phi (v : V F) : InBlock (phi F v) := fun a ha => by
  rw [phi_apply]
  exact Finset.sum_eq_zero fun x _ => ite_eq_right (ha x)

theorem phi_psi {w : M F} (hw : InBlock w) : phi F (psi F w) = w := by
  ext a
  rw [phi_apply]
  by_cases ha : ∃ x : Coord, nIdx x = a
  · obtain ⟨x, rfl⟩ := ha
    rw [Finset.sum_eq_single x]
    · rw [ite_eq_left rfl, psi_apply, ← mul_assoc, natSgn_cast_mul_self, one_mul]
    · intro y _ hyx
      rw [ite_eq_right fun h => hyx (nIdx_injective h)]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · push Not at ha
    rw [hw a ha]
    exact Finset.sum_eq_zero fun x _ => ite_eq_right (ha x)

theorem InBlock.add {w w' : M F} (hw : InBlock w) (hw' : InBlock w') : InBlock (w + w') :=
  fun a ha => by rw [Finsupp.add_apply, hw a ha, hw' a ha, add_zero]

theorem InBlock.sub {w w' : M F} (hw : InBlock w) (hw' : InBlock w') : InBlock (w - w') :=
  fun a ha => by rw [Finsupp.sub_apply, hw a ha, hw' a ha, sub_zero]

theorem InBlock.smul {w : M F} (hw : InBlock w) (c : F) : InBlock (c • w) :=
  fun a ha => by rw [Finsupp.smul_apply, hw a ha, smul_zero]

theorem inBlock_single (x : Coord) (c : F) : InBlock (Finsupp.single (nIdx x) c) :=
  fun a ha => by rw [Finsupp.single_apply, ite_eq_right (ha x)]

@[expose] def nMap (u w : Coord) : V F →ₗ[F] V F where
  toFun v := v (dualC u) • Pi.single w 1 - v (dualC w) • Pi.single u 1
  map_add' v v' := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]

theorem nMap_apply (u w : Coord) (v : V F) :
    nMap u w v = v (dualC u) • Pi.single w 1 - v (dualC w) • Pi.single u 1 := rfl

variable (F) in
@[expose] def blockStab : Subgroup (Module.End F (M F))ˣ where
  carrier := {g | ∀ w : M F, InBlock w →
    InBlock ((g : Module.End F (M F)) w) ∧ InBlock (((g⁻¹ : (Module.End F (M F))ˣ) :
      Module.End F (M F)) w)}
  mul_mem' {g h} hg hh w hw := ⟨(hg _ (hh w hw).1).1, by
    rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
    exact (hh _ (hg w hw).2).2⟩
  one_mem' w hw := ⟨hw, hw⟩
  inv_mem' {g} hg w hw := ⟨(hg w hw).2, by rw [inv_inv]; exact (hg w hw).1⟩

theorem blockStab_psi_phi {g : (Module.End F (M F))ˣ} (hg : g ∈ blockStab F) (v : V F) :
    phi F (psi F ((g : Module.End F (M F)) (phi F v))) = (g : Module.End F (M F)) (phi F v) :=
  phi_psi ((hg _ (inBlock_phi v)).1)

variable (F) in
@[expose] def blockHom : blockStab F →* (V F ≃ₗ[F] V F) where
  toFun g := LinearEquiv.ofLinearMap
    ((psi F).comp (((g : (Module.End F (M F))ˣ) : Module.End F (M F)).comp (phi F)))
    ((psi F).comp ((((g : (Module.End F (M F))ˣ)⁻¹ : (Module.End F (M F))ˣ) :
      Module.End F (M F)).comp (phi F)))
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [blockStab_psi_phi (inv_mem g.2) v, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_apply, psi_phi])
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [blockStab_psi_phi g.2 v, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Module.End.one_apply, psi_phi])
  map_one' := LinearEquiv.ext fun v => by
    change psi F ((1 : Module.End F (M F)) (phi F v)) = v
    rw [Module.End.one_apply, psi_phi]
  map_mul' g h := LinearEquiv.ext fun v => by
    simp only [LinearEquiv.coe_ofLinearMap, LinearMap.comp_apply, Subgroup.coe_mul, Units.val_mul,
      Module.End.mul_apply, LinearEquiv.mul_apply]
    rw [blockStab_psi_phi h.2 v]

theorem blockHom_apply (g : blockStab F) (v : V F) :
    blockHom F g v = psi F (((g : (Module.End F (M F))ˣ) : Module.End F (M F)) (phi F v)) :=
  rfl

theorem cIdx_dualC (x : Coord) : cIdx (dualC x) = cIdx x := by
  rcases x with i | i <;> rfl

theorem quadPlus_single (x : Coord) : quadPlus 4 F (Pi.single x 1) = 0 := by
  rcases x with i | i
  · exact quadPlus_plusVec 4 F i true
  · exact quadPlus_plusVec 4 F i false

theorem polar_single (v : V F) (x : Coord) :
    polar (quadPlus 4 F) v (Pi.single x 1) = v (dualC x) := by
  rcases x with i | i
  · rw [polar_quadPlus_single_inl]
    rfl
  · rw [polar_quadPlus_single_inr]
    rfl

theorem polar_single_single {u w : Coord} (h : cIdx u ≠ cIdx w) :
    polar (quadPlus 4 F) (Pi.single u 1) (Pi.single w 1) = 0 := by
  rw [polar_single, Pi.single_apply, ite_eq_right]
  intro hw
  exact h (by rw [← hw, cIdx_dualC])

theorem eq_zero_of_polar_plusVec {v : V F}
    (h : ∀ (k : Fin 4) (r : Bool), polar (quadPlus 4 F) v (plusVec 4 F k r) = 0) : v = 0 := by
  funext x
  rcases x with i | i
  · have := h i false
    rwa [plusVec_false, polar_quadPlus_single_inr] at this
  · have := h i true
    rwa [plusVec_true, polar_quadPlus_single_inl] at this

omit [Field F] in
theorem eichler_swap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} {u w : W} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hw, QuadraticMap.map_neg, hu, polar_neg_right]
  module

theorem eichler_single_swap {u w : Coord} (h : cIdx u ≠ cIdx w) (c : F) :
    eichler (quadPlus 4 F) (Pi.single u 1) (c • Pi.single w 1) =
      eichler (quadPlus 4 F) (Pi.single w 1) ((-c) • Pi.single u 1) := by
  have h1 : quadPlus 4 F (c • Pi.single u 1) = 0 := by
    rw [QuadraticMap.map_smul, quadPlus_single, smul_zero]
  have h2 : polar (quadPlus 4 F) (c • Pi.single u 1) (Pi.single w 1) = 0 := by
    rw [polar_smul_left, polar_single_single h, smul_zero]
  calc eichler (quadPlus 4 F) (Pi.single u 1) (c • Pi.single w 1)
      = eichler (quadPlus 4 F) (c • Pi.single u 1) (Pi.single w 1) :=
        (eichler_smul_left c _ _).symm
    _ = eichler (quadPlus 4 F) (Pi.single w 1) (-(c • Pi.single u 1)) :=
        eichler_swap h1 (quadPlus_single w) h2
    _ = _ := by rw [neg_smul]

theorem E_single_natIdx (k : Fin 24) (x : Coord) :
    d4tData.E F k (Finsupp.single (nIdx x) 1) =
      if x = dualC (rU k) then
        ((natSgn x * rS k * natSgn (rW k) : ℤ) : F) •
          Finsupp.single (nIdx (rW k)) 1
      else if x = dualC (rW k) then
        ((-(natSgn x * rS k * natSgn (rU k)) : ℤ) : F) •
          Finsupp.single (nIdx (rU k)) 1
      else 0 := by
  have hc := rootCond_all k x
  rw [MinData.E, toEnd_single]
  change digVec F d4tData.d (opDig k (natIdx x)) = _
  unfold RootCond at hc
  split_ifs at hc ⊢ with h1 h2
  · obtain ⟨h2le, hidx, hsgn⟩ := hc
    have hlt : opDig k (natIdx x) / 2 - 1 < d4tData.d := by rw [← hidx]; exact (natIdx (rW k)).2
    have hfin : (⟨opDig k (natIdx x) / 2 - 1, hlt⟩ : Fin d4tData.d) = nIdx (rW k) :=
      Fin.ext hidx.symm
    rw [digVec_of_le h2le hlt, hfin]
    congr 1
    have : ((-1 : ℤ) ^ opDig k (natIdx x)) = natSgn x * rS k * natSgn (rW k) := by
      rw [← hsgn]
      have h := natSgn_mul_self x
      have h' := natSgn_mul_self (rW k)
      calc (-1 : ℤ) ^ opDig k (natIdx x)
          = (natSgn x * natSgn x) * (-1) ^ opDig k (natIdx x) *
              (natSgn (rW k) * natSgn (rW k)) := by rw [h, h', one_mul, mul_one]
        _ = natSgn x * (natSgn x * (-1) ^ opDig k (natIdx x) * natSgn (rW k)) *
              natSgn (rW k) := by ring
    rw [← this]
    push_cast
    rfl
  · obtain ⟨h2le, hidx, hsgn⟩ := hc
    have hlt : opDig k (natIdx x) / 2 - 1 < d4tData.d := by rw [← hidx]; exact (natIdx (rU k)).2
    have hfin : (⟨opDig k (natIdx x) / 2 - 1, hlt⟩ : Fin d4tData.d) = nIdx (rU k) :=
      Fin.ext hidx.symm
    rw [digVec_of_le h2le hlt, hfin]
    congr 1
    have : ((-1 : ℤ) ^ opDig k (natIdx x)) = -(natSgn x * rS k * natSgn (rU k)) := by
      have h := natSgn_mul_self x
      have h' := natSgn_mul_self (rU k)
      calc (-1 : ℤ) ^ opDig k (natIdx x)
          = (natSgn x * natSgn x) * (-1) ^ opDig k (natIdx x) *
              (natSgn (rU k) * natSgn (rU k)) := by rw [h, h', one_mul, mul_one]
        _ = natSgn x * (natSgn x * (-1) ^ opDig k (natIdx x) * natSgn (rU k)) *
              natSgn (rU k) := by ring
        _ = -(natSgn x * rS k * natSgn (rU k)) := by rw [hsgn]; ring
    rw [← this]
    push_cast
    rfl
  · rw [hc, digVec_zero]

theorem E_phi (k : Fin 24) (v : V F) :
    d4tData.E F k (phi F v) = phi F (((rS k : ℤ) : F) • nMap (rU k) (rW k) v) := by
  have hne : rU k ≠ rW k := fun h => (rootData_spec k).1 (congrArg cIdx h)
  have key : (d4tData.E F k).comp (phi F) =
      (phi F).comp ((((rS k : ℤ) : F)) • nMap (rU k) (rW k)) := by
    refine LinearMap.pi_ext fun x c => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, phi_single, map_smul, E_single_natIdx,
      LinearMap.smul_apply, nMap_apply]
    by_cases h1 : x = dualC (rU k)
    · have h2 : x ≠ dualC (rW k) := fun h => hne (by
        have := h1.symm.trans h
        cases hu : rU k <;> cases hw : rW k <;> simp_all [dualC])
      rw [ite_eq_left h1, Pi.single_apply, ite_eq_left h1.symm, Pi.single_apply,
        ite_eq_right (Ne.symm h2), zero_smul, sub_zero, map_smul, map_smul, phi_single]
      simp only [smul_smul]
      congr 1
      push_cast
      linear_combination (c * (rS k : F) * (natSgn (rW k) : F)) *
        natSgn_cast_mul_self (F := F) x
    · rw [ite_eq_right h1]
      by_cases h2 : x = dualC (rW k)
      · rw [ite_eq_left h2, Pi.single_apply, ite_eq_right (Ne.symm h1), Pi.single_apply,
          ite_eq_left h2.symm, zero_smul, zero_sub, map_smul, map_neg, map_smul, phi_single]
        simp only [smul_smul, ← neg_smul]
        congr 1
        push_cast
        linear_combination (-(c * (rS k : F) * (natSgn (rU k) : F))) *
          natSgn_cast_mul_self (F := F) x
      · rw [ite_eq_right h2, smul_zero, Pi.single_apply, ite_eq_right (Ne.symm h1),
          Pi.single_apply, ite_eq_right (Ne.symm h2), zero_smul, zero_smul, sub_zero, smul_zero,
          map_zero]
  exact LinearMap.congr_fun key v

theorem inBlock_E (k : Fin 24) {w : M F} (hw : InBlock w) : InBlock (d4tData.E F k w) := by
  rw [← phi_psi hw, E_phi]
  exact inBlock_phi _

theorem rootOp_root_d4 (k : Fin 24) :
    d4tData.rootOp F (Tag.D4.rootCertificate.root k) = d4tData.E F k :=
  MinData.rootOp_root (by rw [rootCertificate_length]; exact k.2)

theorem exists_root_eq_d4 {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    ∃ k : Fin 24, Tag.D4.rootCertificate.root k = γ := by
  obtain ⟨k, hk, hkγ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .D4) hγ
  rw [rootCertificate_length] at hk
  exact ⟨⟨k, hk⟩, hkγ⟩

theorem inBlock_rootOp (γ : Fin Tag.D4.rank → ℤ) {w : M F} (hw : InBlock w) :
    InBlock (d4tData.rootOp F γ w) := by
  by_cases hγ : IsRoot Tag.D4 γ
  · obtain ⟨k, rfl⟩ := exists_root_eq_d4 hγ
    rw [rootOp_root_d4]
    exact inBlock_E k hw
  · rw [MinData.rootOp_eq_zero hγ, LinearMap.zero_apply]
    exact fun _ _ => rfl

theorem xu_mem_blockStab (γ : Fin Tag.D4.rank → ℤ) (c : F) :
    d4tData_valid.xu F γ c ∈ blockStab F := fun w hw =>
  ⟨by
    rw [MinData.Valid.xu_apply]
    exact hw.add ((inBlock_rootOp γ hw).smul c),
   by
    change InBlock ((1 - c • d4tData.rootOp F γ) w)
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]
    exact hw.sub ((inBlock_rootOp γ hw).smul c)⟩

theorem minGroup_le_blockStab : d4tData_valid.minGroup F ≤ blockStab F :=
  (Subgroup.closure_le _).2 fun _ ⟨γ, _, c, hg⟩ => hg ▸ xu_mem_blockStab γ c

variable (F) in
@[expose] def blockRep : d4tData_valid.minGroup F →* (V F ≃ₗ[F] V F) :=
  (blockHom F).comp (Subgroup.inclusion minGroup_le_blockStab)

theorem blockRep_apply (g : d4tData_valid.minGroup F) (v : V F) :
    blockRep F g v = psi F (((g : (Module.End F (M F))ˣ) : Module.End F (M F)) (phi F v)) :=
  rfl

theorem blockRep_xm (k : Fin 24) (c : F) :
    blockRep F (d4tData_valid.xm F (Tag.D4.rootCertificate.root k) c) =
      eichler (quadPlus 4 F) (Pi.single (rU k) 1)
        ((((rS k : ℤ) : F) * c) • Pi.single (rW k) 1) := by
  have hne := (rootData_spec k).1
  have hpol : polar (quadPlus 4 F) (Pi.single (rU k) 1)
      ((((rS k : ℤ) : F) * c) • Pi.single (rW k) 1) = 0 := by
    rw [polar_smul_right, polar_single_single hne, smul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [blockRep_apply]
  change psi F ((d4tData_valid.xu F (Tag.D4.rootCertificate.root k) c :
    Module.End F (M F)) (phi F v)) = _
  rw [MinData.Valid.xu_apply, rootOp_root_d4, E_phi, map_add, map_smul, psi_phi, psi_phi,
    eichler_apply (quadPlus_single _) hpol, polar_single, polar_smul_right, polar_single,
    QuadraticMap.map_smul, quadPlus_single, nMap_apply, smul_zero, zero_mul, add_zero,
    smul_eq_mul]
  module

end CFSG.HardMathSupport.Lang.Coordinator.D4Bridge
