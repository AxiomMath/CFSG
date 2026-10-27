module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Block
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdKer
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Signs
public import CFSG.Adapters.TauCetiExceptional.TwistedD4Match

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Twisted
  CFSG.TauCetiBridge.Minuscule

variable {F : Type} [Field F]

theorem eq_zero_of_diagonal_of_sq {d : ℕ} {y Δ : Module.End F (Fin d →₀ F)} (hy : y * y = 0)
    (hyd : ∀ a, y (Finsupp.single a 1) a = 0)
    (hΔ : ∀ a b, a ≠ b → Δ (Finsupp.single a 1) b = 0) (hsq : (y + Δ) * (y + Δ) = 0) :
    Δ = 0 := by
  have hdiag : ∀ a, Δ (Finsupp.single a 1) = Δ (Finsupp.single a 1) a • Finsupp.single a 1 :=
    fun a => by
      ext b
      rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : a = b
      · subst h
        rw [ite_eq_left rfl, mul_one]
      · rw [ite_eq_right h, mul_zero, hΔ a b h]
  have happ : ∀ (u : Fin d →₀ F) (a : Fin d), Δ u a = Δ (Finsupp.single a 1) a * u a := by
    intro u a
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u u' hu hu' => rw [map_add, Finsupp.add_apply, hu, hu', Finsupp.add_apply, mul_add]
    | single b c =>
      rw [show Finsupp.single b c = c • Finsupp.single b 1 from
          (Finsupp.smul_single_one b c).symm, map_smul, Finsupp.smul_apply, Finsupp.smul_apply,
        smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
      by_cases h : b = a
      · subst h
        rw [ite_eq_left rfl]
        ring
      · rw [ite_eq_right h, hΔ b a h]
        ring
  have hd : ∀ a, Δ (Finsupp.single a 1) a = 0 := fun a => by
    have h1 : y (y (Finsupp.single a 1)) a = 0 := by
      rw [← Module.End.mul_apply, hy, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
    have h2 : y (Δ (Finsupp.single a 1)) a = 0 := by
      rw [hdiag a, map_smul, Finsupp.smul_apply, hyd, smul_zero]
    have h3 : Δ (y (Finsupp.single a 1)) a = 0 := by rw [happ, hyd, mul_zero]
    have h4 : Δ (Δ (Finsupp.single a 1)) a =
        Δ (Finsupp.single a 1) a * Δ (Finsupp.single a 1) a := happ _ a
    have key : ((y + Δ) * (y + Δ)) (Finsupp.single a 1) a = 0 := by
      rw [hsq, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
    simp only [Module.End.mul_apply, LinearMap.add_apply, map_add, Finsupp.add_apply, h1, h2, h3,
      h4, zero_add] at key
    exact mul_self_eq_zero.1 key
  refine LinearMap.ext fun u => Finsupp.ext fun a => ?_
  rw [happ, hd a, zero_mul, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]

theorem intCast_ne_zero_of_mul_self {z : ℤ} (h : z * z = 1) : (z : F) ≠ 0 := fun h0 => by
  have := congrArg (Int.cast : ℤ → F) h
  rw [Int.cast_mul, h0, zero_mul, Int.cast_one] at this
  exact zero_ne_one this


theorem adjMap_apply_single_apply (v : RootModule Tag.D4 F) (a b : Fin d4tData.d) :
    adjMap F d4tSigns d4tData v (Finsupp.single a 1) b =
      v.sum fun l c =>
        c * adjMap F d4tSigns d4tData (Finsupp.single l 1) (Finsupp.single a 1) b := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show Finsupp.single l (v l) = v l • Finsupp.single l 1 from
      (Finsupp.smul_single_one l (v l)).symm, map_smul, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem adjMap_inl_apply_single_apply (j : Fin Tag.D4.rank) {a b : Fin d4tData.d} (hab : a ≠ b) :
    adjMap F d4tSigns d4tData (Finsupp.single (Sum.inl j) 1) (Finsupp.single a 1) b = 0 := by
  rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.D4 F) = hVec Tag.D4 F j from rfl,
    adjMap_hVec, LinearMap.smul_apply, cartanOp_single, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.single_apply, ite_eq_right hab, smul_zero, smul_zero]

theorem adjMap_inr_apply_single_apply {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α)
    (a b : Fin d4tData.d) :
    adjMap F d4tSigns d4tData (Finsupp.single (Sum.inr ⟨α, hα⟩) 1) (Finsupp.single a 1) b =
      ((d4tSigns.sRoot α : ℤ) : F) * ((rootMat d4tData α b a : ℤ) : F) := by
  rw [← rootVec_eq_single F hα, adjMap_rootVec, LinearMap.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, rootOp_single_apply_eq_cast, rootMat, natMat_apply]

theorem rootOp_single_self {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) (a : Fin d4tData.d) :
    d4tData.rootOp F γ (Finsupp.single a 1) a = 0 := by
  have h := rootMat_self d4tData_valid posDef_cartan_D4 hγ a
  rw [rootMat, natMat_apply] at h
  rw [rootOp_single_apply_eq_cast, h, Int.cast_zero]

theorem coeff_root_eq_zero {v : RootModule Tag.D4 F}
    (hv : ∀ z : M F, InBlock z → adjMap F d4tSigns d4tData v z = 0) {α : Fin Tag.D4.rank → ℤ}
    (hα : IsRoot Tag.D4 α) : v (Sum.inr ⟨α, hα⟩) = 0 := by
  obtain ⟨k, hk⟩ := exists_root_eq_d4 hα
  have hne := (rootData_spec k).1
  have hxw : dualC (rU k) ≠ rW k := fun h => hne (by rw [← h, cIdx_dualC])
  have hab : nIdx (dualC (rU k)) ≠ nIdx (rW k) := fun h => hxw (nIdx_injective h)
  have hrs : rS k * rS k = 1 := by
    rcases (rootData_spec k).2 with h | h <;> rw [h] <;> norm_num
  have hσ : (natSgn (dualC (rU k)) * rS k * natSgn (rW k)) *
      (natSgn (dualC (rU k)) * rS k * natSgn (rW k)) = 1 := by
    calc (natSgn (dualC (rU k)) * rS k * natSgn (rW k)) *
          (natSgn (dualC (rU k)) * rS k * natSgn (rW k))
        = (natSgn (dualC (rU k)) * natSgn (dualC (rU k))) * (rS k * rS k) *
            (natSgn (rW k) * natSgn (rW k)) := by ring
      _ = 1 := by rw [natSgn_mul_self, natSgn_mul_self, hrs, one_mul, one_mul]
  have hE : d4tData.rootOp F α (Finsupp.single (nIdx (dualC (rU k))) 1) (nIdx (rW k)) =
      ((natSgn (dualC (rU k)) * rS k * natSgn (rW k) : ℤ) : F) := by
    rw [← hk, rootOp_root_d4, E_single_natIdx, ite_eq_left rfl, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have hmat : rootMat d4tData α (nIdx (rW k)) (nIdx (dualC (rU k))) ≠ 0 := by
    intro h0
    rw [rootMat, natMat_apply] at h0
    rw [rootOp_single_apply_eq_cast, h0, Int.cast_zero] at hE
    exact intCast_ne_zero_of_mul_self hσ hE.symm
  have h0 := congrArg (fun u : M F => u (nIdx (rW k))) (hv _ (inBlock_single (dualC (rU k)) 1))
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h0
  rw [adjMap_apply_single_apply, Finsupp.sum, Finset.sum_eq_single (Sum.inr ⟨α, hα⟩)] at h0
  · rw [adjMap_inr_apply_single_apply] at h0
    refine (mul_eq_zero.1 h0).resolve_right (mul_ne_zero ?_ ?_)
    · exact intCast_ne_zero_of_mul_self (d4tSigns.sRoot_mul_self α)
    · exact intCast_ne_zero_of_mul_self (rootMat_ne_zero d4tData_valid hα hmat).2
  · intro l _ hl
    rcases l with j | ⟨β, hβ⟩
    · rw [adjMap_inl_apply_single_apply j hab, mul_zero]
    · have hβα : β ≠ α := fun h => hl (by subst h; rfl)
      rw [adjMap_inr_apply_single_apply hβ,
        rootMat_eq_zero_of_ne d4tData_valid posDef_cartan_D4 hα hβ hβα hmat, Int.cast_zero,
        mul_zero, mul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.1 h, zero_mul]

theorem adjMap_apply_single_of_ne {v : RootModule Tag.D4 F}
    (hv : ∀ z : M F, InBlock z → adjMap F d4tSigns d4tData v z = 0) {a b : Fin d4tData.d}
    (hab : a ≠ b) : adjMap F d4tSigns d4tData v (Finsupp.single a 1) b = 0 := by
  rw [adjMap_apply_single_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases l with j | ⟨β, hβ⟩
  · rw [adjMap_inl_apply_single_apply j hab, mul_zero]
  · rw [coeff_root_eq_zero hv hβ, zero_mul]

theorem apply_eq_of_blockHom_eq_one {g : blockStab F} (hg : blockHom F g = 1) {z : M F}
    (hz : InBlock z) : ((g : (Module.End F (M F))ˣ) : Module.End F (M F)) z = z := by
  have h : psi F (((g : (Module.End F (M F))ˣ) : Module.End F (M F)) z) = psi F z := by
    have := DFunLike.congr_fun hg (psi F z)
    rwa [blockHom_apply, phi_psi hz] at this
  rw [← phi_psi (g.2 z hz).1, h, phi_psi hz]

theorem commute_of_conj_eq_adjMap {G Gi y : Module.End F (M F)} {s : F} (hss : s * s = 1)
    (hGiG : Gi * G = 1) (hyy : y * y = 0) (hyd : ∀ a, y (Finsupp.single a 1) a = 0)
    (hfix : ∀ z, InBlock z → G z = z) (hfix' : ∀ z, InBlock z → Gi z = z)
    (hyb : ∀ z, InBlock z → InBlock (y z)) {w w' : RootModule Tag.D4 F}
    (hw : G * (s • y) * Gi = adjMap F d4tSigns d4tData w)
    (hw' : adjMap F d4tSigns d4tData w' = s • y) : Commute G y := by
  have hY : G * y * Gi = adjMap F d4tSigns d4tData (s • w) := by
    rw [map_smul, ← hw, mul_smul_comm, smul_mul_assoc, smul_smul, hss, one_smul]
  have hy : y = adjMap F d4tSigns d4tData (s • w') := by
    rw [map_smul, hw', smul_smul, hss, one_smul]
  have hΔ : G * y * Gi - y = adjMap F d4tSigns d4tData (s • w - s • w') := by
    rw [map_sub, ← hY, ← hy]
  have hvan : ∀ z, InBlock z → adjMap F d4tSigns d4tData (s • w - s • w') z = 0 :=
    fun z hz => by
      rw [← hΔ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hfix' z hz,
        hfix _ (hyb z hz), sub_self]
  have hdiag : ∀ a b, a ≠ b → (G * y * Gi - y) (Finsupp.single a 1) b = 0 := fun a b hab => by
    rw [hΔ]
    exact adjMap_apply_single_of_ne hvan hab
  have hsum : y + (G * y * Gi - y) = G * y * Gi := by abel
  have hsq : (y + (G * y * Gi - y)) * (y + (G * y * Gi - y)) = 0 := by
    rw [hsum]
    calc G * y * Gi * (G * y * Gi) = G * y * (Gi * G) * y * Gi := by noncomm_ring
      _ = 0 := by rw [hGiG, mul_one, mul_assoc G y y, hyy, mul_zero, zero_mul]
  have hconj : G * y * Gi = y := sub_eq_zero.1 (eq_zero_of_diagonal_of_sq hyy hyd hdiag hsq)
  show G * y = y * G
  calc G * y = G * y * Gi * G := by rw [mul_assoc (G * y), hGiG, mul_one]
    _ = y * G := by rw [hconj]

theorem commute_rootOp_of_blockRep_eq_one {g : d4tData_valid.minGroup F} (hg : blockRep F g = 1)
    (γ : Fin Tag.D4.rank → ℤ) :
    Commute ((g : (Module.End F (M F))ˣ) : Module.End F (M F)) (d4tData.rootOp F γ) := by
  by_cases hγ : IsRoot Tag.D4 γ
  swap
  · rw [MinData.rootOp_eq_zero hγ]
    exact Commute.zero_right _
  have hb : blockHom F ⟨g, minGroup_le_blockStab g.2⟩ = 1 := hg
  obtain ⟨w, hw⟩ := (minGroup_le_adjNormalizer d4tData_valid posDef_cartan_D4 d4tSigns_check F
    g.2).1 (rootVec Tag.D4 F γ)
  rw [adjMap_rootVec] at hw
  refine commute_of_conj_eq_adjMap (s := ((d4tSigns.sRoot γ : ℤ) : F)) ?_ (Units.inv_mul _)
    (d4tData_valid.rootOp_mul_self γ) (rootOp_single_self hγ)
    (fun z hz => apply_eq_of_blockHom_eq_one hb hz)
    (fun z hz => apply_eq_of_blockHom_eq_one (g := ⟨g, minGroup_le_blockStab g.2⟩⁻¹)
      (by rw [map_inv, hb, inv_one]) hz)
    (fun z hz => inBlock_rootOp γ hz) hw (adjMap_rootVec F d4tSigns γ)
  rw [← Int.cast_mul, d4tSigns.sRoot_mul_self, Int.cast_one]

theorem adMin_eq_one_of_blockRep_eq_one {g : d4tData_valid.minGroup F} (hg : blockRep F g = 1) :
    adMin d4tData_valid posDef_cartan_D4 d4tSigns_check F g = 1 := by
  rw [adMin_apply, ad_eq_one_iff]
  exact fun i => ⟨commute_rootOp_of_blockRep_eq_one hg _, commute_rootOp_of_blockRep_eq_one hg _⟩

end CFSG.HardMathSupport.Lang.Coordinator.D4Bridge
