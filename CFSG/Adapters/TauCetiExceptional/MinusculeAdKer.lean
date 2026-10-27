module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdCarrier

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid)

section Field

variable (K : Type*) [Field K]

include hV in
theorem commute_rootOp_of_simple
    {g : Module.End K (Fin D.d →₀ K)}
    (hE : ∀ i, Commute g (D.rootOp K (Pi.single i 1)))
    (hF : ∀ i, Commute g (D.rootOp K (-Pi.single i 1))) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    Commute g (D.rootOp K γ) := by
  have hx : ∀ (γ : Fin τ.rank → ℤ) (c : K), Commute g (D.rootOp K γ) →
      Commute g (hV.endo K (hV.xm K γ c)) := fun γ c h => by
    rw [hV.endo_xm]
    exact (Commute.one_right g).add_right (h.smul_right c)
  have hn : ∀ i, Commute g (D.nOp K i) := fun i => by
    rw [← hV.endo_nm K i, Valid.nm, Valid.nt, hV.endo_mul, hV.endo_mul]
    exact ((hx _ _ (hE i)).mul_right (hx _ _ (hF i))).mul_right (hx _ _ (hE i))
  have hn' : ∀ i, Commute g (D.nInv K i) := fun i => by
    rw [← hV.endo_nm_inv K i]
    have := hn i
    rw [← hV.endo_nm K i] at this
    exact this.units_inv_right
  induction hγ with
  | basis j => exact hE j
  | @reflect i v hv ih =>
    obtain ⟨σ, hσ, h⟩ := hV.conj_rootOp (R := K) hv i
    have e : D.rootOp K (reflect τ i v) = σ • (D.nOp K i * D.rootOp K v * D.nInv K i) := by
      rw [h, smul_smul, hσ.mul_self, one_smul]
    rw [e]
    exact (((hn i).mul_right ih).mul_right (hn' i)).smul_right σ

include hV in
theorem commute_adjMap_of_simple
    (S : AdjSigns τ) {g : Module.End K (Fin D.d →₀ K)}
    (hE : ∀ i, Commute g (D.rootOp K (Pi.single i 1)))
    (hF : ∀ i, Commute g (D.rootOp K (-Pi.single i 1))) (v : RootModule τ K) :
    Commute g (adjMap K S D v) := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Commute.zero_right g
  | add v w hv hw => rw [map_add]; exact hv.add_right hw
  | single l c =>
    rw [← Finsupp.smul_single_one, map_smul]
    refine Commute.smul_right ?_ c
    rcases l with j | ⟨α, hα⟩
    · rw [show (Finsupp.single (Sum.inl j) 1 : RootModule τ K) = hVec τ K j from rfl, adjMap_hVec,
        ← rootOp_single_comm_neg_single hV K j]
      exact (((hE j).mul_right (hF j)).sub_right ((hF j).mul_right (hE j))).smul_right _
    · rw [← rootVec_eq_single K hα, adjMap_rootVec]
      exact (commute_rootOp_of_simple hV K hE hF hα).smul_right _

theorem eq_of_sRoot_smul_eq (S : AdjSigns τ) (γ : Fin τ.rank → ℤ)
    {X Y : Module.End K (Fin D.d →₀ K)}
    (h : ((S.sRoot γ : ℤ) : K) • X = ((S.sRoot γ : ℤ) : K) • Y) : X = Y := by
  have h' := congrArg (fun T => ((S.sRoot γ : ℤ) : K) • T) h
  simp only [smul_smul, ← Int.cast_mul, S.sRoot_mul_self, Int.cast_one, one_smul] at h'
  exact h'

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)

theorem ad_eq_one_iff
    (S : AdjSigns τ) (g : adjNormalizer K S D) :
    ad hV hpd S g = 1 ↔ ∀ i,
      Commute ((g : (Module.End K (Fin D.d →₀ K))ˣ) : Module.End K (Fin D.d →₀ K))
        (D.rootOp K (Pi.single i 1)) ∧
      Commute ((g : (Module.End K (Fin D.d →₀ K))ˣ) : Module.End K (Fin D.d →₀ K))
        (D.rootOp K (-Pi.single i 1)) := by
  constructor
  · intro h
    have key : ∀ v, Commute ((g : (Module.End K (Fin D.d →₀ K))ˣ) : Module.End K (Fin D.d →₀ K))
        (adjMap K S D v) := fun v => by
      have hv := congrArg (· * ((g : (Module.End K (Fin D.d →₀ K))ˣ) :
        Module.End K (Fin D.d →₀ K))) ((ad_apply_eq_iff hV hpd S g v v).1 (by rw [h]; rfl))
      simp only [mul_assoc, Units.inv_mul, mul_one] at hv
      exact hv
    intro i
    refine ⟨?_, ?_⟩
    · have h1 := (key (rootVec τ K (Pi.single i 1))).eq
      rw [adjMap_rootVec, mul_smul_comm, smul_mul_assoc] at h1
      exact eq_of_sRoot_smul_eq K S _ h1
    · have h1 := (key (rootVec τ K (-Pi.single i 1))).eq
      rw [adjMap_rootVec, mul_smul_comm, smul_mul_assoc] at h1
      exact eq_of_sRoot_smul_eq K S _ h1
  · intro h
    refine Units.ext (LinearMap.ext fun v => ?_)
    rw [Units.val_one, Module.End.one_apply, ad_apply_eq_iff,
      (commute_adjMap_of_simple hV K S (fun i => (h i).1) (fun i => (h i).2) v).eq, mul_assoc,
      Units.mul_inv, mul_one]

end Field

section Carrier

theorem commute_one_add_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (g E : Module.End R M) : Commute g (1 + E) ↔ Commute g E := by
  simp only [commute_iff_eq, mul_add, add_mul, mul_one, one_mul, add_right_inj]

theorem commute_units_iff {M : Type*} [Monoid M] (u v : Mˣ) :
    Commute u v ↔ Commute (u : M) (v : M) := by
  rw [commute_iff_eq, commute_iff_eq, Units.ext_iff, Units.val_mul, Units.val_mul]

theorem commute_map_iff {A B : Type*} [Monoid A] [Monoid B] (e : A ≃* B) (x y : A) :
    Commute (e x) (e y) ↔ Commute x y := by
  rw [commute_iff_eq, commute_iff_eq, ← map_mul, ← map_mul, e.injective.eq_iff]

variable {n : ℕ} (lab : Fin n ≃ Fin D.d) (L : Type) [Field L]

theorem commute_toMat_rootUnit_iff
    (z : Matrix.GeneralLinearGroup (Fin n) L)
    (γ : Fin τ.rank → ℤ) :
    Commute z (toMat lab L (rootUnit hV L γ 1)) ↔
      Commute (((toMat lab L).symm z : (Module.End L (Fin D.d →₀ L))ˣ) :
        Module.End L (Fin D.d →₀ L)) (D.rootOp L γ) := by
  conv_lhs => rw [← (toMat lab L).apply_symm_apply z]
  rw [commute_map_iff, commute_units_iff, coe_rootUnit, one_smul, commute_one_add_iff]

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {S : AdjSigns τ}
  (hS : S.check D = true) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L))
  (hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L))

theorem adCarrier_eq_one_iff (z : H) :
    adCarrier hV hpd hS lab L H hH z = 1 ↔ ∀ i,
      Commute (z : Matrix.GeneralLinearGroup (Fin n) L)
          (toMat lab L (rootUnit hV L (Pi.single i 1) 1)) ∧
        Commute (z : Matrix.GeneralLinearGroup (Fin n) L)
          (toMat lab L (rootUnit hV L (-Pi.single i 1) 1)) := by
  rw [adCarrier_apply, ad_eq_one_iff hV L hpd S]
  simp only [commute_toMat_rootUnit_iff]

theorem adCarrier_eq_one_iff' (z : H) :
    adCarrier hV hpd hS lab L H hH z = 1 ↔ ∀ i,
      ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((toMat lab L (rootUnit hV L (Pi.single i 1) 1) : Matrix.GeneralLinearGroup (Fin n) L) :
            Matrix (Fin n) (Fin n) L) =
        ((toMat lab L (rootUnit hV L (Pi.single i 1) 1) : Matrix.GeneralLinearGroup (Fin n) L) :
            Matrix (Fin n) (Fin n) L) *
          ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((toMat lab L (rootUnit hV L (-Pi.single i 1) 1) :
            Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((toMat lab L (rootUnit hV L (-Pi.single i 1) 1) :
            Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  rw [adCarrier_eq_one_iff]
  simp only [commute_iff_eq, Units.ext_iff, Units.val_mul]

end Carrier

end CFSG.TauCetiBridge.Minuscule
