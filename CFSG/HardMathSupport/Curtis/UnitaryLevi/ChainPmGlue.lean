module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainDet
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainKerDim
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PmOfKerdims

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K]

@[expose] noncomputable def detU (M : Type*) [AddCommGroup M] [Module K M] :
    LinearMap.GeneralLinearGroup K M →* Kˣ :=
  Units.map (LinearMap.det : (M →ₗ[K] M) →* K)

theorem coe_detU {M : Type*} [AddCommGroup M] [Module K M] (A : LinearMap.GeneralLinearGroup K M) :
    ((detU M A : Kˣ) : K) = LinearMap.det ((A : LinearMap.GeneralLinearGroup K M) : Module.End K M) :=
  rfl

theorem eq_one_of_detU_eq_one {M : Type*} [AddCommGroup M] [Module K M] (hM : finrank K M = 1)
    (A : LinearMap.GeneralLinearGroup K M) (hA : detU M A = 1) : A = 1 := by
  obtain ⟨ν, hν⟩ := exists_units_scalar_of_finrank_one hM A
  have hM' : Module.Finite K M := Module.finite_of_finrank_pos (by omega : 0 < finrank K M)
  have h1 : ((detU M A : Kˣ) : K) = ν := by
    rw [coe_detU, det_eq_pow_of_forall _ (ν : K) hν, hM, pow_one]
  rw [hA] at h1
  have : (ν : K) = 1 := h1.symm
  refine Units.ext (LinearMap.ext fun m => ?_)
  rw [hν m, this, one_smul]
  rfl

theorem detU_eq_of_scalar {M : Type*} [AddCommGroup M] [Module K M] (hM : finrank K M = 1)
    (A : LinearMap.GeneralLinearGroup K M) (ν : K)
    (hν : ∀ m, (A : Module.End K M) m = ν • m) : ((detU M A : Kˣ) : K) = ν := by
  have hM' : Module.Finite K M := Module.finite_of_finrank_pos (by omega : 0 < finrank K M)
  rw [coe_detU, det_eq_pow_of_forall _ ν hν, hM, pow_one]

variable {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem inv_of_pow_three {c : K} (hc : c ^ 3 = 1) : (c ^ 2)⁻¹ = c :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hc)

open scoped Classical in
theorem pm_of_chain_two [CharP K 2] [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
    {W : ℕ → Submodule K V} {U : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hK : Nat.card K = 4) (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (hσc : ∀ c : K, σ c = c ^ 2) (h : ChainStabData B 2 W U) (hW0 : W 0 = ⊥)
    (hlt : ∀ j, 1 ≤ j → j ≤ 2 → W (j - 1) < W j)
    (hiso : W 2 ≤ (W 2).orthogonalBilin B) (hM : finrank K (perpQuot B (W 2)) = 1)
    (d : Fin 3 → ℕ) (hd : ∀ S T : Finset (Fin 3), ∑ i ∈ S, d i = ∑ i ∈ T, d i → S = T)
    (hd0 : d 0 = 2 * finrank K (PieceQ (W 0) (W 1)))
    (hd1 : d 1 = 2 * finrank K (PieceQ (W 1) (W 2))) (hd2 : d 2 = 1)
    (φ : K ≃+* K) (τ : V ≃+ V) (hτ : ∀ c v, τ (c • v) = φ c • τ v) (e e' : U)
    (hee' : ∀ v, ((e' : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (τ v) =
      τ (((e : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)) :
    e' = e ∨ e' = e⁻¹ := by
  have hs : 1 ≤ 2 := by norm_num
  set θ := h.chainHom hW0 hlt hs with hθ
  have hinjθ : Function.Injective θ := h.chainHom_injective hW0 hlt hs
  have hmono : ∀ j, j < 2 → W j ≤ W (j + 1) := fun j hj => by
    have := hlt (j + 1) (by omega) (by omega)
    simpa using this.le
  have hu3 : ∀ u : U, (u : LinearMap.GeneralLinearGroup K V) ^ 3 = 1 := by
    intro u
    have h1 : θ (u ^ 3) = θ 1 := by
      rw [map_pow, map_one]
      refine Prod.ext ?_ ?_
      · funext i
        simpa using units_pow_three_of_card_four hK _
      · have := card_generalLinearGroup_one hK hM
        have h3 := pow_card_eq_one' (G := LinearMap.GeneralLinearGroup K (perpQuot B (W 2)))
          (x := (θ u).2)
        rw [this] at h3
        simpa using h3
    have := hinjθ h1
    exact congrArg Subtype.val (show u ^ 3 = 1 from this)
  let χ : Fin 3 → (U →* Kˣ) :=
    ![(Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 0).comp ((MonoidHom.fst _ _).comp θ),
      (Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 1).comp ((MonoidHom.fst _ _).comp θ),
      (detU (perpQuot B (W 2))).comp ((MonoidHom.snd _ _).comp θ)]
  have hinj : ∀ u : U, (∀ i, χ i u = 1) → u = 1 := by
    intro u hu
    apply hinjθ
    rw [map_one]
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i
      · simpa [χ] using hu 0
      · simpa [χ] using hu 1
    · exact eq_one_of_detU_eq_one hM _ (by simpa [χ] using hu 2)
  have hker : ∀ (u : U) (lam : Kˣ),
      Module.finrank K (LinearMap.ker (((u : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) - (lam : K) • 1)) = ∑ i, d i * (if χ i u = lam then 1 else 0) := by
    intro u lam
    obtain ⟨ν, hν, hform⟩ := finrank_ker_chain_eq_scalOf_of_finrank_one hσ hB hs hW0 hmono hiso h hK
      u (hu3 u) hM lam
    rw [hform]
    have hν' : ((χ 2 u : Kˣ) : K) = ν := by
      refine detU_eq_of_scalar hM _ ν fun m => ?_
      show ((((h.chainHom hW0 hlt hs u).2 : LinearMap.GeneralLinearGroup K _) : Module.End K _)) m = _
      rw [chainHom_snd_eq_perpEnd h hW0 hlt hs u]
      exact hν m
    have hc : ∀ i : Fin 2, (σ (h.scalOf u i))⁻¹ = h.scalOf u i := by
      intro i
      rw [← chainHom_fst_eq_scalOf h hW0 hlt hs u i, hσc]
      apply inv_of_pow_three
      have := congrArg Units.val (units_pow_three_of_card_four hK ((θ u).1 i))
      simpa using this
    simp only [Fin.sum_univ_two, Fin.sum_univ_three, hc, hd0, hd1, hd2]
    have e0 : (χ 0 u = lam) ↔ h.scalOf u 0 = (lam : K) := by
      rw [← chainHom_fst_eq_scalOf h hW0 hlt hs u 0, ← Units.ext_iff]
      rfl
    have e1 : (χ 1 u = lam) ↔ h.scalOf u 1 = (lam : K) := by
      rw [← chainHom_fst_eq_scalOf h hW0 hlt hs u 1, ← Units.ext_iff]
      rfl
    have e2 : (χ 2 u = lam) ↔ ν = (lam : K) := by
      rw [← hν', ← Units.ext_iff]
    simp only [e0, e1, e2]
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod]
    split_ifs <;> simp <;> ring
  exact pm_of_kerdims hK U χ hinj d hd hker φ τ hτ e e' hee'

end CFSG.HardMathSupport.Curtis.UnitaryLevi
