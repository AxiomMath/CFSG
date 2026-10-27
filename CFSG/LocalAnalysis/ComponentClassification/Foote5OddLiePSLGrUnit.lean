module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrSp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL CFSG.LieType.BorelTits

variable {n : ℕ} {K : Type} [Field K]

theorem slGraphFieldAut_apply (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    CatalogueBGraphField.slGraphFieldAut n K σ g = gfLift σ g := by
  ext i j
  rfl

theorem fixedGroup_slGraphFieldAut {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) :
    ClassicalInvolution.Balance.fixedGroup (CatalogueBGraphField.slGraphFieldAut n K σ) =
      unitarySL n σ := by
  ext g
  rw [ClassicalInvolution.Balance.mem_fixedGroup, slGraphFieldAut_apply, gfLift_eq_iff hσσ]

variable [Finite K]

theorem eq_one_unitary {p e : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hKe : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (fieldAut n K (unitaryInvolution K p e) * dualAut n K) =
      fieldAut n K (unitaryInvolution K p e) * dualAut n K * r)
    (hRc : ∀ s, (fieldAut n K (unitaryInvolution K p e) * dualAut n K) s = s →
      Odd (orderOf s) → ∀ r ∈ R, MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  set σ := unitaryInvolution K p e with hσdef
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hKe
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hKe
    intro h
    exact ha (by rw [← hσdef, h]; rfl)
  have hστ : ∀ τ : K ≃+* K, ∀ x, σ (τ x) = τ (σ x) := fun τ x => by
    rw [hσdef, unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hq := isQuasisimple_unitarySL hp2 hKe hn
  have hQ₀ : Open.IsComponentOf (unitarySL n σ)
      (ClassicalInvolution.Balance.fixedGroup (CatalogueBGraphField.slGraphFieldAut n K σ)) := by
    rw [fixedGroup_slGraphFieldAut hσσ]
    exact ⟨le_rfl, Open.IsSubnormal.refl _,
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)⟩
  have hδ : ∀ g, (fieldAut n K σ * dualAut n K) (proj n K g) =
      proj n K (CatalogueBGraphField.slGraphFieldAut n K σ g) := fun g => by
    rw [fieldAut_mul_dualAut_proj, slGraphFieldAut_apply]
  intro r hr
  obtain ⟨D, τ, rfl⟩ := Burgoyne.PSL.exists_semilinear_of_odd hn (odd_orderOf_of_mem hRodd hr)
  have hfix : ∀ g ∈ unitarySL n σ,
      (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g :=
    fun g hg => fix_of_component hinj _ hδ hQ₀ hRodd hRi hRc hr hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  have hex : ∀ g ∈ unitarySL n σ, (D : Matrix (Fin n) (Fin n) K) *
      ((SpecialLinearGroup.map τ.toRingHom g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g := by
    intro g hg
    have h := slConj_map_eq_of_commutator_eq hperf hfix hg
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simpa only [CatalogueBHigherLinearAction.slConjugation_matrix] using this
  have hDD : ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ g ∈ unitarySL n σ, SpecialLinearGroup.map τ.toRingHom g = g →
      (D : Matrix (Fin n) (Fin n) K) * g = g * D := by
    intro g hg hgτ
    have h1 := hex g hg
    rw [hgτ] at h1
    calc (D : Matrix (Fin n) (Fin n) K) * g
        = (D : Matrix (Fin n) (Fin n) K) * g * (((D⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * D) := by rw [hDD, Matrix.mul_one]
      _ = g * D := by rw [← Matrix.mul_assoc, h1]
  have hDs : (D : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) ((D : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) := by
    refine eq_scalar_of_commute_sign_rot h2 hn (fun i j hij => ?_) (fun i j hij => ?_)
    · have := hcomm _ (signSL_mem_unitarySL σ hij) (map_signSL τ _ _)
      rwa [coe_signSL] at this
    · have := hcomm _ (rotSL_mem_unitarySL σ hij) (map_rotSL τ hij)
      rwa [coe_rotSL] at this
  have hD : conjAut n K D = 1 := conjAut_eq_one_of_eq_scalar _ hDs
  have hτ : τ = 1 := by
    refine eq_one_of_fix_norm_one hσσ hσ1 (hστ τ) fun u hu => ?_
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hu
      exact zero_ne_one hu
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hN : σ u * u = 1 := by rw [mul_comm]; exact hu
    have h1 := hex _ (diagSL_mem_unitarySL h01 hu0 hN)
    have hsc : ∀ M : Matrix (Fin n) (Fin n) K, (D : Matrix (Fin n) (Fin n) K) * M *
        ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
      intro M
      have hcD : Commute (D : Matrix (Fin n) (Fin n) K) M := by
        rw [hDs]
        exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) M
      rw [hcD.eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    rw [hsc] at h1
    have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    simpa [diagSL] using this
  rw [hD, hτ, map_one, one_mul]

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr
