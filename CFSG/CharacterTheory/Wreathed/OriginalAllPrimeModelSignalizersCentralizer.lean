module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTools

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem centralizer_le_modelBase [Fintype F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) :
    ∀ g ∈ modelC b m hm heven Sigma hSigma,
      g ∈ Subgroup.centralizer ((modelLayer b m hm heven Sigma hSigma ⊓
        modelC b m hm heven Sigma hSigma : Subgroup _) : Set _) →
      g ∈ modelBase b m hm heven Sigma hSigma := by
  intro g hg hgc
  have hgl := (mem_modelC_iff g).mp hg
  have hσ : ((g.right : Sigma) : F ≃+* F) = 1 := by
    apply eq_one_of_fieldSL_fixes_torus h2
    intro t ht
    have hmem : (SemidirectProduct.inl (specialInclusion F b m hm heven t) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈
          modelLayer b m hm heven Sigma hSigma ⊓ modelC b m hm heven Sigma hSigma :=
      ⟨inl_specialInclusion_mem_modelLayer t, (inl_specialInclusion_mem_modelC_iff t).mpr ht⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hgc _ hmem
    have hconj : g * SemidirectProduct.inl (specialInclusion F b m hm heven t) * g⁻¹ =
        SemidirectProduct.inl (specialInclusion F b m hm heven t) := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [semidirect_conj_inl, fieldAction_specialInclusion] at hconj
    have hσt : fieldSL F g.right t ∈ Subgroup.centralizer {weyl F} :=
      CFSG.Wreathed.OddFieldTorus.fieldAction_mem_torus (g.right : F ≃+* F) ht
    have hiσt := (CFSG.Wreathed.ReducedInvolution.specialInclusion_mem_centralizer_iff
      (b := b) (hm := hm) (heven := heven) _).mpr hσt
    have hc := CFSG.Wreathed.ReducedInvolution.centralizer_involutionY_comm hb hgl hiσt
    rw [hc, mul_inv_cancel_right] at hconj
    exact specialInclusion_injective F b m hm heven (SemidirectProduct.inl_injective hconj)
  have hr : g.right = 1 := Subtype.ext hσ
  refine ⟨g.left, SemidirectProduct.ext rfl ?_⟩
  rw [SemidirectProduct.right_inl, hr]

theorem psi_conj_modelY (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    psi F b m hm heven Sigma hSigma
        (modelY b m hm heven Sigma hSigma * h * (modelY b m hm heven Sigma hSigma)⁻¹) =
      psi F b m hm heven Sigma hSigma h := by
  rw [map_mul, map_mul, map_inv]
  apply Prod.ext
  · simp only [Prod.fst_mul, Prod.fst_inv]
    rw [mul_comm, inv_mul_cancel_left]
  · simp only [Prod.snd_mul, Prod.snd_inv]
    have hy : (psi F b m hm heven Sigma hSigma (modelY b m hm heven Sigma hSigma)).2 = 1 := rfl
    rw [hy, one_mul, inv_one, mul_one]

theorem signalizer_le_modelLayer [Finite F] (h4 : 4 ∣ m) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ U ∈ signalizers ⊤ (modelC b m hm heven Sigma hSigma) r,
        U ≤ modelLayer b m hm heven Sigma hSigma := by
  intro r hr hr2 U hU
  obtain ⟨-, hpU, hnorm, hinf⟩ := hU
  have hy2 : modelY b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma = 1 := by
    rw [modelY_eq, ← map_mul, involutionY_mul_self h4, map_one]
  have hyC : modelY b m hm heven Sigma hSigma ∈ modelC b m hm heven Sigma hSigma :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  intro u hu
  have hinv := conj_eq_inv_of_inf_centralizer_eq_bot hy2 (hnorm hyC) hinf hu
  have hψ := psi_conj_modelY (b := b) (hm := hm) (heven := heven) (hSigma := hSigma) u
  rw [hinv, map_inv] at hψ
  have hsq : psi F b m hm heven Sigma hSigma u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hψ]
    exact inv_mul_cancel _
  obtain ⟨k, hk⟩ := hpU ⟨u, hu⟩
  have hpow : psi F b m hm heven Sigma hSigma u ^ r ^ k = 1 := by
    rw [← map_pow]
    have : u ^ r ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
  have hcop : Nat.Coprime 2 (r ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  have h1 : psi F b m hm heven Sigma hSigma u = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hsq, hpow⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  rw [modelLayer_eq_matrixLayer, ← psi_ker]
  exact h1

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
