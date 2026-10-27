module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussBasis
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHD4OddLev

public section

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

theorem fh_basisEquiv_mem_orthogonalGroup {F V ι : Type} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0)
    (b b' : Module.Basis ι F V) (hb : ∀ i j, polar Q (b i) (b j) = if i = j then 1 else 0)
    (hb' : ∀ i j, polar Q (b' i) (b' j) = if i = j then 1 else 0) :
    b.equiv b' (Equiv.refl ι) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have key : (polarBilin Q).compl₁₂ (b.equiv b' (Equiv.refl ι) : V →ₗ[F] V)
      (b.equiv b' (Equiv.refl ι) : V →ₗ[F] V) = polarBilin Q := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, polarBilin_apply_apply, hb, hb']
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h := LinearMap.congr_fun₂ key v v
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, polarBilin_apply_apply, polar_self,
    two_smul] at h
  have h' : (2 : F) * Q (b.equiv b' (Equiv.refl ι) v) = 2 * Q v := by
    rw [two_mul, two_mul]
    exact h
  exact mul_left_cancel₀ h2 h'

theorem fh_simFamO_one_neg_one : FHSimFamO 1 (-1) := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hsim, one_mul]
  have ha2' : ∀ v, a (a v) = -v := fun v => by rw [ha2, neg_one_smul]
  have hyO : Levi.embSL 𝔽₃ 4 fhLevY ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
    Levi.embSL_mem_orthogonalGroup _
  have hy2 : ∀ v, Levi.embSL 𝔽₃ 4 fhLevY (Levi.embSL 𝔽₃ 4 fhLevY v) = -v :=
    fh_embSL_sq (F := 𝔽₃) fhLevY_sq
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hK hQ haO ha2'
  obtain ⟨m', hm', ⟨ab'⟩⟩ := exists_adaptedBasis hK hQ hyO hy2
  rw [finrank_d4] at hm hm'
  obtain rfl : m = 4 := by omega
  obtain rfl : m' = 4 := by omega
  set θ := ab'.basis.equiv ab.basis (Equiv.refl _) with hθ
  have hθO : θ ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
    fh_basisEquiv_mem_orthogonalGroup h2 ab'.basis ab.basis ab'.orth ab.orth
  have hθb : ∀ i, θ (ab'.basis i) = ab.basis i := fun i => by
    rw [hθ, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hcomm : a * θ = θ * Levi.embSL 𝔽₃ 4 fhLevY := by
    refine ab'.basis.ext' fun i => ?_
    rcases i with k | k
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hθb, ← ab.inr_eq, ← ab'.inr_eq, hθb]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hθb, ab.inr_eq, ha2', ab'.inr_eq, hy2,
        map_neg, hθb]
  have hac : a = θ * Levi.embSL 𝔽₃ 4 fhLevY * θ⁻¹ :=
    calc a = a * θ * θ⁻¹ := by group
      _ = θ * Levi.embSL 𝔽₃ 4 fhLevY * θ⁻¹ := by rw [hcomm]
  refine fh_smul_of_conj hodd hβ hθO hac ?_ ?_
  · rw [← map_mul, ← map_mul, fhLevT_comm_Y]
  · rw [← map_mul, ← map_mul, fhLevL_comm_Y]

end CFSG.OddStandard.SmallF3.Omega
