module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKSim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKTri
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T
open CFSG.ClassicalInvolution.G2D4Models.Twin (z0 z2 z3 spinAction_z2_mul_z3
  spinAction_z3_mul_z0 spinAction_z0_mul_z2)
open CFSG.LieType.Universal.Spin (spinAction quadPlus nondegenerate_quadPlus mem_ker_spinAction_iff)
open CFSG.Open (StatedProj StatedOmega StatedQuadPlus)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "Q₀" => quadPlus 4 (ZMod 3)

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

private theorem fk_neg_ne_one :
    (LinearEquiv.neg (GaloisField 3 1) :
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) ≠
      1 := by
  intro h
  have h' := congrFun (LinearEquiv.congr_fun h (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)
  exact Q3MFOD.neg_one_ne_one_of_card_three
    ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three (by simpa using h')

private theorem fk_neg_mul_neg :
    (LinearEquiv.neg (GaloisField 3 1) :
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) *
      LinearEquiv.neg (GaloisField 3 1) = 1 :=
  LinearEquiv.ext fun v => by simp

theorem fk_tri_square {ρ : MulAut Spin₈} (hρ : FKTri ρ) {c : Spin₈}
    (hc : c ∈ Subgroup.center Spin₈) :
    spinAction Q₄ c = 1 ∨ spinAction Q₄ (ρ c) = 1 ∨ spinAction Q₄ (ρ (ρ c)) = 1 := by
  have e1 : ρ (z2 𝔽₃ * z3 𝔽₃) = z3 𝔽₃ * z0 𝔽₃ := by rw [map_mul, hρ.apply_z2, hρ.apply_z3]
  have e2 : ρ (z3 𝔽₃ * z0 𝔽₃) = z0 𝔽₃ * z2 𝔽₃ := by rw [map_mul, hρ.apply_z3, hρ.apply_z0]
  have e3 : ρ (z0 𝔽₃ * z2 𝔽₃) = z2 𝔽₃ * z3 𝔽₃ := by rw [map_mul, hρ.apply_z0, hρ.apply_z2]
  have hθb : spinAction Q₄ (z2 𝔽₃ * z3 𝔽₃) = 1 := spinAction_z2_mul_z3
  have hθb₁ : spinAction Q₄ (z3 𝔽₃ * z0 𝔽₃) = LinearEquiv.neg 𝔽₃ := spinAction_z3_mul_z0
  have hθb₂ : spinAction Q₄ (z0 𝔽₃ * z2 𝔽₃) = LinearEquiv.neg 𝔽₃ := spinAction_z0_mul_z2
  have hb1 : z2 𝔽₃ * z3 𝔽₃ ≠ 1 := by
    intro h
    have h' : z0 𝔽₃ * z2 𝔽₃ = 1 := ρ.injective (by rw [e3, h, map_one])
    rw [h', map_one] at hθb₂
    exact fk_neg_ne_one hθb₂.symm
  rcases (fk_mem_center_iff c).mp hc with h | h
  · exact Or.inl h
  · have hn : (LinearEquiv.neg 𝔽₃ :
        (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))⁻¹ = LinearEquiv.neg 𝔽₃ :=
      inv_eq_of_mul_eq_one_right fk_neg_mul_neg
    have hcb₁ : c * (z3 𝔽₃ * z0 𝔽₃) ∈ (spinAction Q₄).ker := by
      rw [MonoidHom.mem_ker, map_mul, h, hθb₁]
      exact fk_neg_mul_neg
    have hbk : z2 𝔽₃ * z3 𝔽₃ ∈ (spinAction Q₄).ker := hθb
    haveI : Invertible (2 : 𝔽₃) :=
      invertibleOfNonzero ClassicalInvolution.ModelFacts.TG3.two_ne_zero_three
    have hQ₄ : (quadPlus 4 𝔽₃).Nondegenerate := nondegenerate_quadPlus 4 𝔽₃
    have hbN := ((mem_ker_spinAction_iff Q₄ hQ₄ _).mp hbk).resolve_left hb1
    rcases (mem_ker_spinAction_iff Q₄ hQ₄ _).mp hcb₁ with h1 | h1
    ·
      have hc' : c = (z3 𝔽₃ * z0 𝔽₃)⁻¹ := eq_inv_of_mul_eq_one_left h1
      refine Or.inr (Or.inr ?_)
      rw [hc', map_inv, map_inv, e2, e3]
      rw [map_inv, hθb, inv_one]
    ·
      have hc' : c = (z2 𝔽₃ * z3 𝔽₃) * (z3 𝔽₃ * z0 𝔽₃)⁻¹ :=
        eq_mul_inv_of_mul_eq (h1.trans hbN.symm)
      refine Or.inr (Or.inl ?_)
      rw [hc', map_mul, map_inv, e1, e2, map_mul, map_inv, hθb₁, hθb₂, hn]
      exact fk_neg_mul_neg

private theorem fk_aut_conj_conj {G : Type*} [Group G] (τ : MulAut G) (q : G) :
    τ * MulAut.conj q * τ⁻¹ = MulAut.conj (τ q) := by
  ext g
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem fkInner_reduce (p : omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) (hp : p * p = 1) :
    ∃ (τ : MulAut (omegaProj (nondegenerate_quadPlus 4 (ZMod 3)))) (s : OGroup Q₀),
      s * s = 1 ∧ τ * MulAut.conj p * τ⁻¹ = projAut (nondegenerate_quadPlus 4 (ZMod 3)) s := by
  obtain ⟨e, he⟩ := fk_exists_equiv
  obtain ⟨ρ, hρ⟩ := fkTri_exists
  obtain ⟨p', rfl⟩ := e.surjective p
  obtain ⟨x, rfl⟩ := Q3MFOD.d4Proj_surjective p'
  have hxx : x * x ∈ Subgroup.center Spin₈ := by
    rw [← Q3MFOD.ker_d4Proj, MonoidHom.mem_ker, map_mul]
    exact e.injective (by rw [map_mul, map_one]; exact hp)
  obtain ⟨σ, hσ⟩ : ∃ σ : MulAut Spin₈, spinAction Q₄ (σ (x * x)) = 1 := by
    rcases fk_tri_square hρ hxx with h | h | h
    · exact ⟨1, h⟩
    · exact ⟨ρ, h⟩
    · exact ⟨ρ * ρ, h⟩
  have hss : fkSpin (σ x) * fkSpin (σ x) = 1 := by
    rw [← map_mul, ← map_mul]
    apply Subtype.ext
    rw [coe_fkSpin, hσ, map_one]
    rfl
  have hsΩ := fkSpin_mem_omegaGroup (σ x)
  refine ⟨MulAut.congr e (Q3MFOD.descAut σ), fkSpin (σ x), hss, ?_⟩
  rw [fk_aut_conj_conj]
  refine Eq.trans ?_
    (fj_projAut_eq_conj (nondegenerate_quadPlus 4 (ZMod 3)) ⟨fkSpin (σ x), hsΩ⟩).symm
  congr 1
  have h1 : ((MulAut.congr e (Q3MFOD.descAut σ) (e (d4Proj (GaloisField 3 1) x)) :
      omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) : ProjOrth Q₀) =
      toProj Q₀ (fkSpin (σ x)) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, Q3MFOD.descAut_apply]
    exact he _
  exact Subtype.ext h1

end CFSG.OddStandard.SmallF3.Omega
