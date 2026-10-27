module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsMatrix
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizers
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolution

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

section Conjugation

variable {F : Type} [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def iota :
    SpecialLinearGroup (Fin 2) F →* SemilinearExtension F b m hm heven Sigma hSigma :=
  (SemidirectProduct.inl : CentralExtension F b m hm heven →* _).comp
    (specialInclusion F b m hm heven)

theorem iota_apply (Z : SpecialLinearGroup (Fin 2) F) :
    iota b m hm heven Sigma hSigma Z = SemidirectProduct.inl (specialInclusion F b m hm heven Z) :=
  rfl

theorem iota_injective : Function.Injective (iota b m hm heven Sigma hSigma) :=
  SemidirectProduct.inl_injective.comp (specialInclusion_injective F b m hm heven)

@[expose] noncomputable def yV : CentralExtension F b m hm heven :=
  (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * specialInclusion F b m hm heven (weyl F)

theorem modelY_eq_inl_yV :
    modelY b m hm heven Sigma hSigma = SemidirectProduct.inl (yV b m hm heven) :=
  rfl

theorem modelLayer_eq_range :
    modelLayer b m hm heven Sigma hSigma = (iota b m hm heven Sigma hSigma).range := by
  rw [modelLayer, iota, MonoidHom.range_comp]

theorem commute_cyclicGenerator_sq (v : CentralExtension F b m hm heven) :
    cyclicGenerator F b m hm heven ^ 2 * v = v * cyclicGenerator F b m hm heven ^ 2 :=
  (Subgroup.mem_center_iff.mp (CentralSL2.cyclicGenerator_sq_mem_center F b m hm heven) v).symm

theorem commute_inl_pow (k : ℕ) (v : CentralExtension F b m hm heven) :
    (SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ k) :
        SemilinearExtension F b m hm heven Sigma hSigma) * SemidirectProduct.inl v =
      SemidirectProduct.inl v *
        SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ k) := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact ((Commute.pow_left (commute_cyclicGenerator_sq b m hm heven v) k) : _)

theorem modelY_eq :
    modelY b m hm heven Sigma hSigma =
      SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4)) *
        iota b m hm heven Sigma hSigma (weyl F) := by
  rw [modelY, map_mul]
  rfl

theorem modelX_eq :
    modelX b m hm heven Sigma hSigma = iota b m hm heven Sigma hSigma (minusIdentity F) := by
  rw [modelX, CentralSL2.cyclicGenerator_pow_m]
  rfl

theorem modelY_conj_iota (Z : SpecialLinearGroup (Fin 2) F) :
    modelY b m hm heven Sigma hSigma * iota b m hm heven Sigma hSigma Z *
        (modelY b m hm heven Sigma hSigma)⁻¹ =
      iota b m hm heven Sigma hSigma (weyl F * Z * (weyl F)⁻¹) := by
  set A : SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4)) with hA
  set I := iota b m hm heven Sigma hSigma with hI
  have hc : A * I (weyl F * Z * (weyl F)⁻¹) = I (weyl F * Z * (weyl F)⁻¹) * A :=
    commute_inl_pow b m hm heven Sigma hSigma (m / 4) _
  have hB : I (weyl F) * I Z * (I (weyl F))⁻¹ = I (weyl F * Z * (weyl F)⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [modelY_eq]
  calc A * I (weyl F) * I Z * (A * I (weyl F))⁻¹ =
      A * (I (weyl F) * I Z * (I (weyl F))⁻¹) * A⁻¹ := by group
    _ = I (weyl F * Z * (weyl F)⁻¹) := by rw [hB, hc, mul_inv_cancel_right]

theorem iota_conj_modelY (X : SpecialLinearGroup (Fin 2) F) :
    iota b m hm heven Sigma hSigma X * modelY b m hm heven Sigma hSigma *
        (iota b m hm heven Sigma hSigma X)⁻¹ =
      SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4)) *
        iota b m hm heven Sigma hSigma (X * weyl F * X⁻¹) := by
  set A : SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4)) with hA
  set I := iota b m hm heven Sigma hSigma with hI
  have hc : A * I X = I X * A := commute_inl_pow b m hm heven Sigma hSigma (m / 4) _
  have hB : I X * I (weyl F) * (I X)⁻¹ = I (X * weyl F * X⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [modelY_eq]
  calc I X * (A * I (weyl F)) * (I X)⁻¹ = (I X * A) * I (weyl F) * (I X)⁻¹ := by group
    _ = A * (I X * I (weyl F) * (I X)⁻¹) := by rw [← hc]; group
    _ = A * I (X * weyl F * X⁻¹) := by rw [hB]

theorem conj_weyl_of_conj_modelY {X : SpecialLinearGroup (Fin 2) F}
    (hX : iota b m hm heven Sigma hSigma X * modelY b m hm heven Sigma hSigma *
        (iota b m hm heven Sigma hSigma X)⁻¹ =
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma) :
    X * weyl F * X⁻¹ = minusIdentity F * weyl F := by
  set A : SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4)) with hA
  set I := iota b m hm heven Sigma hSigma with hI
  have hc : A * I (minusIdentity F) = I (minusIdentity F) * A :=
    commute_inl_pow b m hm heven Sigma hSigma (m / 4) _
  rw [iota_conj_modelY, modelX_eq, modelY_eq] at hX
  have h2 : I (minusIdentity F) * (A * I (weyl F)) = A * I (minusIdentity F * weyl F) := by
    rw [map_mul, ← mul_assoc, ← hc, mul_assoc]
  rw [h2] at hX
  exact iota_injective b m hm heven Sigma hSigma (mul_left_cancel hX)

theorem inr_conj_iota (τ : Sigma) (Z : SpecialLinearGroup (Fin 2) F) :
    (SemidirectProduct.inr τ : SemilinearExtension F b m hm heven Sigma hSigma) *
        iota b m hm heven Sigma hSigma Z * (SemidirectProduct.inr τ)⁻¹ =
      iota b m hm heven Sigma hSigma (fieldSL F τ Z) := by
  rw [iota_apply, iota_apply, ← fieldAction_specialInclusion F b m hm heven Sigma hSigma,
    SemidirectProduct.inl_aut, map_inv]

theorem conj_iota (τ : Sigma) (w Z : SpecialLinearGroup (Fin 2) F) :
    (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ) *
        iota b m hm heven Sigma hSigma Z *
        (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ)⁻¹ =
      iota b m hm heven Sigma hSigma (w * fieldSL F τ Z * w⁻¹) := by
  have h := inr_conj_iota b m hm heven Sigma hSigma τ Z
  calc iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ *
        iota b m hm heven Sigma hSigma Z *
        (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ)⁻¹ =
      iota b m hm heven Sigma hSigma w * (SemidirectProduct.inr τ *
        iota b m hm heven Sigma hSigma Z * (SemidirectProduct.inr τ)⁻¹) *
        (iota b m hm heven Sigma hSigma w)⁻¹ := by group
    _ = _ := by rw [h, ← map_inv, ← map_mul, ← map_mul]

theorem conj_iota_of_mem_torus (τ : Sigma) {w Z : SpecialLinearGroup (Fin 2) F}
    (hw : w ∈ torus F) (hZ : Z ∈ torus F) :
    (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ) *
        iota b m hm heven Sigma hSigma Z *
        (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ)⁻¹ =
      iota b m hm heven Sigma hSigma (fieldSL F τ Z) := by
  have h := inr_conj_iota b m hm heven Sigma hSigma τ Z
  have hc : w * fieldSL F τ Z * w⁻¹ = fieldSL F τ Z := by
    rw [torus_comm hw (fieldSL_mem_torus (τ : F ≃+* F) hZ), mul_inv_cancel_right]
  have hc' : iota b m hm heven Sigma hSigma w * iota b m hm heven Sigma hSigma (fieldSL F τ Z) *
      (iota b m hm heven Sigma hSigma w)⁻¹ = iota b m hm heven Sigma hSigma (fieldSL F τ Z) := by
    rw [← map_inv, ← map_mul, ← map_mul, hc]
  calc iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ *
        iota b m hm heven Sigma hSigma Z *
        (iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ)⁻¹ =
      iota b m hm heven Sigma hSigma w * (SemidirectProduct.inr τ *
        iota b m hm heven Sigma hSigma Z * (SemidirectProduct.inr τ)⁻¹) *
        (iota b m hm heven Sigma hSigma w)⁻¹ := by group
    _ = _ := by rw [h, hc']

end Conjugation

section Centralizer

variable {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
  (hcard : Nat.card F = p ^ f) {m : ℕ} (hm : 0 < m) (heven : Even m)
  (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
  {Sigma : Subgroup (F ≃+* F)} (hd : Odd (Nat.card Sigma)) {b : Fˣ}
  (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) (hb : ¬ IsSquare b)

include hp hpodd hf hcard hm2 hd hSigma hb

theorem centralizer_comm {g g' : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.centralizer {yV b m hm heven})
    (hg' : g' ∈ Subgroup.centralizer {yV b m hm heven}) : g * g' = g' * g := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  exact hred.2.2.1 g hg g' hg'

theorem exists_eq_iF_of_odd {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g)) {g : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.centralizer {yV b m hm heven}) (hodd : Odd (orderOf g)) :
    ∃ w ∈ W, specialInclusion F b m hm heven w = g := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hall⟩ := hred
  obtain ⟨hmem, -⟩ := hall W hW
  exact (hmem g).mp ⟨hg, hodd⟩

theorem modelLayer_inf_modelC :
    modelLayer b m hm heven Sigma hSigma ⊓ modelC b m hm heven Sigma hSigma =
      (torus F).map (iota b m hm heven Sigma hSigma) := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, hMD, -⟩ := hred
  have hinj : Function.Injective (SemidirectProduct.inl : CentralExtension F b m hm heven →*
      SemilinearExtension F b m hm heven Sigma hSigma) := SemidirectProduct.inl_injective
  have key : modelLayer b m hm heven Sigma hSigma ⊓ modelC b m hm heven Sigma hSigma =
      ((specialInclusion F b m hm heven).range ⊓ Subgroup.centralizer
        {(cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (weyl F)}).map SemidirectProduct.inl := by
    rw [modelC, modelY, modelLayer]
    apply le_antisymm
    · intro w hw
      obtain ⟨⟨v, hv, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hw
      refine ⟨v, Subgroup.mem_inf.mpr ⟨hv, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      apply hinj
      rw [map_mul _ v, map_mul _ _ v]
      exact hc
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨⟨v, hv1, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hv2 ⊢
      rw [← map_mul, ← map_mul, hv2]
  rw [key, hMD, iota, ← Subgroup.map_map]
  rfl

theorem exists_eq_of_odd {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g))
    {g : SemilinearExtension F b m hm heven Sigma hSigma}
    (hg : g ∈ modelC b m hm heven Sigma hSigma) (hodd : Odd (orderOf g)) :
    ∃ w ∈ W, ∃ τ : Sigma, g = iota b m hm heven Sigma hSigma w * SemidirectProduct.inr τ := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hall⟩ := hred
  obtain ⟨-, ⟨φ, hφ⟩, hrest⟩ := hall W hW
  obtain ⟨-, hΘ, -⟩ := hrest φ hφ
  have : Finite (CentralExtension F b m hm heven) := inferInstance
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (Subgroup.centralizer {yV b m hm heven})))
  obtain ⟨Θ, hΘ⟩ := hΘ P
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := Θ.surjective ⟨g, hg⟩
  have hx₁ : x₁ = 1 := by
    have h1 : Odd (orderOf (x₁, x₂)) := by
      rw [← MulEquiv.orderOf_eq Θ, hx, ← Subgroup.orderOf_coe]
      exact hodd
    have h2 : x₁ ^ orderOf (x₁, x₂) = 1 := by
      have h := congrArg Prod.fst (pow_orderOf_eq_one (x₁, x₂))
      rwa [Prod.pow_fst, Prod.fst_one] at h
    obtain ⟨k, hk⟩ := P.isPGroup' x₁
    have hcop : Nat.Coprime (2 ^ k) (orderOf (x₁, x₂)) :=
      (Nat.coprime_two_left.mpr h1).pow_left k
    have h3 := pow_gcd_eq_one.mpr ⟨hk, h2⟩
    rw [hcop.gcd_eq_one] at h3
    exact (pow_one x₁).symm.trans h3
  refine ⟨x₂.left, x₂.left.2, x₂.right, ?_⟩
  have h := hΘ x₁ x₂
  rw [hx, hx₁] at h
  simp only [OneMemClass.coe_one, map_one, one_mul] at h
  rw [iota_apply]
  exact h

end Centralizer

end CFSG.Wreathed.OriginalAllPrime.IVFacts
