module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniData
import CFSG.LocalAnalysis.AGLEmbeddingD2.SimpleQuotient
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open

variable {ℓ f : ℕ} {K : Type} [Field K]

section Hom

variable (h : UnitaryFieldData ℓ f K)

abbrev UG : Subgroup (GL (Fin 3) K) :=
  primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[expose] noncomputable def conjUHom : UG h →* MulAut (SG h) where
  toFun A := primeFormConjSU h _ A
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change ((1 : UG h) : GL (Fin 3) K) * g * ((1 : UG h) : GL (Fin 3) K)⁻¹ = g
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
  map_mul' A B := MulEquiv.ext fun g => Subtype.ext (by
    change ((A * B : UG h) : GL (Fin 3) K) * g * ((A * B : UG h) : GL (Fin 3) K)⁻¹ =
      (A : GL (Fin 3) K) * ((B : GL (Fin 3) K) * g * (B : GL (Fin 3) K)⁻¹) *
        (A : GL (Fin 3) K)⁻¹
    rw [Subgroup.coe_mul]
    group)

@[expose] noncomputable def fieldUHom : (K ≃+* K) →* MulAut (SG h) where
  toFun σ := primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change glAut 1 (g : GL (Fin 3) K) = g
    rw [map_one]
    rfl)
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (by
    change glAut (σ * τ) (g : GL (Fin 3) K) = glAut σ (glAut τ (g : GL (Fin 3) K))
    rw [map_mul]
    rfl)

variable {h}

theorem coe_conjUHom_apply (A : UG h) (g : SG h) :
    ((conjUHom h A g : SG h) : GL (Fin 3) K) = (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ :=
  rfl

theorem fieldUHom_apply_entry (σ : K ≃+* K) (g : SG h) (i j : Fin 3) :
    (((fieldUHom h σ g : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) :=
  rfl

theorem fieldUHom_conj (σ : K ≃+* K) (A : UG h) :
    fieldUHom h σ * conjUHom h A * (fieldUHom h σ)⁻¹ =
      conjUHom h (primeFormFieldU h (isPrimeFormGram_one (n := 3)) σ A) := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply]
  change glAut σ ((A : GL (Fin 3) K) * glAut σ⁻¹ (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹) =
    glAut σ (A : GL (Fin 3) K) * g * (glAut σ (A : GL (Fin 3) K))⁻¹
  simp only [map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem conjUHom_of_mem (s : SG h) :
    conjUHom h ⟨(s : GL (Fin 3) K), ((mem_gramSU_iff_unitary h).1 s.2).1⟩ = MulAut.conj s :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem conjUHom_scalar_mul {A B : UG h} (c : Kˣ)
    (hAB : (A : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c * B) :
    conjUHom h A = conjUHom h B := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_conjUHom_apply, coe_conjUHom_apply, hAB]
  set s := Matrix.GeneralLinearGroup.scalar (Fin 3) c
  set X := (B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹
  calc s * (B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (s * (B : GL (Fin 3) K))⁻¹ = s * X * s⁻¹ := by
        simp only [X]
        group
    _ = X := by rw [← (commute_scalar c X).eq, mul_inv_cancel_right]

end Hom

section Quot

variable [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2)
include hℓ

theorem center_SG : Subgroup.center (SG h) = normOneScalars h (SG h) 3 := by
  refine le_antisymm (fun z hz => ?_) (normOneScalars_le_center h _ 3)
  have hz' : projU h z ∈ Subgroup.center (PU h) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, hz y]
  rw [center_PU_eq_bot h hℓ, Subgroup.mem_bot] at hz'
  rw [← ker_projU]
  exact MonoidHom.mem_ker.2 hz'

theorem map_normOneScalars_mulAut (β : MulAut (SG h)) :
    (normOneScalars h (SG h) 3).map (β : SG h →* SG h) = normOneScalars h (SG h) 3 := by
  rw [← center_SG h hℓ]
  exact Subgroup.characteristic_iff_map_eq.1
    (inferInstance : (Subgroup.center (SG h)).Characteristic) β

@[expose] noncomputable def quotU : MulAut (SG h) →* MulAut (PU h) where
  toFun β := QuotientGroup.congr _ _ β (map_normOneScalars_mulAut h hℓ β)
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g =>
    QuotientGroup.congr_mk _ _ _ _ g
  map_mul' β γ := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    show QuotientGroup.congr _ _ (β * γ) (map_normOneScalars_mulAut h hℓ (β * γ)) (g : PU h) =
      QuotientGroup.congr _ _ β (map_normOneScalars_mulAut h hℓ β)
        (QuotientGroup.congr _ _ γ (map_normOneScalars_mulAut h hℓ γ) (g : PU h))
    rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    rfl

variable {h}

theorem quotU_projU (β : MulAut (SG h)) (g : SG h) :
    quotU h hℓ β (projU h g) = projU h (β g) :=
  QuotientGroup.congr_mk _ _ β (map_normOneScalars_mulAut h hℓ β) g

theorem quotU_conjUHom (A : UG h) :
    quotU h hℓ (conjUHom h A) = primeFormConjHom h _ A :=
  MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    change quotU h hℓ (conjUHom h A) (projU h g) = primeFormConjHom h _ A (projU h g)
    rw [quotU_projU]
    exact (primeFormConjHom_mk h _ A g).symm

theorem quotU_fieldUHom (σ : K ≃+* K) : quotU h hℓ (fieldUHom h σ) = fieldAut h σ :=
  MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    change quotU h hℓ (fieldUHom h σ) (projU h g) = fieldAut h σ (projU h g)
    rw [quotU_projU, fieldAut_projU]
    rfl

theorem quotU_injective (hperf : commutator (SG h) = ⊤) : Function.Injective (quotU h hℓ) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  refine CFSG.AGLEmbeddingD2.eq_one_of_forall_mul_inv_mem_center
    (by rw [← commutator_def]; exact hperf) β fun x => ?_
  have e : quotU h hℓ β (projU h x) = projU h x := by rw [hβ]; rfl
  rw [quotU_projU] at e
  rw [center_SG h hℓ, ← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]

theorem card_le_pow_three_SG (hperf : commutator (SG h) = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (SG h))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 3 := by
  have hinj := quotU_injective hℓ hperf
  have := card_le_pow_three h hℓ hp hp2 hpℓ
    ((CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hinj p E).2 hE)
  rwa [Subgroup.card_map_of_injective hinj] at this

end Quot

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
