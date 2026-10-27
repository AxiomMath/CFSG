module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeField
import all CFSG.Fischer.F4
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer

variable {E : Type*} [AddCommGroup E] [Finite E]

theorem exists_coords_of_ringHom (hE : Nat.card E = 2 ^ 8) (φ : F4 →+* AddMonoid.End E)
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E)
    (hφρ : ∀ a g, φ a * ρ g = ρ g * φ a) :
    ∃ (c : E ≃+ (Fin 4 → F4)) (M : SpecialLinearGroup (Fin 4) F4 →* SpecialLinearGroup (Fin 4) F4),
      (∀ a x, c (φ a x) = a • c x) ∧
        ∀ g x, c (ρ g x) = (M g : Matrix (Fin 4) (Fin 4) F4) *ᵥ c x := by
  let _ : Module F4 E := Module.compHom E φ
  have hsmul : ∀ (a : F4) (x : E), a • x = φ a x := fun a x => rfl
  have : Module.Finite F4 E := Module.Finite.of_finite
  have hF4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have hfr : Module.finrank F4 E = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := F4) (V := E)
    rw [hE, hF4] at h
    have h' : (4 : ℕ) ^ 4 = 4 ^ Module.finrank F4 E := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h').symm
  let b := Module.finBasisOfFinrankEq F4 E hfr
  let L : SpecialLinearGroup (Fin 4) F4 → (E →ₗ[F4] E) := fun g =>
    { toFun := ρ g
      map_add' := map_add (ρ g)
      map_smul' := fun a x => by
        rw [RingHom.id_apply, hsmul, hsmul, ← addMonoidEnd_mul_apply, ← hφρ,
          addMonoidEnd_mul_apply] }
  have hL : ∀ g x, L g x = ρ g x := fun g x => rfl
  let Mm : SpecialLinearGroup (Fin 4) F4 → Matrix (Fin 4) (Fin 4) F4 :=
    fun g => LinearMap.toMatrix b b (L g)
  have hMmul : ∀ g h, Mm (g * h) = Mm g * Mm h := by
    intro g h
    simp only [Mm]
    rw [← LinearMap.toMatrix_mul]
    congr 1
    ext x
    rw [hL, map_mul, addMonoidEnd_mul_apply, Module.End.mul_apply, hL, hL]
  have hM1 : Mm 1 = 1 := by
    simp only [Mm]
    rw [← LinearMap.toMatrix_id b]
    congr 1
    ext x
    rw [hL, map_one]
    rfl
  let dh : SpecialLinearGroup (Fin 4) F4 →* F4 :=
    { toFun := fun g => (Mm g).det
      map_one' := by rw [hM1, det_one]
      map_mul' := fun g h => by rw [hMmul, det_mul] }
  have hdet : ∀ g, (Mm g).det = 1 := by
    intro g
    have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (n := 4)
      (K := F4) (by norm_num)
    have hk : g ∈ dh.toHomUnits.ker := Abelianization.commutator_subset_ker dh.toHomUnits
      (hperf.commutator_eq_top ▸ Subgroup.mem_top g)
    rw [MonoidHom.mem_ker, Units.ext_iff] at hk
    exact hk
  let M : SpecialLinearGroup (Fin 4) F4 →* SpecialLinearGroup (Fin 4) F4 :=
    { toFun := fun g => ⟨Mm g, hdet g⟩
      map_one' := Subtype.ext hM1
      map_mul' := fun g h => Subtype.ext (hMmul g h) }
  refine ⟨b.equivFun.toAddEquiv, M, fun a x => ?_, fun g x => ?_⟩
  · change b.equivFun (a • x) = a • b.equivFun x
    exact map_smul b.equivFun a x
  · change b.equivFun (L g x) = Mm g *ᵥ b.equivFun x
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (L g) x).symm

@[expose] noncomputable def veeMulVecAddEquiv (A : GL (Fin 4) F4) : (Fin 4 → F4) ≃+ (Fin 4 → F4) where
  toFun v := ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *ᵥ v
  invFun v := (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ v
  left_inv v := by
    simp only [mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  right_inv v := by
    simp only [mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  map_add' v w := mulVec_add _ v w

@[expose] noncomputable def veeSmulAddEquiv (μ : F4) (hμ : μ ≠ 0) :
    (Fin 4 → F4) ≃+ (Fin 4 → F4) where
  toFun v := μ • v
  invFun v := μ⁻¹ • v
  left_inv v := by
    change μ⁻¹ • μ • v = v
    rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
  right_inv v := by
    change μ • μ⁻¹ • v = v
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
  map_add' v w := smul_add μ v w

theorem veeFrobHom_mul_self (x : F4) : veeFrobHom x * veeFrobHom x = veeFrobHom (veeFrobHom x) := by
  revert x
  decide

theorem map_veeFrobHom_map_veeFrobHom (N : Matrix (Fin 4) (Fin 4) F4) :
    (N.map veeFrobHom).map veeFrobHom = N := by
  ext i j
  simp only [Matrix.map_apply, veeFrobHom_veeFrobHom]

omit [Finite E] in
theorem exists_addEquiv_frob_of_equivariant (φ : F4 →+* AddMonoid.End E)
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E)
    (N : SpecialLinearGroup (Fin 4) F4 →* SpecialLinearGroup (Fin 4) F4)
    (hNs : Function.Surjective N)
    (hNf : ∀ g, (N (veeFrob g) : Matrix (Fin 4) (Fin 4) F4) =
      (N g : Matrix (Fin 4) (Fin 4) F4).map veeFrobHom)
    (β₀ : E ≃+ (Fin 4 → F4)) (s : F4 ≃+* F4)
    (hβρ : ∀ g e, β₀ (ρ g e) = (N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ β₀ e)
    (hβφ : ∀ a e, β₀ (φ a e) = s a • β₀ e) (τ : E →+ E) (hτ : Function.Bijective τ)
    (hτρ : ∀ g e, τ (ρ g e) = ρ (veeFrob g) (τ e))
    (hτφ : ∀ a e, τ (φ a e) = φ (veeFrobHom a) (τ e)) :
    ∃ β : E ≃+ (Fin 4 → F4),
      (∀ g e, β (ρ g e) = (N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ β e) ∧
        ∀ e, β (τ e) = veeFrobHom ∘ β e := by
  let τ' : (Fin 4 → F4) →+ (Fin 4 → F4) :=
    (β₀.toAddMonoidHom.comp τ).comp β₀.symm.toAddMonoidHom
  have hτ' : ∀ v, τ' v = β₀ (τ (β₀.symm v)) := fun v => rfl
  let fr : (Fin 4 → F4) →+ (Fin 4 → F4) :=
    { toFun := fun v => veeFrobHom ∘ v
      map_zero' := by funext i; simp
      map_add' := fun v w => by funext i; simp }
  let f := fr.comp τ'
  have hf : ∀ v, f v = veeFrobHom ∘ τ' v := fun v => rfl
  have hsf : ∀ x, s (veeFrobHom x) = veeFrobHom (s x) := fun x => by
    change s (x * x) = s x * s x
    exact map_mul s x x
  have hτ'smul : ∀ (a : F4) v, τ' (a • v) = veeFrobHom a • τ' v := by
    intro a v
    have h1 : β₀.symm (a • v) = φ (s.symm a) (β₀.symm v) := by
      rw [AddEquiv.symm_apply_eq, hβφ, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [hτ', h1, hτφ, hβφ, hsf, RingEquiv.apply_symm_apply, hτ']
  have hτ'N : ∀ g v, τ' ((N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) =
      ((N g : Matrix (Fin 4) (Fin 4) F4).map veeFrobHom) *ᵥ τ' v := by
    intro g v
    have h1 : β₀.symm ((N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) = ρ g (β₀.symm v) := by
      rw [AddEquiv.symm_apply_eq, hβρ, AddEquiv.apply_symm_apply]
    rw [hτ', h1, hτρ, hβρ, hNf, hτ']
  have hflin : ∀ (a : F4) v, f (a • v) = a • f v := by
    intro a v
    rw [hf, hτ'smul, hf]
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, veeFrobHom_veeFrobHom]
  have hfcomm : ∀ (h : SpecialLinearGroup (Fin 4) F4) v,
      f ((h : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) = (h : Matrix (Fin 4) (Fin 4) F4) *ᵥ f v := by
    intro h v
    obtain ⟨g, rfl⟩ := hNs h
    rw [hf, hτ'N, veeFrobHom_comp_mulVec, map_veeFrobHom_map_veeFrobHom, hf]
  obtain ⟨l, hl⟩ := exists_smul_of_commute f hflin hfcomm
  have hl0 : l ≠ 0 := by
    intro hl0
    have hfinj : Function.Injective f := by
      have h1 : Function.Injective τ' := fun v w hvw => by
        rw [hτ', hτ'] at hvw
        exact β₀.symm.injective (hτ.1 (β₀.injective hvw))
      have h2 : Function.Injective fr := fun v w hvw => by
        funext i
        have h := congrFun hvw i
        simp only [fr, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h
        rw [← veeFrobHom_veeFrobHom (v i), h, veeFrobHom_veeFrobHom]
      exact h2.comp h1
    have h1 := hfinj ((hl (Pi.single 0 1)).trans ((hl 0).trans (by rw [hl0, zero_smul, zero_smul])).symm)
    have h2 := congrFun h1 0
    simp at h2
  set μ := veeFrobHom l with hμ
  have hμ0 : μ ≠ 0 := by
    intro h
    apply hl0
    rw [← veeFrobHom_veeFrobHom l, ← hμ, h, map_zero]
  refine ⟨β₀.trans (veeSmulAddEquiv μ hμ0), fun g e => ?_, fun e => ?_⟩
  · change μ • β₀ (ρ g e) = (N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ (μ • β₀ e)
    rw [hβρ, mulVec_smul]
  · change μ • β₀ (τ e) = veeFrobHom ∘ (μ • β₀ e)
    have h1 : β₀ (τ e) = τ' (β₀ e) := by rw [hτ', AddEquiv.symm_apply_apply]
    have h2 : τ' (β₀ e) = veeFrobHom ∘ f (β₀ e) := by
      rw [hf]
      funext i
      simp only [Function.comp_apply, veeFrobHom_veeFrobHom]
    rw [h1, h2, hl]
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, hμ]
    rw [← mul_assoc, veeFrobHom_mul_self]

theorem exists_addEquiv_of_omega (h2 : ∀ x : E, x + x = 0) (hE : Nat.card E = 2 ^ 8)
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E) (hρ : ∀ g, ρ g = 1 → g = 1)
    (ω : AddMonoid.End E) (hω : ω * ω + ω + 1 = 0) (hωρ : ∀ g, ω * ρ g = ρ g * ω)
    (τ : E →+ E) (hτ : Function.Bijective τ) (hτρ : ∀ g e, τ (ρ g e) = ρ (veeFrob g) (τ e))
    (hτω : ∀ e, τ (ω e) = ω (ω (τ e))) :
    ∃ β : E ≃+ (Fin 4 → F4),
      ((∀ g e, β (ρ g e) = (g : Matrix (Fin 4) (Fin 4) F4) *ᵥ β e) ∨
        ∀ g e, β (ρ g e) =
          ((g⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)ᵀ *ᵥ β e) ∧
      ∀ e, β (τ e) = veeFrobHom ∘ β e := by
  have h2E := addMonoidEnd_two_eq_zero h2
  obtain ⟨φ, hφval, hφω⟩ := exists_ringHom_omega ω hω h2E
  have hωω : ω * ω = ω + 1 := by
    have h2' : (ω + 1) + (ω + 1) = 0 := by rw [← two_mul, h2E, zero_mul]
    calc ω * ω = ω * ω + ((ω + 1) + (ω + 1)) := by rw [h2', add_zero]
      _ = (ω * ω + ω + 1) + (ω + 1) := by abel
      _ = ω + 1 := by rw [hω, zero_add]
  have hφρ : ∀ a g, φ a * ρ g = ρ g * φ a := by
    intro a g
    rw [hφval]
    rcases f4_cases a with rfl | rfl | rfl | rfl
    · rw [veeScalarFun_zero, zero_mul, mul_zero]
    · rw [veeScalarFun_one, one_mul, mul_one]
    · rw [veeScalarFun_omega]
      exact hωρ g
    · rw [veeScalarFun_omega_sq, add_mul, mul_add, hωρ g, one_mul, mul_one]
  have hτφ : ∀ a e, τ (φ a e) = φ (veeFrobHom a) (τ e) := by
    intro a e
    rw [hφval, hφval]
    rcases f4_cases a with rfl | rfl | rfl | rfl
    · rw [map_zero, veeScalarFun_zero]
      exact map_zero τ
    · rw [map_one, veeScalarFun_one]
      rfl
    · rw [veeScalarFun_omega, show veeFrobHom F4.ω = F4.ω * F4.ω from by decide,
        veeScalarFun_omega_sq, hτω, ← hωω]
      rfl
    · rw [veeScalarFun_omega_sq, show veeFrobHom (F4.ω * F4.ω) = F4.ω from by decide,
        veeScalarFun_omega]
      change τ (ω e + e) = ω (τ e)
      rw [map_add, hτω, ← addMonoidEnd_mul_apply, hωω]
      change ω (τ e) + τ e + τ e = ω (τ e)
      rw [add_assoc, h2 (τ e), add_zero]
  obtain ⟨c, M, hcφ, hcρ⟩ := exists_coords_of_ringHom hE φ ρ hφρ
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply hρ
    ext x
    apply c.injective
    rw [hcρ, hg, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    rfl
  have hMbij : Function.Bijective M := ⟨hMinj, Finite.injective_iff_surjective.1 hMinj⟩
  obtain ⟨A, σ', hform⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (n := 4) (K := F4) (by norm_num) (MulEquiv.ofBijective M hMbij)
  let β₀ : E ≃+ (Fin 4 → F4) :=
    (c.trans (veeMulVecAddEquiv A)).trans (AddEquiv.piCongrRight fun _ => σ'.symm.toAddEquiv)
  have hβ₀ : ∀ e, β₀ e = σ'.symm ∘ (((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *ᵥ c e) :=
    fun e => rfl
  have hβφ : ∀ a e, β₀ (φ a e) = σ'.symm a • β₀ e := by
    intro a e
    rw [hβ₀, hβ₀, hcφ, mulVec_smul]
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  rcases hform with hform | hform
  ·
    have hβρ : ∀ g e, β₀ (ρ g e) = ((MonoidHom.id _ g : SpecialLinearGroup (Fin 4) F4) :
        Matrix (Fin 4) (Fin 4) F4) *ᵥ β₀ e := by
      intro g e
      have hg := hform g
      change (M g : Matrix (Fin 4) (Fin 4) F4) = _ at hg
      rw [hβ₀, hβ₀, hcρ, hg, mulVec_mulVec, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        ← mulVec_mulVec, symm_comp_map_mulVec]
      rfl
    obtain ⟨β, hβ1, hβ2⟩ := exists_addEquiv_frob_of_equivariant φ ρ (MonoidHom.id _)
      (fun g => ⟨g, rfl⟩) (fun g => rfl) β₀ σ'.symm hβρ hβφ τ hτ hτρ hτφ
    exact ⟨β, Or.inl hβ1, hβ2⟩
  ·
    let N := (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F4).toMonoidHom
    have hN : ∀ g, (N g : Matrix (Fin 4) (Fin 4) F4) =
        ((g⁻¹ : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)ᵀ := fun g => rfl
    have hβρ : ∀ g e, β₀ (ρ g e) = (N g : Matrix (Fin 4) (Fin 4) F4) *ᵥ β₀ e := by
      intro g e
      have hg := hform g
      change (M g : Matrix (Fin 4) (Fin 4) F4) = _ at hg
      rw [hN, hβ₀, hβ₀, hcρ, hg, mulVec_mulVec, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        ← mulVec_mulVec, symm_comp_map_mulVec]
    have hNs : Function.Surjective N :=
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 F4).surjective
    have hNf : ∀ g, (N (veeFrob g) : Matrix (Fin 4) (Fin 4) F4) =
        (N g : Matrix (Fin 4) (Fin 4) F4).map veeFrobHom := by
      intro g
      rw [hN, hN, ← map_inv, coe_veeFrob, Matrix.transpose_map]
    obtain ⟨β, hβ1, hβ2⟩ := exists_addEquiv_frob_of_equivariant φ ρ N hNs hNf β₀ σ'.symm
      hβρ hβφ τ hτ hτρ hτφ
    exact ⟨β, Or.inr fun g e => (hβ1 g e).trans (by rw [hN]), hβ2⟩

end CFSG.SeitzReduction.LinearPilot
