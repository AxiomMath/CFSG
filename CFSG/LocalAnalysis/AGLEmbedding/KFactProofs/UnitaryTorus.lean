module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open scoped commutatorElement
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Skew

variable {K : Type} [Field K] (J : HermitianForm 3 K)

@[expose] def skewCoord (b : K) (hb : b + J.conj b = 0) : Coord J :=
  ⟨(0, b), by simpa using hb⟩

theorem skewCoord_mul (b b' : K) (hb : b + J.conj b = 0) (hb' : b' + J.conj b' = 0) :
    skewCoord J b hb * skewCoord J b' hb' =
      skewCoord J (b + b') (by rw [map_add]; linear_combination hb + hb') := by
  apply Subtype.ext
  rw [coord_mul_val]
  ext <;> simp [skewCoord]

theorem skewCoord_central (b : K) (hb : b + J.conj b = 0) (z : Coord J) :
    skewCoord J b hb * z = z * skewCoord J b hb := by
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val]
  ext <;> simp [skewCoord, add_comm]

end Skew

section CenterTorus

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem isUnitaryInvolution_conj : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution J.conj := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
  have : CharP K p := charP_of_card Fact.out hK
  have h := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := p)
    (f := f) hK
  have hc : J.conj = CFSG.LieType.BorelTits.unitaryInvolution K p f :=
    RingEquiv.ext fun x => by rw [hconj, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rwa [hc]

@[expose] def fixedField : Subfield K := (J.conj : K →+* K).eqLocusField (RingHom.id K)

omit [Finite K] [Fact p.Prime] hK in
theorem card_fixedField : Nat.card (fixedField J) = p ^ f := by
  rw [← hfix]
  exact Nat.card_congr (Equiv.refl _)

theorem exists_centerTorus (hf : 1 ≤ f) :
    ∃ ψ : Multiplicative (GaloisField p f) →* Coord J, Function.Injective ψ ∧
      (∀ a z, ψ a * z = z * ψ a) ∧
      ∀ μ : (GaloisField p f)ˣ, ∃ k : Kˣ, ∀ a : Multiplicative (GaloisField p f),
        hermitianTorusAction J k (ψ a) =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p f) * Multiplicative.toAdd a)) := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  obtain ⟨b₀, hb₀, hb₀t⟩ := hσ.exists_traceZero
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have : Fintype (fixedField J) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p f) = Fintype.card (fixedField J) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card p f (by omega),
      card_fixedField J hfix]
  let ι : GaloisField p f ≃+* fixedField J := FiniteField.ringEquivOfCardEq hcard
  have hι : ∀ a : GaloisField p f, J.conj (ι a : K) = (ι a : K) := fun a => (ι a).2
  have hskew : ∀ a : GaloisField p f, b₀ * (ι a : K) + J.conj (b₀ * (ι a : K)) = 0 := by
    intro a
    rw [map_mul, hι]
    linear_combination (ι a : K) * hb₀t
  let ψ : Multiplicative (GaloisField p f) →* Coord J :=
    { toFun := fun a => skewCoord J (b₀ * (ι (Multiplicative.toAdd a) : K))
        (hskew (Multiplicative.toAdd a))
      map_one' := by
        apply Subtype.ext
        ext <;> simp [skewCoord, coord_one_val]
      map_mul' := fun a b => by
        rw [skewCoord_mul]
        apply Subtype.ext
        ext <;> simp [skewCoord, mul_add] }
  refine ⟨ψ, fun a b hab => ?_, fun a z => skewCoord_central J _ (hskew _) z, fun μ => ?_⟩
  · have h1 := congrArg (fun z : Coord J => (z : K × K).2) hab
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, skewCoord] at h1
    have := mul_left_cancel₀ hb₀ h1
    exact Multiplicative.toAdd.injective (ι.injective (Subtype.ext this))
  · set m : K := (ι (μ : GaloisField p f) : K) with hm
    have hm0 : m ≠ 0 := by
      intro h0
      have : ι (μ : GaloisField p f) = 0 := Subtype.ext h0
      exact μ.ne_zero (ι.injective (by rw [this, map_zero]))
    have hmσ : J.conj m = m := hι _
    obtain ⟨c, hc⟩ := hσ.exists_norm (d := m⁻¹) (by rw [map_inv₀, hmσ])
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hc
      exact inv_ne_zero hm0 hc.symm
    have hinv : (J.conj c)⁻¹ * c⁻¹ = m := by rw [← mul_inv, hc, inv_inv]
    refine ⟨Units.mk0 c hc0, fun a => ?_⟩
    apply Subtype.ext
    rw [torusAction_val]
    ext
    · simp [ψ, skewCoord]
    · simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, skewCoord, Units.val_mk0, toAdd_ofAdd,
        map_mul, Subfield.coe_mul]
      rw [mul_assoc, hinv, hm]
      ring

omit [Fact p.Prime] in
theorem card_commutator_rootGroup :
    Nat.card (⁅rootGroup J hJ, rootGroup J hJ⁆ : Subgroup _) = p ^ f := by
  have h := (huppert_explicit J hJ (p ^ f) hK hfix).2.2.2.2.2.2.2.2.2.1
  rw [← Subgroup.map_subtype_commutator, Subgroup.card_map_of_injective
    (rootGroup J hJ).subtype_injective, h]

theorem exists_centerTorus_rootGroup (hf : 1 ≤ f) :
    ∃ ψ : Multiplicative (GaloisField p f) →* ProjectiveSpecialUnitaryMatrixGroup J,
      Function.Injective ψ ∧
      ψ.range = rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      ∀ μ : (GaloisField p f)ˣ, ∃ g ∈ Subgroup.normalizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
        ∀ a : Multiplicative (GaloisField p f), g * ψ a * g⁻¹ =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p f) * Multiplicative.toAdd a)) := by
  obtain ⟨ψ, hψ, hcen, htor⟩ := exists_centerTorus J hK hfix hf
  have hinj : Function.Injective ((root J hJ).comp ψ) := (root_injective J hJ).comp hψ
  refine ⟨(root J hJ).comp ψ, hinj, ?_, fun μ => ?_⟩
  · apply Subgroup.eq_of_le_of_card_ge (K := rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    · rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨root_mem_rootGroup J hJ _, ?_⟩
      rintro _ hw
      obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hw
      simp only [MonoidHom.comp_apply]
      rw [← map_mul, ← map_mul, hcen]
    · have hrange : Nat.card ((root J hJ).comp ψ).range =
          Nat.card (Multiplicative (GaloisField p f)) :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hq : Nat.card (Multiplicative (GaloisField p f)) = p ^ f := by
        rw [Nat.card_congr Multiplicative.toAdd]
        exact GaloisField.card p f (by omega)
      rw [← commutator_rootGroup J hJ hK hfix, card_commutator_rootGroup J hJ hK hfix, hrange, hq]
  · obtain ⟨k, hk⟩ := htor μ
    refine ⟨torus J hJ k, torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k),
      fun a => ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [torus_mul_root_mul_inv, hk]

end CenterTorus

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitarySylowCenterTorus : KFactUnitarySylowCenterTorus := by
  intro L _ _ p _ d hd h U
  obtain ⟨-, hf, -, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  obtain ⟨ψ, hψ, hrange, htor⟩ := UnitaryModel.exists_centerTorus_rootGroup J hJ hK hfix hf
  refine ⟨(e'.symm : _ →* L).comp ψ, e'.symm.injective.comp hψ, ?_, fun μ => ?_⟩
  · ext x
    have h1 : x ∈ ((e'.symm : _ →* L).comp ψ).range ↔ e' x ∈ ψ.range := by
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨c, by simp⟩
      · rintro ⟨c, hc⟩
        exact ⟨c, by simp [hc]⟩
    rw [h1, hrange, Subgroup.mem_inf, Subgroup.mem_inf, ← hU, UnitaryModel.mem_map_iff,
      UnitaryModel.mem_centralizer_map_iff]
  · obtain ⟨g, hg, hgψ⟩ := htor μ
    refine ⟨e'.symm g, ?_, fun a => ?_⟩
    · rw [← hN] at hg
      exact (UnitaryModel.mem_map_iff e' _ _).1 (by simpa using hg)
    · have := congrArg e'.symm (hgψ a)
      simpa using this

end CFSG.AGLEmbedding
