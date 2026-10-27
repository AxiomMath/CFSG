module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.AdditiveTransfer
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent
public import CFSG.LieType.Universal.Unitary.CurtisDatum
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.GuralnickMalle
open scoped MonoidAlgebra TensorProduct

theorem exists_simple_su_model_of_scalar_core_data {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {m f : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (φ : ↥(CFSG.Open.StatedSU m (2 ^ f) K) →* ↥L) (hφs : Function.Surjective φ)
    (hφk : φ.ker ≤
      (CFSG.Open.StatedScalars (Fin m) K).subgroupOf (CFSG.Open.StatedSU m (2 ^ f) K))
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hA1 : A ≠ ⊥)
    (hAel : CFSG.Quasithin.IsElemAbelian2 A) (hAq : CFSG.Quasithin.IsQuadratic A)
    (hAV : Nat.card V ≤ 2 * Nat.card A * Nat.card (CFSG.Quasithin.fixV A))
    (ζ : traceZero (unitaryInvolution K 2 f)) (hζ : (ζ : K) ≠ 0) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k 2) (_φ₀ : K →+* k)
      (M : Type) (_ : AddCommGroup M) (_ : Module k M) (_ : FiniteDimensional k M)
      (τ : Representation k (SU (unitaryInvolution K 2 f) m) M) (s : ℕ)
      (P : Subgroup (SU (unitaryInvolution K 2 f) m)),
      IsSimpleRep τ ∧ 0 < s ∧
      (∀ g, τ g = 1 ↔ φ (suToStated hK m g) = 1) ∧
      P ≠ ⊥ ∧ CFSG.Open.IsElemAbelian 2 P ∧
      (∀ a ∈ P, ∀ b ∈ P, (τ a - 1) * (τ b - 1) = 0) ∧
      2 ^ (s * (finrank k M - finrank k (fixSubGen τ P))) ≤ 2 * Nat.card P ∧
      (∃ (y : M) (χ : SU (unitaryInvolution K 2 f) m → k) (μ : Fin (m / 2) → k),
        (curtisDatum hK m hm ζ hζ).IsCurtisType τ y χ μ) ∧
      ∀ (y : M) (χ : SU (unitaryInvolution K 2 f) m → k) (μ : Fin (m / 2) → k),
        (curtisDatum hK m hm ζ hζ).IsCurtisType τ y χ μ →
          ∀ h ∈ (curtisDatum hK m hm ζ hζ).H, χ h ^ 2 ^ s = χ h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWadd, hWmod, hWfin, ρ, hirrρ, hkerρ, P₀, hP₀1, hP₀el, hquadρ, hineqρ⟩ :=
    exists_additive_of_scalar_core_data hV hirr hK φ hφs hφk hAL hA1 hAel hAq hAV
  let : AddCommGroup W := hWadd
  let : Module (ZMod 2) W := hWmod
  let : Finite W := hWfin
  let e : SU (unitaryInvolution K 2 f) m ≃* CFSG.Open.StatedSU m (2 ^ f) K :=
    suToStated hK m
  let ρ' : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W :=
    ρ.comp e.toMonoidHom
  have : ρ'.IsIrreducible := isIrreducible_comp_mulEquiv ρ e
  let P : Subgroup (SU (unitaryInvolution K 2 f) m) := P₀.comap e.toMonoidHom
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hmap : P.map e.toMonoidHom = P₀ :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective P₀
    have hP₀bot : P₀ = ⊥ := by
      rw [← hmap, hbot, Subgroup.map_bot]
    exact hP₀1 hP₀bot
  have hPel : CFSG.Open.IsElemAbelian 2 P := hP₀el.comap e.injective
  have hquad' : ∀ a ∈ P, ∀ b ∈ P, (ρ' a - 1) * (ρ' b - 1) = 0 := by
    intro a ha b hb
    exact hquadρ (e a) ha (e b) hb
  have hineq' : Nat.card W ≤ 2 * weight1Gen ρ' P := by
    change Nat.card W ≤ 2 * weight1Gen (ρ.comp e.toMonoidHom) (P₀.comap e.toMonoidHom)
    rw [weight1Gen_comp_mulEquiv ρ e P₀]
    exact hineqρ
  let R : Type := End (ZMod 2)[SU (unitaryInvolution K 2 f) m] ρ'.asModule
  let : Field R := endField_field ρ'
  let : Finite R := endField_finite ρ'
  have : CharP R 2 := endField_charP ρ' 2
  let : Module.Finite R ρ'.asModule :=
    Module.finite_iff_finite.mpr (finite_asModule ρ')
  obtain ⟨s, hs, hRcard⟩ := exists_card_endField_eq_two_pow (ρ := ρ')
  let k : Type := AlgebraicClosure R
  let : Field k := inferInstance
  let : CharP k 2 := inferInstance
  obtain ⟨φ₀⟩ := nonempty_ringHom_algebraicClosure (K := R) (F₀ := K) (p := 2)
  let : Algebra K k := φ₀.toAlgebra
  let M : Type := k ⊗[R] ρ'.asModule
  let : FiniteDimensional k M := Module.Finite.base_change R k ρ'.asModule
  let τ : Representation k (SU (unitaryInvolution K 2 f) m) M :=
    Theory.Representation.extendScalars k (endFieldRep ρ')
  have hsimple : IsSimpleRep τ := by
    change IsSimpleRep (Theory.Representation.extendScalars k (endFieldRep ρ'))
    exact isSimpleRep_extendScalars_endFieldRep (ρ := ρ') (k := k)
  have hkerτ : ∀ g, τ g = 1 ↔ φ (suToStated hK m g) = 1 := by
    intro g
    exact (extendScalars_endFieldRep_eq_one_iff (ρ := ρ') (k := k) g).trans
      (hkerρ (e g))
  have hquadτ : ∀ a ∈ P, ∀ b ∈ P, (τ a - 1) * (τ b - 1) = 0 := by
    intro a ha b hb
    exact extendScalars_endFieldRep_sub_one_mul_sub_one (ρ := ρ') (k := k)
      (a := a) (b := b) (hquad' a ha b hb)
  have hineqτ : 2 ^ (s * (finrank k M - finrank k (fixSubGen τ P))) ≤
      2 * Nat.card P := by
    have h := pow_codim_le_of_card_le (ρ := ρ') (k := k) P (c := 2) hineq'
    rw [hRcard] at h
    rw [← pow_mul] at h
    simpa [M, τ] using h
  let D := curtisDatum hK m hm ζ hζ
  have hsplit : SplitOver k D.H := curtisDatum_splitOver hK m hm ζ hζ k
  have : Finite (coxeterMatrix (isFiniteType_cartan m)).Group :=
    finite_group (isFiniteType_cartan m)
  have htype : ∃ (y : M) (χ : SU (unitaryInvolution K 2 f) m → k)
      (μ : Fin (m / 2) → k), D.IsCurtisType τ y χ μ :=
    D.exists_isCurtisType hsplit hsimple
  refine ⟨k, inferInstance, inferInstance, φ₀, M, inferInstance, inferInstance,
    inferInstance, τ, s, P, hsimple, hs, hkerτ, hP1, hPel, hquadτ, hineqτ, htype, ?_⟩
  intro y χ μ ht h hh
  have h1 := isCurtisType_chi_pow_card (ρ := ρ') (D := D) (k := k) ht hh
  rw [hRcard] at h1
  exact h1

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
