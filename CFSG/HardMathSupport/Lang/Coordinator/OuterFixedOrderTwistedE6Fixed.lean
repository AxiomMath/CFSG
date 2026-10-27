module

public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false

theorem exists_subfield_card_of_card_eq {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : 1 ≤ p)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ (2 * (d * p))) :
    ∃ S : Subfield K, Nat.card S = ℓ ^ (2 * d) := by
  have h2dp : 1 ≤ 2 * (d * p) := by have := Nat.mul_pos hd hp; omega
  obtain ⟨fr, -, hord, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ h2dp hK
  obtain ⟨hAc, S, -, hS⟩ := hA (Subgroup.zpowers (fr ^ (2 * d)))
  have hdvd : 2 * d ∣ orderOf fr := by
    rw [hord]
    exact ⟨p, by ring⟩
  have hordpow : orderOf (fr ^ (2 * d)) = p := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, show 2 * (d * p) = 2 * d * p by ring,
      Nat.mul_div_cancel_left _ (by omega)]
  rw [Nat.card_zpowers, hordpow] at hS
  refine ⟨S, ?_⟩
  rw [hS, show 2 * (d * p) = 2 * d * p by ring, Nat.mul_div_cancel _ (by omega)]

theorem card_fixedSubgroup_fieldActor_dvd {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : 1 ≤ p)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * (d * p))) (σ ε : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p)) (hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) :
    Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) ∣
      lieOrderNumerator .twistedE6 0 (ℓ ^ d) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2dp : 1 ≤ 2 * (d * p) := by have := Nat.mul_pos hd hp; omega
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ h2dp hK
  obtain ⟨S, hS⟩ := exists_subfield_card_of_card_eq hℓ hd hp K hK
  have hS2 : Nat.card S = (ℓ ^ d) ^ 2 := by rw [hS, ← pow_mul, mul_comm]
  have : Finite S := Subtype.finite
  have : CharP S ℓ := inferInstance
  set Ω := AlgebraicClosure S with hΩ
  have : IsAlgClosed Ω := AlgebraicClosure.isAlgClosed S
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap S Ω).injective ℓ
  have : Algebra.IsAlgebraic S K := Algebra.IsAlgebraic.of_finite S K
  let ι : K →+* Ω := (IsAlgClosed.lift (M := Ω) (R := S) (S := K) : K →ₐ[S] Ω).toRingHom
  have hι : Function.Injective ι := ι.injective
  let Fr : Ω →+* Ω := iterateFrobenius Ω ℓ d
  have hFr : ∀ c, Fr c = c ^ ℓ ^ d := fun c => rfl
  let T : K →+* K := iterateFrobenius K ℓ d
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => rfl
  let σ₀ : S →+* S := iterateFrobenius S ℓ d
  have hσ₀ : ∀ c, σ₀ c = c ^ ℓ ^ d := fun c => rfl
  have hcomm : ι.comp T = Fr.comp ι := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hT, hFr, map_pow]
  obtain ⟨-, -, -, -, -, hRcard, -⟩ := twisted_E6_full_rational_fixed_group_order hℓ hd S hS2 σ₀
    hσ₀ Ω Fr hFr
  have hKcard : ∀ c : K, c ^ ℓ ^ (2 * (d * p)) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hTσε : T = σ.toRingHom.comp ε.toRingHom := RingHom.ext fun c => by
    change c ^ ℓ ^ d = σ (ε c)
    rw [hε, hσ, ← pow_mul, ← pow_add]
    rw [show d * (p + 1) + d * p = 2 * (d * p) + d by ring, pow_add, pow_mul, hKcard]
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set H : Subgroup (ModGL TwistTag.E6.tag K) :=
    (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)).map C.subtype with hH
  have hHle : H.map (baseChangeGL ι) ≤ twistedFixedGroup TwistTag.E6 Ω Fr := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxC : (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
      graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2
    have hfixε : Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x := by
      have h1 : fieldActor σ ε x = x := hx
      exact congrArg Subtype.val h1
    have hfixT : twistHom TwistTag.E6 K T (x : ModGL TwistTag.E6.tag K) = x := by
      have hσx := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1 hxC).2
      rw [twistHom_apply, hTσε, ← units_map_entrywiseHom_comp, hfixε]
      rw [twistHom_apply] at hσx
      exact hσx
    have hadj := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1 hxC).1
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 Ω Fr).2
      ⟨(adjointBaseChangeHom TwistTag.E6.tag ι ⟨_, hadj⟩).2, ?_⟩
    rw [Subgroup.coe_subtype, twistHom_baseChangeGL ι hcomm, hfixT]
  have hcardH : Nat.card H = Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hcardHΩ : Nat.card (H.map (baseChangeGL ι)) = Nat.card H :=
    Subgroup.card_map_of_injective (baseChangeGL_injective ι)
  rw [← hcardH, ← hcardHΩ]
  have h := Subgroup.card_dvd_of_le hHle
  rwa [hRcard] at h

end CFSG.HardMathSupport.Lang.Coordinator
