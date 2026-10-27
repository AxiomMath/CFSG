module

public import CFSG.HardMathSupport.Timmesfeld.DFour.T1bPlus
public import CFSG.HardMathSupport.Timmesfeld.DFour.TrialityFix
public import CFSG.HardMathSupport.Timmesfeld.DFour.CodimTwo
public import CFSG.HardMathSupport.Timmesfeld.DFour.FixDescent
public import CFSG.HardMathSupport.Timmesfeld.DFour.FixParity
public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank4
import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K]

@[expose] noncomputable def omegaToProj (K : Type) [Field K] :
    StatedOmega (StatedQuadPlus 4 K) →* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
  (matrixProjectiveProjection (coordinateQuadPlus 4 K)).comp
    (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).toMonoidHom

theorem omegaToProj_surjective : Function.Surjective (omegaToProj K) :=
  (matrixProjectiveProjection_surjective _).comp (MulEquiv.surjective _)

theorem sq_eq_one_of_omegaToProj (hQv : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    {x : StatedOmega (StatedQuadPlus 4 K)} (hx : omegaToProj K x = 1) : x ^ 2 = 1 := by
  set r := statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
    with hr
  have hmem : r x ∈ matrixDerivedScalars (coordinateQuadPlus 4 K) := by
    have hker : (matrixProjectiveProjection (coordinateQuadPlus 4 K)).ker =
        matrixDerivedScalars (coordinateQuadPlus 4 K) := QuotientGroup.ker_mk' _
    rw [← hker]
    exact hx
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff _ _).mp hmem
  have hiso : (r x).val ∈ matrixIsometries (coordinateQuadPlus 4 K) :=
    matrixDerived_le_isometries _ (r x).2
  rw [mem_matrixIsometries_iff] at hiso
  obtain ⟨v, hv⟩ := hQv
  have h1 := hiso v
  have hsm : matrixLinearEquiv (r x).val v = (c : K) • v := by
    rw [← hc]
    ext i
    simp [matrixLinearEquiv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal]
  rw [hsm, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hcc : (c : K) * (c : K) = 1 := by
    have h3 : ((c : K) * (c : K) - 1) * coordinateQuadPlus 4 K v = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hv)
  have hc2 : c * c = 1 := Units.ext (by rw [Units.val_mul, hcc, Units.val_one])
  apply r.injective
  rw [map_pow, map_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, pow_two, ← map_mul, hc2, map_one]
  rfl

variable [Finite K]

theorem exists_lift (hQv : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 81) :
    ∃ E : Subgroup (StatedOmega (StatedQuadPlus 4 K)), Nat.card E = 81 ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∀ x ∈ E, omegaToProj K x ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := omegaToProj K with hψ
  set Ã := A.comap ψ with hÃ
  have hsurj : Function.Surjective ((ψ.comp Ã.subtype).codRestrict A fun x => x.2) := by
    intro a
    obtain ⟨x, hx⟩ := omegaToProj_surjective (K := K) (a : matrixProjectiveDerived _)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change ψ x ∈ A
      rw [hψ, hx]
      exact a.2
    · apply Subtype.ext
      exact hx
  have hdvd : 3 ^ 4 ∣ Nat.card Ã := by
    have := Subgroup.card_dvd_of_surjective hsurj
    rw [hcard] at this
    exact this
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set E := H.map Ã.subtype with hE
  have hEcard : Nat.card E = 81 := by
    rw [hE, Subgroup.card_map_of_injective Ã.subtype_injective, hH]
    norm_num
  have hEA : ∀ x ∈ E, ψ x ∈ A := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h81 : ∀ x ∈ E, x ^ 81 = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
    rw [hEcard] at this
    exact congrArg Subtype.val this
  have hker : ∀ z ∈ E, ψ z = 1 → z = 1 := by
    intro z hz hψz
    have h2 := sq_eq_one_of_omegaToProj hQv hψz
    have h81z := h81 z hz
    have e : z = z ^ 81 * ((z ^ 2) ^ 40)⁻¹ := by group
    rw [e, h81z, h2, one_pow, inv_one, mul_one]
  refine ⟨E, hEcard, fun x hx => ?_, fun x hx y hy => ?_, hEA⟩
  · have h3 : ψ (x ^ 3) = 1 := by rw [map_pow]; exact hA.2 _ (hEA x hx)
    have h6 : x ^ 6 = 1 := by
      have := sq_eq_one_of_omegaToProj hQv h3
      rw [← pow_mul] at this
      exact this
    have e : x ^ 3 = x ^ 81 * ((x ^ 6) ^ 13)⁻¹ := by group
    rw [e, h81 x hx, h6, one_pow, inv_one, mul_one]
  · have hcomm : ψ x * ψ y = ψ y * ψ x :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hEA x hx⟩ ⟨_, hEA y hy⟩)
    have hz : ψ (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
    have hzE : x * y * (y * x)⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem hx hy) (E.inv_mem (E.mul_mem hy hx))
    exact mul_inv_eq_one.mp (hker _ hzE hz)

theorem card_le_27_of_triality (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hEA : projectivePointFamilyAut (coordinateQuadPlus 4 K) =
      matrixProjectiveImage (coordinateQuadPlus 4 K))
    (hQv : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    {t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (ht3 : t ^ 3 = 1)
    (htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : CFSG.Open.IsElemAbelian 3 A) (hfix : ∀ a ∈ A, t a = a) : Nat.card A ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  have hp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hA.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk4 : 4 ≤ k := by
    by_contra h
    push Not at h
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (G := A)
    (by rw [hk]; exact Nat.pow_dvd_pow 3 hk4)
  set A' := A₀.map A.subtype with hA'
  have hA'A : A' ≤ A := Subgroup.map_subtype_le _
  have hA'card : Nat.card A' = 81 := by
    rw [hA', Subgroup.card_map_of_injective A.subtype_injective, hA₀]
    norm_num
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA'el : CFSG.Open.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommA _ (hA'A a.2) _ (hA'A b.2))⟩⟩,
      fun x hx => hA.2 x (hA'A hx)⟩
  obtain ⟨E, hEcard, hE3, hEcomm, hEA'⟩ := exists_lift hQv A' hA'el hA'card
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩
  have : Finite E := inferInstance
  set ρ : E →* Module.End K (Fin 4 ⊕ Fin 4 → K) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom.comp
        ((StatedOmega (StatedQuadPlus 4 K)).subtype.comp E.subtype)) with hρ
  have hρapp : ∀ x : E, ρ x = (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := fun x => rfl
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    rw [hρapp, hρapp] at hxy
    exact Subtype.ext (Subtype.ext ((toLinEquiv (Fin 4 ⊕ Fin 4) K).injective
      (LinearEquiv.toLinearMap_injective hxy)))
  have hO : ∀ x : E, toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := fun x => by
    rw [← CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv_val 4 K
      (by norm_num) x.1]
    exact orthElementaryGroup_le _
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv 4 K
        (by norm_num) x.1).property
  have hcube : ∀ x : E, ∀ v, toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1
      (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 v)) = v := by
    intro x v
    have h := hE3 x.1 x.2
    have h' : (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1) ^ 3 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, h, OneMemClass.coe_one, map_one]
    have := congrArg (fun g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => g v) h'
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have heven : ∀ x : E, Even (finrank K (LinearMap.ker (ρ x - 1))) := fun x =>
    even_finrank_ker_sub_one h2 h3 (hO x) (hcube x)
  obtain ⟨x, hx1, hx6⟩ := exists_fixDim_six h3 finrank_V8 ρ hρinj
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, hE3 x.1 x.2, OneMemClass.coe_one]))
    (by rw [hEcard]) heven
  have heq := card_maximal_eq_two_mul_card_lines hEA ht3 htE x.1 (hfix _ (hA'A (hEA' _ x.2)))
  exact card_maximal_ne_two_mul_card_lines h2 h3 (hO x) (hcube x) hx6 heq

theorem pRank_mulAut_le_of_trialityBound27 {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q ≠ 0) (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hidx : (matrixProjectiveImage Q).index ≤ 3)
    (hcen : Subgroup.center (matrixProjectiveDerived Q) = ⊥)
    (hKL : ∀ t : MulAut (matrixProjectiveDerived Q), t ^ 3 = 1 → t ∉ matrixProjectiveImage Q →
      ∀ A : Subgroup (matrixProjectiveDerived Q), CFSG.Open.IsElemAbelian 3 A →
        (∀ a ∈ A, t a = a) → Nat.card A ≤ 27)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived Q))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (matrixProjectiveDerived Q))) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived Q)) + 1 := by
  have hQv :=
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ
  obtain ⟨g, hgE, hg⟩ := exists_gen_image Q
  have hbound : ∀ X : Subgroup (MulAut (matrixProjectiveDerived Q)),
      CFSG.Open.IsElemAbelian 3 X →
      Nat.card (matrixProjectiveImage Q ⊓ X : Subgroup _) ≤
          3 * Nat.card (X ⊓ Inn (matrixProjectiveDerived Q) : Subgroup _) ∧
        Nat.card X ≤ 3 * 3 * Nat.card (X ⊓ Inn (matrixProjectiveDerived Q) : Subgroup _) :=
    fun X hX => card_le_of_tower Nat.prime_three le_rfl (linearRange_normal Q) hidx g hgE hg
      (fun δ hδ hδp => mem_inner_of_mem_linearRange Q hQv hab Nat.prime_three (by norm_num) hδ
        hδp) hX.2
  refine pRank_mulAut_le_of_card_bounds Nat.prime_three hcen (matrixProjectiveImage Q) 4
    (fun X hX hXE => ?_) (fun X hX hXE => ?_) h4
  · have h1 := (hbound X hX).1
    rwa [inf_of_le_right hXE] at h1
  · obtain ⟨t, htX, htE⟩ := Set.not_subset.mp hXE
    obtain ⟨A, hA, hfix, hcardA⟩ := exists_fixed_of_mem hcen hX htX
    have h27 := hKL t (hX.2 t htX) htE A hA hfix
    have h2 := (hbound X hX).2
    rw [← hcardA] at h2
    calc Nat.card X ≤ 3 * 3 * Nat.card A := h2
      _ ≤ 3 * 3 * 27 := Nat.mul_le_mul_left _ h27
      _ = 3 ^ (4 + 1) := by norm_num

theorem dFourCrossThreeDvd_holds : DFourCrossThreeDvd := by
  intro S _ _ r f hm hcen hr2 hr3 _
  have h0 := hm
  obtain ⟨⟨hr, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  have : CharP K r := ringChar.of_eq (coordinate_model_witness_plus hm K hK e).1
  obtain ⟨c2, c4⟩ := CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.char_facts (K := K) hr hr2
    hr3
  have h2K : (2 : K) ≠ 0 := c2
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have : r ∣ 3 := (CharP.cast_eq_zero_iff K r 3).1 (by exact_mod_cast h)
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)
  set φ := coordinatePlusWitnessEquiv K e with hφ
  have hcen' := center_eq_bot_of_mulEquiv φ hcen
  have hEA := coordinate_plus_family_eq_matrixImage hm K hK e
  have hQv :=
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value
      _ hQ
  have h4 : 4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
    have h := four_le_pRank_plus_of_char (K := K) (n := 4) le_rfl c2 c4
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at h
  have key := pRank_mulAut_le_of_trialityBound27 hQ hab hidx hcen'
    (fun t ht3 htE A hA hfix => card_le_27_of_triality h2K h3K hEA hQv ht3 htE A hA hfix) h4
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr φ),
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]

end CFSG.HardMathSupport.Timmesfeld.DFour
