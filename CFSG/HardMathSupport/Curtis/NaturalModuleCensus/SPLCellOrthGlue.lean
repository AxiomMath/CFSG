module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFam
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellBig
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel

public section

open Matrix Module Polynomial CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
open scoped IsMulCommutative
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.RankThree.Classical.SteinbergBY (OrthogonalGates)
open CFSG.RankThree.PartOne.AUTSL (derivedProjEquiv exists_ne_zero_of_polar_nondegenerate)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

open CFSG.HardMathSupport.Curtis

section Group

variable {G : Type} [Group G]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx' : ∀ z, x * z * x⁻¹ = z := fun z => by
    have := congrArg (fun a : MulAut G => a z) (MonoidHom.mem_ker.1 hx)
    simpa [MulAut.conj_apply] using this
  have : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := hx' z
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [h] at this
  exact this

theorem fixes_of_comm_conj (h : Subgroup.center G = ⊥) (γ : MulAut G) (y : G)
    (hcomm : γ * MulAut.conj y = MulAut.conj y * γ) : γ y = y := by
  apply conj_injective_of_center_eq_bot h
  ext z
  have h1 := congrArg (fun a : MulAut G => a (γ.symm z)) hcomm
  simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
  have h2 : γ (y * γ.symm z * y⁻¹) = γ y * z * (γ y)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp only [MulAut.conj_apply]
  rw [← h2]
  simpa using h1

variable [Finite G]

@[expose] noncomputable def restrictAut (γ : MulAut G) (E : Subgroup G) (hγE : ∀ y ∈ E, γ y ∈ E) :
    MulAut ↥E :=
  have hmap : E.map (γ : G →* G) = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hγE y hy
    · rw [Subgroup.card_map_of_injective γ.injective]
  (γ.subgroupMap E).trans (MulEquiv.subgroupCongr hmap)

theorem restrictAut_apply (γ : MulAut G) (E : Subgroup G) (hγE : ∀ y ∈ E, γ y ∈ E) (e : ↥E) :
    ((restrictAut γ E hγE e : ↥E) : G) = γ e := rfl

theorem restrictAut_pow_apply (γ : MulAut G) (E : Subgroup G) (hγE : ∀ y ∈ E, γ y ∈ E) (m : ℕ)
    (e : ↥E) : (((restrictAut γ E hγE ^ m) e : ↥E) : G) = (γ ^ m) e := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih, restrictAut_apply]

theorem restrictAut_pow_eq_one (γ : MulAut G) (E : Subgroup G) (hγE : ∀ y ∈ E, γ y ∈ E) (m : ℕ)
    (h : γ ^ m = 1) : restrictAut γ E hγE ^ m = 1 :=
  MulEquiv.ext fun e => Subtype.ext (by rw [restrictAut_pow_apply, h]; rfl)

end Group

section Rep

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def matrixLin (d : ℕ) (K : Type) [Field K] :
    GL (Fin d) K →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) where
  toFun := matrixLinearEquiv
  map_one' := LinearEquiv.ext fun v => by
    rw [matrixLinearEquiv_apply]
    simp
  map_mul' := matrixLinearEquiv_mul

theorem matrixLin_apply (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLin d K A v = (A : Matrix (Fin d) (Fin d) K) *ᵥ v := rfl

theorem matrixLin_injective : Function.Injective (matrixLin d K) := by
  intro A B h
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ : (Fin d → K) ≃ₗ[K] (Fin d → K) => φ v) h
  simpa [matrixLin_apply] using this

variable (Q : QuadraticForm K (Fin d → K)) [CharP K 2] (hQ : ∃ v, Q v ≠ 0)

@[expose] noncomputable def omegaRep : matrixProjectiveDerived Q →* GL (Fin d) K :=
  (matrixDerived Q).subtype.comp (derivedProjEquiv Q hQ).symm.toMonoidHom

@[expose] noncomputable def omegaMat (e : matrixProjectiveDerived Q) : Matrix (Fin d) (Fin d) K :=
  ((omegaRep Q hQ e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)

@[expose] noncomputable def omegaLin :
    matrixProjectiveDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (matrixLin d K).comp (omegaRep Q hQ)

theorem omegaLin_apply (e : matrixProjectiveDerived Q) (v : Fin d → K) :
    omegaLin Q hQ e v = omegaMat Q hQ e *ᵥ v := rfl

theorem omegaRep_injective : Function.Injective (omegaRep Q hQ) :=
  Subtype.val_injective.comp (derivedProjEquiv Q hQ).symm.injective

theorem omegaLin_injective : Function.Injective (omegaLin Q hQ) :=
  matrixLin_injective.comp (omegaRep_injective Q hQ)

theorem omegaRep_proj (A : matrixDerived Q) :
    omegaRep Q hQ (matrixProjectiveProjection Q A) = A.val := by
  change (((derivedProjEquiv Q hQ).symm (derivedProjEquiv Q hQ A) : matrixDerived Q) :
    GL (Fin d) K) = A.val
  rw [MulEquiv.symm_apply_apply]

theorem omegaRep_mem_isometries (e : matrixProjectiveDerived Q) :
    omegaRep Q hQ e ∈ matrixIsometries Q :=
  matrixDerived_le_isometries Q ((derivedProjEquiv Q hQ).symm e).2

theorem omegaRep_conj (g : similarityPairs Q) (e : matrixProjectiveDerived Q) :
    omegaRep Q hQ (matrixProjectiveConjugationHom Q g e) =
      g.val.left * glFieldAut (Fin d) K g.val.right (omegaRep Q hQ e) * g.val.left⁻¹ := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q e
  change omegaRep Q hQ (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A)) = _
  rw [matrixProjectiveConjugation_mk, omegaRep_proj, omegaRep_proj, matrixDerivedConjugation_val]

theorem omegaMat_conj (g : similarityPairs Q) (e : matrixProjectiveDerived Q) :
    omegaMat Q hQ (matrixProjectiveConjugationHom Q g e) =
      (g.val.left : Matrix (Fin d) (Fin d) K) * (omegaMat Q hQ e).map g.val.right *
        ((g.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h := congrArg (fun A : GL (Fin d) K => (A : Matrix (Fin d) (Fin d) K))
    (omegaRep_conj Q hQ g e)
  simp only [Units.val_mul] at h
  exact h

theorem semiMap_omegaLin (g : similarityPairs Q) (e : matrixProjectiveDerived Q) (v : Fin d → K) :
    Coordinator.SPLCell.semiMap g.val.left g.val.right (omegaLin Q hQ e v) =
      omegaLin Q hQ (matrixProjectiveConjugationHom Q g e)
        (Coordinator.SPLCell.semiMap g.val.left g.val.right v) := by
  rw [omegaLin_apply, omegaLin_apply, Coordinator.SPLCell.semiMap_mulVec, omegaMat_conj]

theorem semiMap_comm_of_fixed (g : similarityPairs Q) (y : matrixProjectiveDerived Q)
    (hy : matrixProjectiveConjugationHom Q g y = y) (v : Fin d → K) :
    Coordinator.SPLCell.semiMap g.val.left g.val.right (omegaMat Q hQ y *ᵥ v) =
      omegaMat Q hQ y *ᵥ Coordinator.SPLCell.semiMap g.val.left g.val.right v := by
  have h := semiMap_omegaLin Q hQ g y v
  rw [hy] at h
  exact h

omit [CharP K 2] in
theorem right_pow_eq_one_of_gates {f : ℕ} (hg : OrthogonalGates Q f) (g : similarityPairs Q)
    (N : ℕ) (h : matrixProjectiveConjugationHom Q g ^ N = 1) : g.val.right ^ N = 1 := by
  have h1 : matrixProjectiveConjugationHom Q (g ^ N) = 1 := by rw [map_pow]; exact h
  have h2 := (hg.1 (g ^ N)).1 h1
  have h3 : (g ^ N).val.right = g.val.right ^ N :=
    map_pow (SemidirectProduct.rightHom : coordinateSemilinearGroup d K →* (K ≃+* K)) g.val N
  rw [← h3]
  exact h2.1

end Rep

section Data

variable {K : Type} [Field K] [Finite K] {n : ℕ}

structure OrthCellData (Q : QuadraticForm K (Fin (2 * n) → K)) (f : ℕ) : Prop where
  card_eq : Nat.card K = 2 ^ f
  one_le_f : 1 ≤ f
  four_le_n : 4 ≤ n
  nondegenerate : (QuadraticMap.polarBilin Q).Nondegenerate
  totally_singular : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  gates : OrthogonalGates Q f
  top_of_five_le : 5 ≤ n → matrixProjectiveImage Q = ⊤

namespace OrthCellData

variable {Q : QuadraticForm K (Fin (2 * n) → K)} {f : ℕ} (h : OrthCellData Q f)
include h

theorem charP_two : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, h.card_eq])

omit [Finite K] in
theorem pos_dim : 0 < 2 * n := by have := h.four_le_n; omega

omit [Finite K] in
theorem exists_ne_zero : ∃ v, Q v ≠ 0 :=
  exists_ne_zero_of_polar_nondegenerate h.pos_dim Q h.nondegenerate

theorem simple_nonabelian : IsSimpleGroup (matrixProjectiveDerived Q) ∧
    ∃ a b : matrixProjectiveDerived Q, a * b ≠ b * a :=
  CFSG.RankThree.PartOne.KCOrthogonalSubfield.matrix_simple_nonabelian h.pos_dim h.nondegenerate
    h.totally_singular

theorem center_eq_bot : Subgroup.center (matrixProjectiveDerived Q) = ⊥ :=
  CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot h.pos_dim h.nondegenerate
    h.totally_singular

theorem conj_injective :
    Function.Injective (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) :=
  conj_injective_of_center_eq_bot h.center_eq_bot

omit [Finite K] in
theorem mem_E_of_five_le (hn : 5 ≤ n) (β : MulAut (matrixProjectiveDerived Q)) :
    β ∈ matrixProjectiveImage Q := by
  rw [h.top_of_five_le hn]
  exact Subgroup.mem_top _

omit [Finite K] in
theorem mem_E_of_prime_power {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    {γ : MulAut (matrixProjectiveDerived Q)} {k : ℕ} (hγ : γ ^ r ^ k = 1) :
    γ ∈ matrixProjectiveImage Q := by
  have hpg : IsPGroup r (Subgroup.zpowers γ) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hm, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm m,
      _root_.zpow_mul, _root_.zpow_natCast, hγ, _root_.one_zpow]
    rfl
  have hK0 := h.gates.2.2.2.2.2.2.1 r hr hr3 _ hpg
  have h1 : γ ∈ CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointFamilyAut Q :=
    h.gates.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers γ))
  rw [h.gates.2.2.2.2.2.1] at h1
  exact h1

omit [Finite K] in
theorem exists_pair_of_prime_power {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    {γ : MulAut (matrixProjectiveDerived Q)} {k : ℕ} (hγ : γ ^ r ^ k = 1) :
    ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = γ ∧ g.val.right ^ r ^ k = 1 := by
  obtain ⟨g, hg⟩ := h.mem_E_of_prime_power hr hr3 hγ
  exact ⟨g, hg, right_pow_eq_one_of_gates Q h.gates g _ (by rw [hg]; exact hγ)⟩

theorem zeta_cases (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : MulAut (matrixProjectiveDerived Q)} (hζ : ζ ^ p = 1) :
    (∃ y : matrixProjectiveDerived Q, MulAut.conj y = ζ ∧ y ^ p = 1) ∨
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = ζ ∧ orderOf g.val.right = p ∧
        ζ ∉ (linearConjugationHom Q).range := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hD : ζ ∈ (linearConjugationHom Q).range
  · left
    obtain ⟨-, k, hk⟩ := h.gates.2.2.1
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived Q)).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hin : ζ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived Q) :=
      CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2
        hD hζ
    obtain ⟨y, rfl⟩ := hin
    refine ⟨y, rfl, h.conj_injective ?_⟩
    rw [map_pow, hζ, map_one]
  · right
    obtain ⟨ψ, hψ, hker, -⟩ := h.gates.2.1
    have hζE := h.mem_E_of_five_le hn ζ
    obtain ⟨g, hgζ⟩ := hζE
    refine ⟨g, hgζ, ?_, hD⟩
    have hψg : ψ ⟨ζ, ⟨g, hgζ⟩⟩ = g.val.right := by
      have := hψ g
      rw [← this]
      congr 1
      exact Subtype.ext hgζ.symm
    have hpow : g.val.right ^ p = 1 := by
      rw [← hψg, ← map_pow]
      have : (⟨ζ, ⟨g, hgζ⟩⟩ : matrixProjectiveImage Q) ^ p = 1 := Subtype.ext (by simpa using hζ)
      rw [this, map_one]
    have hne : g.val.right ≠ 1 := by
      intro h1
      apply hD
      have hmem : (⟨ζ, ⟨g, hgζ⟩⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hψg, h1]
      rw [hker, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    exact orderOf_eq_prime hpow hne

end OrthCellData

end Data

section Action

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
  (hQ : ∃ v, Q v ≠ 0)

theorem exists_action_data {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Ē : Subgroup (matrixProjectiveDerived Q)) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (y : matrixProjectiveDerived Q) (hyp : y ^ p = 1)
    (hyE : ∀ e ∈ Ē, y * e * y⁻¹ = e) (g : similarityPairs Q) (k : ℕ)
    (hγ : matrixProjectiveConjugationHom Q g ^ r ^ k = 1)
    (hγE : ∀ e ∈ Ē, matrixProjectiveConjugationHom Q g e ∈ Ē)
    (hfix : matrixProjectiveConjugationHom Q g y = y)
    (hnt : ∃ e ∈ Ē, matrixProjectiveConjugationHom Q g e ≠ e) :
    (p : K) ≠ 0 ∧ (∀ e : ↥Ē, e ^ p = 1) ∧
    (∀ [Fintype ↥Ē], ((Fintype.card ↥Ē : ℕ) : K) ≠ 0) ∧
    ∃ (ρ : ↥Ē →* ((Fin d → K) ≃ₗ[K] (Fin d → K))) (z : Module.End K (Fin d → K))
      (γ' : MulAut ↥Ē) (g₀ : ↥Ē),
      Function.Injective ρ ∧ z = ((omegaLin Q hQ y : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        Module.End K (Fin d → K)) ∧
      (∀ e : ↥Ē, Commute z ((ρ e : (Fin d → K) ≃ₗ[K] (Fin d → K)) : Module.End K (Fin d → K))) ∧
      z ^ p = 1 ∧ (∀ e : ↥Ē, ((γ' e : ↥Ē) : matrixProjectiveDerived Q) =
        matrixProjectiveConjugationHom Q g e) ∧ γ' ^ r ^ k = 1 ∧ γ' g₀ ≠ g₀ ∧
      (∀ (e : ↥Ē) (v : Fin d → K),
        Coordinator.SPLCell.semiMap g.val.left g.val.right (ρ e v) =
          ρ (γ' e) (Coordinator.SPLCell.semiMap g.val.left g.val.right v)) ∧
      (∀ v, Coordinator.SPLCell.semiMap g.val.left g.val.right (z v) =
        z (Coordinator.SPLCell.semiMap g.val.left g.val.right v)) := by
  classical
  have : IsMulCommutative ↥Ē := hE.1
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  refine ⟨hpK, fun e => Subtype.ext (hE.2 e e.2), ?_, ?_⟩
  · intro _
    rw [← Nat.card_eq_fintype_card, hcard]
    push_cast
    exact pow_ne_zero _ hpK
  let ρ : ↥Ē →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) := (omegaLin Q hQ).comp Ē.subtype
  let z : Module.End K (Fin d → K) := ((omegaLin Q hQ y : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    Module.End K (Fin d → K))
  have hz_apply : ∀ v, z v = omegaLin Q hQ y v := fun v => rfl
  have hcommz : ∀ e : ↥Ē, Commute z ((ρ e : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
      Module.End K (Fin d → K)) := by
    intro e
    have hye : y * (e : matrixProjectiveDerived Q) = (e : matrixProjectiveDerived Q) * y := by
      have := hyE e e.2
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    refine LinearMap.ext fun v => ?_
    change z (ρ e v) = ρ e (z v)
    have h1 := congrArg (fun a : matrixProjectiveDerived Q => omegaLin Q hQ a v) hye
    simpa [hz_apply, ρ] using h1
  have hzpow : ∀ (m : ℕ) (v : Fin d → K), (z ^ m) v = (omegaLin Q hQ y ^ m) v := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, LinearEquiv.mul_apply, ih]
      rfl
  have hzp : z ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    rw [hzpow, ← map_pow, hyp, map_one]
    rfl
  obtain ⟨e0, he0, hne⟩ := hnt
  refine ⟨ρ, z, restrictAut (matrixProjectiveConjugationHom Q g) Ē hγE, ⟨e0, he0⟩,
    (omegaLin_injective Q hQ).comp Subtype.val_injective, rfl, hcommz, hzp, fun e => rfl,
    restrictAut_pow_eq_one _ _ _ _ hγ, fun h => hne (congrArg Subtype.val h), ?_, ?_⟩
  · intro e v
    exact semiMap_omegaLin Q hQ g e v
  · intro v
    rw [hz_apply, hz_apply, omegaLin_apply, omegaLin_apply]
    exact semiMap_comm_of_fixed Q hQ g y hfix v

theorem exists_big_primary_factor_of_pair {f : ℕ} (hK : Nat.card K = 2 ^ f) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (Ē : Subgroup (matrixProjectiveDerived Q)) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (y : matrixProjectiveDerived Q) (hyp : y ^ p = 1)
    (hyE : ∀ e ∈ Ē, y * e * y⁻¹ = e) (g : similarityPairs Q) (k : ℕ)
    (hγ : matrixProjectiveConjugationHom Q g ^ r ^ k = 1) (hσ : g.val.right ^ r ^ k = 1)
    (hγE : ∀ e ∈ Ē, matrixProjectiveConjugationHom Q g e ∈ Ē)
    (hfix : matrixProjectiveConjugationHom Q g y = y)
    (hnt : ∃ e ∈ Ē, matrixProjectiveConjugationHom Q g e ≠ e) :
    ∃ h : K[X], h ∈ primaryFactors ((omegaLin Q hQ y : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        Module.End K (Fin d → K)) ∧ Irreducible h ∧
      5 ≤ primaryMultiplicity ((omegaLin Q hQ y : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        Module.End K (Fin d → K)) h := by
  classical
  have : IsMulCommutative ↥Ē := hE.1
  have : Fintype ↥Ē := Fintype.ofFinite _
  obtain ⟨-, hGp, hGK, ρ, z, γ', g₀, hρinj, hz, hcommz, hzp, -, hγ', hg0, hfρ, hfz⟩ :=
    exists_action_data Q hQ hp hp2 Ē hE hcard y hyp hyE g k hγ hγE hfix hnt
  subst hz
  obtain ⟨h, hmem, hirr, hmult⟩ := Coordinator.SPLCell.exists_big_primary_factor hK hp hp2 hr hr5 hrp
    hGp hGK ρ hρinj _ hcommz hzp γ' hγ' g₀ hg0 g.val.right hσ
    (Coordinator.SPLCell.semiMap g.val.left g.val.right)
    (Coordinator.SPLCell.semiMap_bijective _ _) hfρ hfz
  exact ⟨h, hmem, hirr, hmult⟩

end Action

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus coordinate_model_witness_plus coordinate_model_witness_minus
    coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv)

theorem orthCellData_plus {S : Type} [Group S] {n f : ℕ}
    (hmodel : StatedClassicalModel S .POmegaPlus n 2 f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (e : S ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    OrthCellData (coordinateQuadPlus n K) f := by
  obtain ⟨-, hf, hn⟩ := hmodel.1
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hmodel K hK e
  exact ⟨hK, hf, hn, hnd, hT,
    CFSG.RankThree.Classical.SteinbergBY.orthogonal_large_prime_semilinear_field_and_diagonal_gates S
      .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f hmodel K hK e,
    fun h5 => CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n h5⟩

theorem orthCellData_minus {S : Type} [Group S] {n f : ℕ}
    (hmodel : StatedClassicalModel S .POmegaMinus n 2 f) (hn1 : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : S ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    OrthCellData (coordinateQuadMinus n K hn1 b c) f := by
  obtain ⟨-, hf, hn⟩ := hmodel.1
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hmodel K hK b c hirr e
  exact ⟨hK, hf, hn, hnd, hT,
    CFSG.RankThree.Classical.SteinbergBY.orthogonal_large_prime_semilinear_field_and_diagonal_gates S
      .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f hmodel hn1 K hK b c hirr e,
    fun h5 => CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n
      (by omega) b c hirr⟩

end Model

section Families

open CFSG.HardMathSupport.Curtis.Coordinator (SPLCellFor SPLLieInnerCellFam IsIdxD IsIdxTwistedD
  prime_facts)

theorem exists_stated_model_D {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1) (hD : IsIdxD d.1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : ∃ n f, StatedClassicalModel S .POmegaPlus n 2 f := by
  obtain ⟨r0, q, hdq⟩ := hD
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .D r0 q := hdq
  have hq : q.p = 2 := hd
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r0 q hv hq e
  rw [hq] at h
  exact ⟨_, _, h⟩

theorem exists_stated_model_twistedD {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1) (hD : IsIdxTwistedD d.1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ n f, StatedClassicalModel S .POmegaMinus n 2 f := by
  obtain ⟨r0, q, hdq⟩ := hD
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .twistedD r0 q := hdq
  have hq : q.p = 2 := hd
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r0 q hv hq e
  rw [hq] at h
  exact ⟨_, _, h⟩

@[expose] def OrthPlusCell : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), StatedClassicalModel S .POmegaPlus n 2 f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      S ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
      ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → 5 ≤ r → ¬ r ∣ p - 1 → SPLCellFor S p r

@[expose] def OrthMinusCell : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), StatedClassicalModel S .POmegaMinus n 2 f → 1 ≤ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∀ (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      S ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
      ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → 5 ≤ r → ¬ r ∣ p - 1 → SPLCellFor S p r

theorem splLieInnerCellFam_D_of (H : OrthPlusCell) : SPLLieInnerCellFam IsIdxD := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨n, f, hmodel⟩ := exists_stated_model_D d hd hF e
  obtain ⟨hr5, hrp⟩ := prime_facts hp hp2 hr hr1 hr2
  have hmodel' := hmodel
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel'
  exact H S n f hmodel K hK eK p r hp hp2 hr hr5 hrp

theorem splLieInnerCellFam_twistedD_of (H : OrthMinusCell) : SPLLieInnerCellFam IsIdxTwistedD := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨n, f, hmodel⟩ := exists_stated_model_twistedD d hd hF e
  obtain ⟨hr5, hrp⟩ := prime_facts hp hp2 hr hr1 hr2
  have hmodel' := hmodel
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨eK⟩⟩ := hmodel'
  exact H S n f hmodel (by omega) K hK b c hirr eK p r hp hp2 hr hr5 hrp

end Families

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth
