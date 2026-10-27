module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.FixedInverted
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.InvertedTorus
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.UnitaryForm
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.UnitaryInvolutionIndex

open Matrix Module

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

@[expose] noncomputable def glMap (k : Type*) [Field k] [Algebra F k] :
    GL n F →* Module.End k (n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k)).toMonoidHom.comp
    ((Units.coeHom _).comp (GeneralLinearGroup.map (algebraMap F k)))

theorem glMap_apply (k : Type*) [Field k] [Algebra F k] (g : GL n F) (v : n → k) :
    glMap k g v = ((g : Matrix n n F).map (algebraMap F k)) *ᵥ v := by
  simp [glMap]

theorem glMap_injective (k : Type*) [Field k] [Algebra F k] :
    Function.Injective (glMap (n := n) (F := F) k) := by
  intro g g' hgg'
  apply Units.ext
  ext i j
  have h := congrArg (fun T : Module.End k (n → k) => T (Pi.single j 1) i) hgg'
  simp only [glMap_apply, mulVec_single_one, col_apply, map_apply] at h
  exact (algebraMap F k).injective h

theorem glMap_apply_injective (k : Type*) [Field k] [Algebra F k] (g : GL n F) :
    Function.Injective (glMap k g) := by
  intro v w hvw
  have h := congrArg (glMap k g⁻¹) hvw
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Module.End.one_apply] at h

theorem exists_charP_of_card_eq_sq [Finite F] {q : ℕ} (hq : IsPrimePow q)
    (hF : Nat.card F = q ^ 2) : ∃ ℓ f : ℕ, ℓ.Prime ∧ 0 < f ∧ ℓ ^ f = q ∧ CharP F ℓ := by
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := (isPrimePow_def q).mp hq
  rw [← Nat.prime_iff] at hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let := Fintype.ofFinite F
  exact ⟨ℓ, f, hℓ, hf, rfl, charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])⟩

theorem prime_facts_of_dvd_succ {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime)
    (hf : 0 < f) (hpq : p ∣ ℓ ^ f + 1) : p ≠ ℓ ∧ ¬p ∣ ℓ ^ f ∧ ¬p ∣ ℓ ^ f - 1 := by
  have hpq' : ¬p ∣ ℓ ^ f := fun hd => by
    have := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨fun h => hpq' (h ▸ dvd_pow_self p hf.ne'), hpq', fun hd => ?_⟩
  have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h2 : ℓ ^ f + 1 = (ℓ ^ f - 1) + 2 := by omega
  rw [h2] at hpq
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right hd).mp hpq))

theorem isCyclic_and_card_le_of_le_unitaryGroup [Finite F] {q : ℕ} (hq : IsPrimePow q)
    (hF : Nat.card F = q ^ 2) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ q)
    {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F} (hh : h.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (B : Subgroup (GL (Fin 3) F)) (hBU : B ≤ unitaryGroup h)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : IsPGroup p B) {t : GL (Fin 3) F}
    (htB : ∀ b ∈ B, t * b * t⁻¹ = b⁻¹) :
    IsCyclic B ∧ Nat.card B ≤ p ^ (q + 1).factorization p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hf, rfl, hchar⟩ := exists_charP_of_card_eq_sq hq hF
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP (AlgebraicClosure F) ℓ :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective ℓ
  set k := AlgebraicClosure F
  let φ : k →+* k := iterateFrobenius k ℓ f
  have hφ : ∀ c, φ c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hφι : ∀ c : F, φ (algebraMap F k c) = algebraMap F k (σ c) := by
    intro c
    rw [hφ, hσ, map_pow]
  obtain ⟨hpℓ, hpq', hpq1⟩ := prime_facts_of_dvd_succ hp hp2 hℓ hf hpq
  have hpk : (p : k) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff k ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  let ρ : B →* Module.End k (Fin 3 → k) := (glMap k).comp B.subtype
  have hρ : Function.Injective ρ := (glMap_injective k).comp B.subtype_injective
  have hTρ : ∀ b : B, glMap k t * ρ b = ρ b⁻¹ * glMap k t := by
    intro b
    have hb := htB b b.2
    have e : t * (b : GL (Fin 3) F) = ((b : GL (Fin 3) F))⁻¹ * t := by
      rw [← hb]
      group
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, InvMemClass.coe_inv, ← map_mul, e]
  have hβρ : ∀ (b : B) (v w : Fin 3 → k),
      baseChange h φ (ρ b v) (ρ b w) = baseChange h φ v w := by
    intro b v w
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, glMap_apply]
    exact baseChange_mulVec h hφι (hBU b.2) v w
  exact isCyclic_and_card_le_of_inverted hpk hp2 hBp
    (fun x y => Subtype.ext (hBc _ x.2 _ y.2)) ρ hρ (Module.finrank_fin_fun k) (glMap k t)
    (glMap_apply_injective k t) hTρ hφ (baseChange h φ)
    (baseChange_separatingLeft hh φ.injective) hβρ hpq' hpq1

theorem unitary_three_abelian_involution_index_bound [Finite F] {q : ℕ} (hq : IsPrimePow q)
    (hF : Nat.card F = q ^ 2) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ q)
    {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F} (hh : h.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (A : Subgroup (GL (Fin 3) F)) (hAU : A ≤ unitaryGroup h)
    (hAc : IsMulCommutative A) (hAp : IsPGroup p A) (t : GL (Fin 3) F) (ht : t ^ 2 = 1)
    (htA : t ∈ Subgroup.normalizer (A : Set (GL (Fin 3) F))) :
    (A ⊓ Subgroup.centralizer {t}).relIndex A ≤ p ^ (q + 1).factorization p ∧
      IsCyclic (Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)}) ∧
      Nat.card (Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)}) ≤
        p ^ (q + 1).factorization p ∧
      (∀ b ∈ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)}, t * b * t⁻¹ = b⁻¹) ∧
      A ⊓ Subgroup.centralizer {t} ⊓ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} =
        ⊥ ∧
      A ⊓ Subgroup.centralizer {t} ⊔ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} =
        A := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have hodd : Odd (Nat.card A) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
    rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  have hBA := closure_commutator_le hA htA
  obtain ⟨hcyc, hcard⟩ := isCyclic_and_card_le_of_le_unitaryGroup hq hF hσ hh hp hp2 hpq _
    (hBA.trans hAU) (fun x hx y hy => hA x (hBA hx) y (hBA hy))
    (hAp.to_le hBA) (fun b hb => conj_eq_inv_of_mem ht htA hA hb)
  exact ⟨(relIndex_eq_card htA hA).trans_le hcard, hcyc, hcard,
    fun b hb => conj_eq_inv_of_mem ht htA hA hb, inf_eq_bot ht htA hA hodd,
    sup_eq ht htA hA hodd⟩

end CFSG.UnitaryInvolutionIndex
