module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelOMData

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)

section Ext

variable {K : Type} [Field K] [Finite K]

theorem exists_quadExt {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E) (ω : E),
      Nat.card E = Nat.card K ^ 2 ∧ finrank K E = 2 ∧
        ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0 := by
  set P : K[X] := X ^ 2 + C b * X + C c with hP
  have hdeg : P.natDegree = 2 := by
    rw [hP]
    compute_degree!
  have hP0 : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hirrP : Irreducible P := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun s hs => ?_
    apply hirr s
    simpa [hP, IsRoot] using hs
  have : Fact (Irreducible P) := ⟨hirrP⟩
  have hfin : finrank K (AdjoinRoot P) = 2 := by
    rw [(AdjoinRoot.powerBasis hP0).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, AdjoinRoot.root P, ?_, hfin,
    ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := K), hfin]
  · have h := AdjoinRoot.eval₂_root P
    simpa [hP, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_X_pow, AdjoinRoot.algebraMap_eq]
      using h

end Ext

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  [Finite E] {g : ℕ} {b c : K} {ω : E}

omit [Finite K] [Finite E] in
include K in
theorem charTwo_of_algebra : CharP E 2 :=
  charP_of_injective_algebraMap (algebraMap K E).injective 2

omit [CharP K 2] [Finite E] in
theorem algebraMap_pow_two_pow (hK : Nat.card K = 2 ^ g) (k : K) :
    algebraMap K E k ^ 2 ^ g = algebraMap K E k := by
  have := Fintype.ofFinite K
  rw [← map_pow]
  congr 1
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card k

omit [Finite K] [CharP K 2] [Finite E] in
theorem eq_zero_of_add_mul_omega (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) {α β : K}
    (h : algebraMap K E α + algebraMap K E β * ω = 0) : α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap K E).injective (by rw [h, map_zero]), rfl⟩
  · exfalso
    have hβ' : algebraMap K E β ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hωe : ω = algebraMap K E (-α / β) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    apply hirr (-α / β)
    apply (algebraMap K E).injective
    rw [map_add, map_add, map_mul, map_pow, ← hωe, map_zero]
    exact hω

theorem ne_zero_of_irreducible (hK : Nat.card K = 2 ^ g) (hg : 1 ≤ g)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  have := Fintype.ofFinite K
  apply hirr (c ^ 2 ^ (g - 1))
  have hc : (c ^ 2 ^ (g - 1)) ^ 2 = c := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hg, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rw [hc, zero_mul, add_zero]
  exact CharTwo.add_self_eq_zero c

omit [Finite K] [CharP K 2] [Finite E] in
theorem omega_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) : ω ≠ 0 := by
  rintro rfl
  apply hirr 0
  apply (algebraMap K E).injective
  simpa using hω

theorem card_le_of_forall_pow_eq {p : ℕ} (hp : 1 < p) (h : ∀ z : E, z ^ p = z) :
    Nat.card E ≤ p := by
  classical
  have := Fintype.ofFinite E
  have hne : (X ^ p - X : E[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hp
  have hsub : (Finset.univ : Finset E) ⊆ (X ^ p - X : E[X]).roots.toFinset := fun z _ => by
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, h z, sub_self]
  calc Nat.card E = (Finset.univ : Finset E).card := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ (X ^ p - X : E[X]).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (X ^ p - X : E[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ p - X : E[X]).natDegree := card_roots' _
    _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq E hp

theorem omega_pow_two_pow (hK : Nat.card K = 2 ^ g) (hg : 1 ≤ g) (hE : Nat.card E = Nat.card K ^ 2)
    (hfin : finrank K E = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) :
    ω ^ 2 ^ g = ω + algebraMap K E b := by
  have : CharP E 2 := charTwo_of_algebra (K := K)
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  set z := ω ^ 2 ^ g with hz
  have hzr : z ^ 2 + algebraMap K E b * z + algebraMap K E c = 0 := by
    have h := congrArg (fun w : E => w ^ 2 ^ g) hω
    simp only [zero_pow (pow_ne_zero g two_ne_zero)] at h
    rw [add_pow_char_pow, add_pow_char_pow, mul_pow, ← pow_mul, mul_comm 2, pow_mul,
      algebraMap_pow_two_pow hK, algebraMap_pow_two_pow hK] at h
    exact h
  have hprod : (z - ω) * (z - ω - algebraMap K E b) = 0 := by
    linear_combination hzr + hω - (algebraMap K E b * z + algebraMap K E c + z * ω) * h2
  rcases mul_eq_zero.1 hprod with h1 | h1
  · exfalso
    have hzω : z = ω := sub_eq_zero.1 h1
    have hli : LinearIndependent K ![(1 : E), ω] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      exact eq_zero_of_add_mul_omega hirr hω hst
    set B := basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfin]; rfl) with hB
    have hfix : ∀ w : E, w ^ 2 ^ g = w := by
      intro w
      have hw := B.sum_repr w
      rw [Fin.sum_univ_two, hB, coe_basisOfLinearIndependentOfCardEqFinrank'] at hw
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hw
      rw [← hw, add_pow_char_pow, mul_pow, algebraMap_pow_two_pow hK, algebraMap_pow_two_pow hK,
        ← hz, hzω]
    have hle := card_le_of_forall_pow_eq (Nat.one_lt_two_pow (by omega)) hfix
    rw [hE, hK, ← pow_mul] at hle
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : g < g * 2)
    omega
  · linear_combination h1

end Field

section Coord

open CFSG.ClassicalGroups.UnitaryFlag (HypIndex hypPartner hypForm hypForm_apply)

@[expose] def lagLo {k : ℕ} (i : Fin k) : Fin (2 * k + 1 - 1) := ⟨i.1, by omega⟩

@[expose] def lagHi {k : ℕ} (i : Fin k) : Fin (2 * k + 1 - 1) := ⟨k + i.1, by omega⟩

theorem sum_fin_two_mul_eq {M : Type*} [AddCommMonoid M] (k : ℕ) (f : Fin (2 * k + 1 - 1) → M) :
    ∑ a, f a = ∑ i : Fin k, (f (lagLo i) + f (lagHi i)) := by
  set e : Fin (2 * k + 1 - 1) ≃ Fin (k + k) := finCongr (by omega)
  rw [← e.symm.sum_comp, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  rfl

variable {K : Type} [Field K] {E : Type} [Field E] [Algebra K E]

@[expose] def lagUnitCoord (b : K) (ω : E) (k : ℕ)
    (v : Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K) : HypIndex k 1 → E
  | .inl i => algebraMap K E (v (.inl (lagLo i))) + algebraMap K E (v (.inl (lagHi i))) * ω
  | .inr (.inl _) => algebraMap K E (v (.inr (.inr 0))) + algebraMap K E (v (.inr (.inr 1))) * ω
  | .inr (.inr i) => (algebraMap K E (v (.inr (.inl (lagHi i)))) +
      algebraMap K E (v (.inr (.inl (lagLo i)))) * ω) * (algebraMap K E b)⁻¹

@[expose] def lagUnitLin (b : K) (ω : E) (k : ℕ) :
    (Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K) →ₗ[K] (HypIndex k 1 → E) where
  toFun := lagUnitCoord b ω k
  map_add' v w := by
    funext a
    rcases a with i | j | i <;> simp only [lagUnitCoord, Pi.add_apply, map_add] <;> ring
  map_smul' t v := by
    funext a
    rcases a with i | j | i <;>
      simp only [lagUnitCoord, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
        Algebra.smul_def] <;> ring

end Coord

section Form

open CFSG.ClassicalGroups.UnitaryFlag (HypIndex hypPartner hypForm hypForm_apply
  hypPartner_inl hypPartner_inr_inl hypPartner_inr_inr)

variable {K : Type} [Field K] [CharP K 2] {E : Type} [Field E] [Algebra K E] {p f : ℕ}

theorem hypForm_lagUnitCoord (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hbar : ∀ t : K, h.bar (algebraMap K E t) = algebraMap K E t) {b c : K} {ω : E}
    (hbω : h.bar ω = ω + algebraMap K E b) (hb : b ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) (k : ℕ)
    (v : Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K) :
    hypForm h k 1 (lagUnitCoord b ω k v) (lagUnitCoord b ω k v) =
      algebraMap K E (quadMinus (2 * k + 1) K b c v) := by
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hb' : algebraMap K E b ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hBinv : (algebraMap K E b)⁻¹ * algebraMap K E b = 1 := inv_mul_cancel₀ hb'
  have hbinv : h.bar (algebraMap K E b)⁻¹ = (algebraMap K E b)⁻¹ := by rw [map_inv₀, hbar]
  set Ψ := lagUnitCoord b ω k v with hΨ
  have hL : hypForm h k 1 Ψ Ψ = ∑ i : Fin k, (h.bar (Ψ (.inl i)) * Ψ (.inr (.inr i)) +
      h.bar (Ψ (.inr (.inr i))) * Ψ (.inl i)) + h.bar (Ψ (.inr (.inl 0))) * Ψ (.inr (.inl 0)) := by
    rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_one,
      Finset.sum_add_distrib]
    simp only [hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr]
    ring
  have hR : algebraMap K E (quadMinus (2 * k + 1) K b c v) =
      ∑ i : Fin k, (algebraMap K E (v (.inl (lagLo i))) *
          algebraMap K E (v (.inr (.inl (lagLo i)))) +
        algebraMap K E (v (.inl (lagHi i))) * algebraMap K E (v (.inr (.inl (lagHi i))))) +
      (algebraMap K E (v (.inr (.inr 0))) ^ 2 +
        algebraMap K E b * algebraMap K E (v (.inr (.inr 0))) * algebraMap K E (v (.inr (.inr 1))) +
        algebraMap K E c * algebraMap K E (v (.inr (.inr 1))) ^ 2) := by
    rw [quadMinus_apply, sum_fin_two_mul_eq]
    simp only [map_add, map_mul, map_sum, map_pow]
    ring
  rw [hL, hR]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
  · simp only [hΨ, lagUnitCoord, map_add, map_mul, hbar, hbω, hbinv]
    linear_combination ((algebraMap K E b)⁻¹ *
      (algebraMap K E (v (.inl (lagLo i))) * algebraMap K E (v (.inr (.inl (lagHi i)))) +
       algebraMap K E (v (.inl (lagLo i))) * algebraMap K E (v (.inr (.inl (lagLo i)))) * ω +
       algebraMap K E (v (.inl (lagHi i))) * algebraMap K E (v (.inr (.inl (lagHi i)))) * ω +
       algebraMap K E (v (.inl (lagHi i))) * algebraMap K E (v (.inr (.inl (lagLo i)))) * ω ^ 2 +
       algebraMap K E (v (.inl (lagHi i))) * algebraMap K E (v (.inr (.inl (lagLo i)))) *
         algebraMap K E b * ω)) * h2 +
      (algebraMap K E (v (.inl (lagLo i))) * algebraMap K E (v (.inr (.inl (lagLo i)))) +
       algebraMap K E (v (.inl (lagHi i))) * algebraMap K E (v (.inr (.inl (lagHi i))))) * hBinv
  · simp only [hΨ, lagUnitCoord, map_add, map_mul, hbar, hbω]
    linear_combination (algebraMap K E (v (.inr (.inr 0))) * algebraMap K E (v (.inr (.inr 1))) *
        ω - algebraMap K E c * algebraMap K E (v (.inr (.inr 1))) ^ 2) * h2 +
      algebraMap K E (v (.inr (.inr 1))) ^ 2 * hω

end Form

section Iso

open CFSG.ClassicalGroups.UnitaryFlag (HypIndex)

variable {K : Type} [Field K] {E : Type} [Field E] [Algebra K E]

theorem lagUnitLin_injective {b c : K} {ω : E} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) (hb : b ≠ 0) (k : ℕ) :
    Function.Injective (lagUnitLin b ω k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv' : ∀ a, lagUnitCoord b ω k v a = 0 := fun a => congrFun hv a
  have hb' : (algebraMap K E b)⁻¹ ≠ 0 := inv_ne_zero (by rwa [ne_eq, map_eq_zero])
  have he : ∀ i, v (.inl (lagLo i)) = 0 ∧ v (.inl (lagHi i)) = 0 := fun i =>
    eq_zero_of_add_mul_omega hirr hω (hv' (.inl i))
  have hf : ∀ i, v (.inr (.inl (lagHi i))) = 0 ∧ v (.inr (.inl (lagLo i))) = 0 := fun i =>
    eq_zero_of_add_mul_omega hirr hω ((mul_eq_zero.1 (hv' (.inr (.inr i)))).resolve_right hb')
  have hz := eq_zero_of_add_mul_omega hirr hω (hv' (.inr (.inl 0)))
  have hcover : ∀ a : Fin (2 * k + 1 - 1), ∃ i : Fin k, a = lagLo i ∨ a = lagHi i := by
    intro a
    by_cases ha : a.1 < k
    · exact ⟨⟨a.1, ha⟩, .inl (Fin.ext rfl)⟩
    · exact ⟨⟨a.1 - k, by omega⟩, .inr (Fin.ext (by simp only [lagHi]; omega))⟩
  funext x
  rcases x with a | a | j
  · obtain ⟨i, rfl | rfl⟩ := hcover a
    exacts [(he i).1, (he i).2]
  · obtain ⟨i, rfl | rfl⟩ := hcover a
    exacts [(hf i).2, (hf i).1]
  · fin_cases j
    exacts [hz.1, hz.2]

@[expose] noncomputable def lagUnitEquiv {b c : K} {ω : E} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hω : ω ^ 2 + algebraMap K E b * ω + algebraMap K E c = 0) (hb : b ≠ 0)
    (hfin : finrank K E = 2) (k : ℕ) :
    (Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K) ≃ₗ[K] (HypIndex k 1 → E) :=
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hfin
  LinearEquiv.ofBijective (lagUnitLin b ω k) ⟨lagUnitLin_injective hirr hω hb k,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
      simp only [hfin, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_sum,
        Fintype.card_fin]
      omega)).1 (lagUnitLin_injective hirr hω hb k)⟩

end Iso

section Main

open CFSG.ClassicalGroups.UnitaryFlag (HypIndex hypForm hypForm_isSymm hypForm_separatingLeft)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData sesqUnitaryGroup mem_sesqUnitaryGroup)

theorem omegaMinusUnitaryPairInput_holds : OmegaMinusUnitaryPairInput := by
  intro K _ _ _ g n hg hK hodd hn5 b c hirr
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨E, _, _, _, ω, hE, hfin, hω⟩ := exists_quadExt hirr
  have : CharP E 2 := charTwo_of_algebra (K := K)
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h : UnitaryFieldData 2 g E := ⟨Nat.prime_two, hg, by rw [hE, hK, ← pow_mul, mul_comm]⟩
  have hb : b ≠ 0 := ne_zero_of_irreducible hK hg hirr
  have hb' : algebraMap K E b ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hbar : ∀ t : K, h.bar (algebraMap K E t) = algebraMap K E t := fun t => by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    exact algebraMap_pow_two_pow hK t
  have hbω : h.bar ω = ω + algebraMap K E b := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    exact omega_pow_two_pow hK hg hE hfin hirr hω
  have hω0 : ω ≠ 0 := omega_ne_zero hirr hω
  have hωb : ω + algebraMap K E b ≠ 0 := by
    rw [← hbω]
    exact (map_ne_zero h.bar).2 hω0
  set Ψe := lagUnitEquiv hirr hω hb hfin k with hΨe
  have hQΨ : ∀ v, hypForm h k 1 (Ψe v) (Ψe v) = algebraMap K E (quadMinus (2 * k + 1) K b c v) :=
    hypForm_lagUnitCoord h hbar hbω hb hω k
  set B := hypForm h k 1 with hBdef
  let rs : ((HypIndex k 1 → E) ≃ₗ[E] (HypIndex k 1 → E)) →*
      ((HypIndex k 1 → E) ≃ₗ[K] (HypIndex k 1 → E)) :=
    { toFun := fun f => f.restrictScalars K
      map_one' := LinearEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl }
  have hrs : Function.Injective rs := fun f f' hff => LinearEquiv.ext fun x =>
    congrArg (fun F : (HypIndex k 1 → E) ≃ₗ[K] (HypIndex k 1 → E) => F x) hff
  let T : sesqUnitaryGroup B →* ((Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (2 * k + 1 - 1) ⊕ Fin (2 * k + 1 - 1) ⊕ Fin 2 → K)) :=
    (LinearEquiv.autCongr Ψe.symm).toMonoidHom.comp
      (rs.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv E _).toMonoidHom.comp
        (sesqUnitaryGroup B).subtype))
  have hT : Function.Injective T :=
    (LinearEquiv.autCongr Ψe.symm).injective.comp (hrs.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv E _).injective.comp
        (sesqUnitaryGroup B).subtype_injective))
  have hTapp : ∀ (u : sesqUnitaryGroup B) v,
      Ψe (T u v) = ((u : LinearMap.GeneralLinearGroup E (HypIndex k 1 → E)) :
        Module.End E (HypIndex k 1 → E)) (Ψe v) := by
    intro u v
    simp [T, rs, LinearEquiv.autCongr_apply_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  have hTO : ∀ u : sesqUnitaryGroup B,
      T u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (2 * k + 1) K b c) := by
    intro u
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    apply (algebraMap K E).injective
    rw [← hQΨ, ← hQΨ, hTapp]
    exact (mem_sesqUnitaryGroup.1 u.2) _ _
  set lam : E := ω * (ω + algebraMap K E b)⁻¹ with hlam
  have hlam0 : lam ≠ 0 := mul_ne_zero hω0 (inv_ne_zero hωb)
  have hlam1 : lam ≠ 1 := by
    intro h1
    rw [hlam, mul_inv_eq_one₀ hωb] at h1
    apply hb'
    linear_combination (-1 : E) * h1
  have hnorm : h.bar lam * lam = 1 := by
    have hω2 : ω + algebraMap K E b + algebraMap K E b = ω := by
      linear_combination algebraMap K E b * h2
    rw [hlam, map_mul, map_inv₀, map_add, hbω, hbar, hω2]
    field_simp
  have hlampow : lam ^ (2 ^ g + 1) = 1 := by
    rw [pow_succ, ← CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply h, hnorm]
  set yU : LinearMap.GeneralLinearGroup E (HypIndex k 1 → E) :=
    Units.map (algebraMap E (Module.End E (HypIndex k 1 → E))).toMonoidHom (Units.mk0 lam hlam0)
    with hyUdef
  have hyU : ∀ x, ((yU : LinearMap.GeneralLinearGroup E (HypIndex k 1 → E)) :
      Module.End E (HypIndex k 1 → E)) x = lam • x := fun x => by
    simp [hyUdef]
  have hyUmem : yU ∈ sesqUnitaryGroup B := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    rw [hyU, hyU]
    simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm lam, hnorm, one_mul]
  set y₀ : sesqUnitaryGroup B := ⟨yU, hyUmem⟩ with hy₀
  have : Finite (Module.End E (HypIndex k 1 → E)) :=
    Finite.of_injective (fun f : Module.End E (HypIndex k 1 → E) => (f : (HypIndex k 1 → E) →
      (HypIndex k 1 → E))) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup E (HypIndex k 1 → E)) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup E (HypIndex k 1 → E) =>
      (u : Module.End E (HypIndex k 1 → E))) Units.val_injective
  have := Fintype.ofFinite (sesqUnitaryGroup B)
  have hk' : 0 < 2 * g * (2 * k + 1) := Nat.mul_pos (by omega) (by omega)
  have h10 : 10 ≤ 2 * g * (2 * k + 1) := by nlinarith
  obtain ⟨ℓ, hℓ⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * g * (2 * k + 1))
    (by omega) (by omega)
  have hℓp := hℓ.prime
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ2 : ℓ ≠ 2 := hℓ.ne_two hk'
  have hℓdvd : ℓ ∣ 2 ^ (g * (2 * k + 1)) + 1 := by
    refine (hℓ.dvd_add_one_iff hk' _).2 ⟨⟨1, by ring⟩, fun hd => ?_⟩
    have := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hd
    nlinarith
  have hfr : finrank E (HypIndex k 1 → E) = 2 * k + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨hU, -⟩ := CFSG.LinearGroups.unitary_full_group_order h (hypForm_isSymm h)
    (hypForm_separatingLeft h) hfr (by omega)
  have hdvdU : ℓ ∣ Nat.card (sesqUnitaryGroup B) := by
    have h1 : (ℓ : ℤ) ∣ (((2 ^ g : ℕ) : ℤ) ^ (2 * k + 1) - (-1) ^ (2 * k + 1)) := by
      have he : (((2 ^ g : ℕ) : ℤ) ^ (2 * k + 1) - (-1) ^ (2 * k + 1)) =
          ((2 ^ (g * (2 * k + 1)) + 1 : ℕ) : ℤ) := by
        rw [Odd.neg_one_pow ⟨k, rfl⟩]
        push_cast
        rw [← pow_mul]
        ring
      rw [he]
      exact_mod_cast hℓdvd
    have h3 : (ℓ : ℤ) ∣ (Nat.card (sesqUnitaryGroup B) : ℤ) := by
      rw [hU]
      exact Dvd.dvd.mul_left (h1.trans (Finset.dvd_prod_of_mem
        (fun i => ((2 ^ g : ℕ) : ℤ) ^ i - (-1) ^ i)
        (Finset.mem_Icc.2 ⟨(by omega : 1 ≤ 2 * k + 1), le_rfl⟩))) _
    exact_mod_cast h3
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card (G := sesqUnitaryGroup B) ℓ
    (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨hnd, hT3⟩ := regular_quadMinus (K := K) (n := 2 * k + 1) (by omega) hirr
  obtain ⟨-, -, -, -, -, -, hoddmem, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT3
  have hxΩ : T x₀ ∈ orthDerived (quadMinus (2 * k + 1) K b c) :=
    hoddmem _ (hTO x₀) (by rw [orderOf_injective T hT x₀, hx₀]; exact hℓp.odd_of_ne_two hℓ2)
  have hmk : (Units.mk0 lam hlam0) ^ (2 ^ g + 1) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hlampow, Units.val_one])
  have hy₀pow : y₀ ^ (2 ^ g + 1) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hy₀]
    show yU ^ (2 ^ g + 1) = 1
    rw [hyUdef, ← map_pow, hmk, map_one]
  have hodd2 : Odd (2 ^ g + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hyΩ : T y₀ ∈ orthDerived (quadMinus (2 * k + 1) K b c) :=
    hoddmem _ (hTO y₀) (Odd.of_dvd_nat hodd2
      (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy₀pow, map_one])))
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply hlam1
    have h3 := congrArg (fun u : sesqUnitaryGroup B =>
      ((u : LinearMap.GeneralLinearGroup E (HypIndex k 1 → E)) : Module.End E (HypIndex k 1 → E))
        (Pi.single (.inr (.inl 0)) 1)) h1
    simp only [hy₀, hyU, OneMemClass.coe_one, Units.val_one, Module.End.one_apply] at h3
    have h4 := congrFun h3 (.inr (.inl 0))
    simpa using h4
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hy₀, hyU, map_smul]
  refine ⟨⟨T x₀, hxΩ⟩, ⟨T y₀, hyΩ⟩, ℓ, ?_, ?_, ?_, hℓ, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hcomm]
  · intro h1
    apply hy₀1
    apply hT
    rw [map_one]
    exact congrArg Subtype.val h1
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hy₀pow, map_one]
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, ← hx₀, pow_orderOf_eq_one,
      map_one]
  · intro h1
    have h3 : x₀ = 1 := hT (by rw [map_one]; exact congrArg Subtype.val h1)
    rw [h3, orderOf_one] at hx₀
    exact hℓp.one_lt.ne hx₀

end Main

end CFSG.SeitzReduction.SymplecticPilot
