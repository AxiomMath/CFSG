module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsRadical

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification
open scoped MatrixGroups

section Center

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem inf_center_eq_bot_of_isPGroup (hF : Nat.card F = 4) (hn : 1 ≤ n)
    {Q : Subgroup SL(n, F)} (hQ : IsPGroup 2 Q) : Q ⊓ center SL(n, F) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nat.card (center SL(n, F)) ∣ 3 := by
    have := card_scalars_dvd (K := F) hn
    rwa [scalars_eq_center, hF] at this
  have h1 : Nat.card (Q ⊓ center SL(n, F) : Subgroup SL(n, F)) ∣ 3 :=
    (card_dvd_of_le inf_le_right).trans hZ
  obtain ⟨k, hk⟩ := (hQ.to_le (inf_le_left : Q ⊓ center SL(n, F) ≤ Q)).exists_card_eq
  rw [hk] at h1
  rcases k with _ | k
  · rw [← card_eq_one, hk, pow_zero]
  · exfalso
    have h2 : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1
    omega

theorem card_map_eq_of_inf_ker_eq_bot {A B : Type*} [Group A] [Group B] (f : A →* B)
    (Q : Subgroup A) (h : Q ⊓ f.ker = ⊥) : Nat.card (Q.map f) = Nat.card Q := by
  have hinj : Function.Injective (f.comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have : (q : A) ∈ Q ⊓ f.ker := ⟨q.2, hq⟩
    rw [h, mem_bot] at this
    exact Subtype.ext this
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    range_subtype]

variable {G : Type*} [Group G] {K : Subgroup G}

theorem card_map_of_isPGroup (hF : Nat.card F = 4) (hn : 1 ≤ n) (ψ : SL(n, F) →* K)
    (hker : ψ.ker ≤ center SL(n, F)) {Q : Subgroup SL(n, F)} (hQ : IsPGroup 2 Q) :
    Nat.card (Q.map (K.subtype.comp ψ)) = Nat.card Q := by
  refine card_map_eq_of_inf_ker_eq_bot _ Q (eq_bot_iff.2 fun x hx => ?_)
  have hx' : x ∈ Q ⊓ center SL(n, F) := ⟨hx.1, hker (by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hx.2)⟩
  rwa [inf_center_eq_bot_of_isPGroup hF hn hQ] at hx'

end Center

section Acts

variable {n : ℕ} {F : Type} [Field F] [Finite F] {G : Type*} [Group G] {K : Subgroup G}

omit [Finite F] in
theorem mul_self_eq_one_of_acts (hn : 3 ≤ n) (ψ : SL(n, F) →* K)
    (hker : ψ.ker ≤ center SL(n, F)) {t : G} (ht : t * t = 1) {β : MulAut SL(n, F)}
    (hβ : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (β x)) : β * β = 1 := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) hn
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have key : ∀ x, (ψ (β (β x)) : G) = ψ x := fun x => by
    rw [← hβ, ← hβ, htinv, ← mul_assoc, ← mul_assoc, ht, one_mul, mul_assoc, ht, mul_one]
  have hfg := eq_of_inv_mul_mem_center (β * β).toMonoidHom (MonoidHom.id _) fun x => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Subtype.ext
    change ((ψ (β (β x)) : K) : G)⁻¹ * ψ x = 1
    rw [key, inv_mul_cancel]
  exact MulEquiv.ext fun x => DFunLike.congr_fun hfg x

omit [Finite F] in
theorem map_le_centralizer_of_fixed (ψ : SL(n, F) →* K) {t : G} {β : MulAut SL(n, F)}
    (hβ : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (β x)) {Q : Subgroup SL(n, F)}
    (hQ : ∀ x ∈ Q, β x = x) :
    Q.map (K.subtype.comp ψ) ≤ K ⊓ centralizer ({t} : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(ψ x).2, mem_centralizer_singleton_iff.mpr ?_⟩
  change (ψ x : G) * t = t * ψ x
  have := hβ x
  rw [hQ x hx] at this
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

theorem exists_twoSubgroup_of_fixed (hF : Nat.card F = 4) (hn : 1 ≤ n) (ψ : SL(n, F) →* K)
    (hker : ψ.ker ≤ center SL(n, F)) {t : G} {β : MulAut SL(n, F)}
    (hβ : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (β x)) {Q : Subgroup SL(n, F)}
    (hQ : ∀ x ∈ Q, β x = x) (h2 : IsPGroup 2 Q) :
    ∃ Q' ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q' ∧ Nat.card Q' = Nat.card Q :=
  ⟨_, map_le_centralizer_of_fixed ψ hβ hQ, h2.map _, card_map_of_isPGroup hF hn ψ hker h2⟩

theorem exists_twoSubgroup_of_inner (hF : Nat.card F = 4) {m : ℕ} (hn : n = 2 * m)
    (hm : 1 ≤ m) (ψ : SL(n, F) →* K) (hker : ψ.ker ≤ center SL(n, F)) {t : G}
    {g : SL(n, F)} (hg : g * g = 1) (hgt : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (MulAut.conj g x)) :
    ∃ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q ∧ Nat.card F ^ (m * m) ≤ Nat.card Q := by
  have := charP_two_of_card_four hF
  obtain ⟨Q, hQc, hQ2, hQcard⟩ := exists_twoSubgroup_le_centralizer hn g hg
  obtain ⟨Q', hQ', hQ'2, hQ'card⟩ := exists_twoSubgroup_of_fixed hF (by omega) ψ hker hgt
    (Q := Q) (fun x hx => by
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_singleton_iff.mp (hQc hx)).symm) hQ2
  exact ⟨Q', hQ', hQ'2, hQ'card ▸ hQcard⟩

theorem cases_of_lift (hn : 3 ≤ n) (hF : Nat.card F = 4) (ψ : SL(n, F) →* K)
    (hker : ψ.ker ≤ center SL(n, F)) {t : G} (ht : t * t = 1) {A : GL (Fin n) F}
    {σ : F ≃+* F} {ε : ℕ} (hε : ε ≤ 1)
    (hA : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (stdSL n F A σ ε x)) :
    (σ = 1 ∧ ((∃ g : SL(n, F), g * g = 1 ∧
        ∀ x, t * (ψ x : G) * t⁻¹ = ψ (MulAut.conj g x)) ∨
      ∃ H C : GL (Fin n) F, ((C : Matrix (Fin n) (Fin n) F) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r) ∧
        ∀ x, t * (ψ x : G) * t⁻¹ =
          ψ ((stdSL n F H 1 0 * stdSL n F C 1 1 * (stdSL n F H 1 0)⁻¹) x))) ∨
    (σ ≠ 1 ∧ (∀ c, σ c = c ^ 2) ∧ ∃ H : GL (Fin n) F, ∀ x, t * (ψ x : G) * t⁻¹ =
      ψ ((stdSL n F H 1 0 * stdSL n F 1 σ ε * (stdSL n F H 1 0)⁻¹) x)) := by
  have hβ := mul_self_eq_one_of_acts hn ψ hker ht hA
  have h2 : (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε) ^ 2 = 1 := by
    rw [← descendAut_stdSL, sq, ← map_mul, hβ, map_one]
  rcases stdSL_cases hn hF A σ hε h2 with ⟨-, hσ, g, hg, hgA⟩ | ⟨-, hσ, H, C, hC, hHC⟩ |
      ⟨hε0, hσ, hσx, H, hH⟩ | ⟨hε1, hσ, hσx, H, hH⟩
  · exact Or.inl ⟨hσ, Or.inl ⟨g, hg, fun x => by rw [hA, hgA]⟩⟩
  · exact Or.inl ⟨hσ, Or.inr ⟨H, C, hC, fun x => by rw [hA, hHC]⟩⟩
  · subst hε0
    exact Or.inr ⟨hσ, hσx, H, fun x => by rw [hA, hH]⟩
  · subst hε1
    exact Or.inr ⟨hσ, hσx, H, fun x => by rw [hA, hH]⟩

theorem exists_cases (hn : 3 ≤ n) (hF : Nat.card F = 4) (ψ : SL(n, F) →* K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(n, F)) {t : G}
    (htN : t ∈ normalizer (K : Set G)) (ht : t * t = 1) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      (∀ x, t * (ψ x : G) * t⁻¹ = ψ (stdSL n F A σ ε x)) ∧
    ((σ = 1 ∧ ((∃ g : SL(n, F), g * g = 1 ∧
        ∀ x, t * (ψ x : G) * t⁻¹ = ψ (MulAut.conj g x)) ∨
      ∃ H C : GL (Fin n) F, ((C : Matrix (Fin n) (Fin n) F) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r) ∧
        ∀ x, t * (ψ x : G) * t⁻¹ =
          ψ ((stdSL n F H 1 0 * stdSL n F C 1 1 * (stdSL n F H 1 0)⁻¹) x))) ∨
    (σ ≠ 1 ∧ (∀ c, σ c = c ^ 2) ∧ ∃ H : GL (Fin n) F, ∀ x, t * (ψ x : G) * t⁻¹ =
      ψ ((stdSL n F H 1 0 * stdSL n F 1 σ ε * (stdSL n F H 1 0)⁻¹) x))) := by
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_stdSL_lift hn ψ hψ hker htN
  exact ⟨A, σ, ε, hε, hA, cases_of_lift hn hF ψ hker ht hε hA⟩

end Acts

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
