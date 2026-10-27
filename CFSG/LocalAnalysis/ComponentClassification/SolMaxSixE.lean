module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCkInv
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCJ

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

@[expose] def KernelBalanceAt {X : Type} [Group X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (K : Subgroup X) : Prop :=
  ∀ F : Subgroup X, F ≤ J → Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
    ∀ DF : Finset (Fin 9), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Perm (Fin 9)) ω = ω) →
    ∀ a ∈ F, a ≠ 1 →
    ∀ L : Subgroup X, L ≤ centralizer (F : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer (F : Set X))) → L ≤ K →
      t ∈ normalizer (L : Set X) →
      (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype ⊔ L =
        (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype ⊔
          ⁅L, zpowers t⁆ →
      ⁅L, (pPrimeCore 2 ↥(centralizer ({a * t} : Set X))).map
          (centralizer ({a * t} : Set X)).subtype ⊓ centralizer (F : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype

theorem kernelBalanceAt_of_uniqueInvolution {X : Type} [Group X] [Finite X] {t : X}
    {J K Q : Subgroup X} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htK : t ∈ K) (hQK : Q ≤ K)
    (hQcard : Nat.card Q = 2 ^ (Nat.card K).factorization 2)
    (hQu : ∀ y ∈ Q, orderOf y = 2 → y = t) : KernelBalanceAt t J e K := by
  intro F _ _ DF _ _ a _ _ L hLC hLpc hLK htN hcov
  exfalso
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hconjo : ∀ k y : X, orderOf (k * y * k⁻¹) = orderOf y := fun k y => by
    have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
    simpa using this
  have huniq : ∀ P : Subgroup X, P ≤ K → IsPGroup 2 P → t ∈ P →
      ∀ y ∈ P, y ≠ 1 → y * y = 1 → y = t := by
    intro P hPK hP2 htP y hyP hy1 hy2
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_card_eq_of_le hQK hQcard hPK hP2
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
    have h1 : k * t * k⁻¹ = t := hQu _ (hk t htP) (by rw [hconjo, hto])
    have h2 : k * y * k⁻¹ = t := hQu _ (hk y hyP) (by rw [hconjo, hyo])
    rw [← h1] at h2
    have h3 := congrArg (fun z => k⁻¹ * z * k) h2
    simpa [mul_assoc] using h3
  exact false_of_isPComponent_of_uniqueInvolution hLC hLpc hLK htK ht2 ht1 htN huniq hcov

end CFSG.ComponentClassification.SolMax
