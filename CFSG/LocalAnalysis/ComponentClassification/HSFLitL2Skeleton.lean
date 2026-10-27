module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Data
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGH
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitTop
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Top

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv Blueprint GorensteinWalter

@[expose] def R8K : Subgroup (Perm (ZMod 8)) := R8 ⊔ zpowers k8

namespace L2Data

variable {X : Type} [Group X] {t : X} {L : Subgroup X} (A : L2Data t L)

structure CaseK where
  k : X
  k_mem : k ∈ A.T
  k_sq : k ^ 2 = 1
  ψ_k : A.ψ ⟨k, k_mem⟩ = k8
  card_K : Nat.card A.K = 2
  range_le : ∀ g, A.ψ g ∈ R8K

structure CaseKD where
  k : X
  k_mem : k ∈ A.T
  k_sq : k ^ 2 = 1
  ψ_k : A.ψ ⟨k, k_mem⟩ = k8
  d : X
  d_mem : d ∈ A.T
  ψ_d : A.ψ ⟨d, d_mem⟩ = d8
  card_K : Nat.card A.K = 2

end L2Data

@[expose] def FritzL2Action : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X), Config t L →
    ∀ (F : Type) [Field F] [Finite F], Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F) →
    ∀ T : Sylow 2 ↥(centralizer ({t} : Set X)), ∃ A : L2Data t L, A.syl = T

@[expose] def FritzL2Section3 : Prop :=
  HaradaInput → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : L2Data t L),
      Nonempty A.CaseK ∨ Nonempty A.CaseKD

@[expose] def L2E {X : Type} [Group X] (z yi t k : X) : Subgroup X := closure {z, yi, t, k}

@[expose] def FritzL2KFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X) (L : Subgroup X) (F : Type) [Field F] [Finite F],
    Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F) → ∀ (A : L2Data t L) (C : A.CaseK),
    ∃ x y : X, x ∈ A.R ∧ y ∈ A.R ∧ y ^ 2 = 1 ∧ y * x * y⁻¹ = x⁻¹ ∧ orderOf x = 4 ∧
      (∃ d ∈ centralizer ({t} : Set X),
        d ∈ normalizer (L2E (x ^ 2) (x * y) t C.k : Set X) ∧ d * x ^ 2 * d⁻¹ = x * y ∧
          d * (x * y) * d⁻¹ = x ^ 2 * (x * y) ∧ d * C.k * d⁻¹ = C.k) ∧
      (∃ d ∈ centralizer ({t} : Set X),
        d ∈ normalizer (L2E (x ^ 2) y t C.k : Set X) ∧ d * x ^ 2 * d⁻¹ = x ^ 2 * y ∧
          d * y * d⁻¹ = x ^ 2 ∧ d * (x ^ 2 * C.k) * d⁻¹ = x ^ 2 * C.k) ∧
      (∀ n ∈ normalizer (L2E (x ^ 2) (x * y) t C.k : Set X) ⊓ centralizer ({t} : Set X),
        n * C.k * n⁻¹ = C.k) ∧
      (∀ n ∈ normalizer (L2E (x ^ 2) y t C.k : Set X) ⊓ centralizer ({t} : Set X),
        n * (x ^ 2 * C.k) * n⁻¹ = x ^ 2 * C.k) ∧
      (∀ g ∈ centralizer ({t} : Set X),
        ¬ ∀ e ∈ L2E (x ^ 2) y t C.k, g * e * g⁻¹ ∈ L2E (x ^ 2) (x * y) t C.k) ∧
      ((∀ g ∈ centralizer ({t} : Set X), g * x ^ 2 * g⁻¹ ≠ t * x ^ 2) →
        {b | ∃ g ∈ centralizer ({t} : Set X), g * x ^ 2 * g⁻¹ = b}.ncard ≡ 1 [MOD 4])

@[expose] def FritzL2CaseK : Prop :=
  FritzA7Sections4to8 → HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (F : Type) [Field F] [Finite F],
      Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F) → ∀ A : L2Data t L, A.CaseK → False

@[expose] def FritzL2CaseKD : Prop :=
  HaradaInput → GorensteinHarrisInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (F : Type) [Field F] [Finite F],
      Nonempty (L ⧸ pPrimeCore 2 L ≃* PSL2 F) → ∀ A : L2Data t L, A.CaseKD →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6)) ∧
          Nonempty (X ≃* NativeSporadic.HS)

theorem fritzTheoremB_of_parts (hH : HaradaInput) (hGH : GorensteinHarrisInput)
    (h48 : FritzA7Sections4to8) (hA : FritzL2Action) (h3 : FritzL2Section3)
    (hK : FritzL2CaseK) (hKD : FritzL2CaseKD) : FritzTheoremB := by
  intro X _ _ _ hnonab t L h hnot
  rcases h.type with he | ⟨F, _, _, -, -, he⟩
  · obtain ⟨e⟩ := he
    exact absurd (gen4_of_alternating_seven hH h48 hnonab h e) hnot
  · obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(centralizer ({t} : Set X))) := inferInstance
    obtain ⟨A, -⟩ := hA X t L h F he T
    rcases h3 hH X hnonab hnot t L A with hk | hkd
    · obtain ⟨hk⟩ := hk
      exact (hK h48 hH X hnonab hnot t L F he A hk).elim
    · obtain ⟨hkd⟩ := hkd
      exact hKD hH hGH X hnonab hnot t L F he A hkd

end CFSG.ComponentClassification.HSFLit
