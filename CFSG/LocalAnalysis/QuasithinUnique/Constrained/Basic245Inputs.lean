module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

@[expose] def NaturalModuleStructure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R H L : Subgroup G),
    IsMinimalParabolic R H → CharTwo H → IsChi0Block H L →
    ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) →
    ⁅L, thompsonJ R⁆ = L → H = L ⊔ R → R ≤ Subgroup.normalizer (L : Set G) →
    ∃ (q : ℕ) (W : Subgroup G), 2 ≤ q ∧ W ≤ blockU L ∧
      (baum R ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex (baum R) = q ∧
      W.relIndex (blockU L) = q ∧
      (∀ y ∈ baum R, y ∉ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
        ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)) ∧
      ⁅blockU L, baum R⁆ = W ∧
      (blockU L ⊓ Subgroup.centralizer (L : Set G)).relIndex (blockU L) = q ^ 2 ∧
      (∀ y ∈ Subgroup.normalizer (baum R : Set G),
        ¬ conjSubgroup (blockU L) y ≤ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
        ¬ conjSubgroup (blockU L) y⁻¹ ≤ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
        ∃ k ∈ L, L ≤ conjSubgroup (blockU L) y ⊔ conjSubgroup (conjSubgroup (blockU L) y) k) ∧
      (∀ r ∈ R, (∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H) → r ∈ baum R ⊔ pCoreOf 2 H)

@[expose] def C56_7Concl (S H L M₀ : Subgroup G) : Prop :=
  blockU0 S L = pCoreOf 2 (conjJoin S L) ∧
  IsElemAbelian 2 (baumD S L) ∧
  baumD S L = blockD S L ∧
  pCoreOf 2 H = baumD S L ⊔ blockU0 S L ∧
  CFSG.Quasithin.IsMaxElemAbelian S (pCoreOf 2 H) ∧
  CFSG.Quasithin.baum S = CFSG.Quasithin.thompsonJ S ∧
  ∀ x ∈ M₀, x ∉ S →
    baumD S L ⊓ conjR (baumD S L) x = ⊥ ∧
    CFSG.Quasithin.baum S = baumD S L ⊔ blockU0 S L ⊔ conjR (blockU0 S L) x ∧
    (conjJoin S L = L → (IsAltType L 3 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A ↔
        A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) ∧
    (conjJoin S L = L → IsAltType L 5 →
      ∀ r ∈ S ⊓ conjJoin S L, r ∉ CFSG.Quasithin.baum S →
        ∃ A : Subgroup G, (A ⊓ pCoreOf 2 H).relIndex A = 2 ∧
          ∀ B : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S B ↔
            B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x ∨ B = A ∨ B = conjR A r) ∧
    (conjJoin S L ≠ L →
      ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A →
        ((∀ s ∈ S, conjR A s = A) ↔
          (A = baumD S L ⊔ blockU0 S L ∨ A = baumD S L ⊔ conjR (blockU0 S L) x)))

theorem lemma245_C56_7_iff : Lemma245_C56_7 ↔
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
      ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀ :=
  Iff.rfl

@[expose] def C56A5Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀

@[expose] def C56DoubleCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L ≠ L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 → C56_7Concl S H L M₀

@[expose] def BlockUEqO2Single : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) → blockU L = blockQ L

@[expose] def C61Concl (T H S L : Subgroup G) : Prop :=
  (S.relIndex (normT T S) = 2 ∧
    ∀ x ∈ normT T S, x ∉ S →
      CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.baum S ∧
      CFSG.Quasithin.baum S = pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x) ∧
  (conjJoin S L = L →
    ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) →
      (∀ x ∈ normT T S, x ∉ S → ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A ↔
        A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) ∧
      ((IsAltType L 3 → Nat.card (blockD S L) ≤ 2 ^ 1) ∧
        ∀ n : ℕ, 1 < n → IsLin2Type L n → Nat.card (blockD S L) ≤ 2 ^ n)) ∧
  ((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L) →
    ∀ x ∈ normT T S, x ∉ S → ∀ r ∈ S, r ∉ CFSG.Quasithin.thompsonJ S →
      ∃ A₁ : Subgroup G, (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
        ∀ B : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S B ↔
          B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x ∨ B = A₁ ∨ B = conjR A₁ r) ∧
  pCoreOf 2 H = blockD S L ⊔ pCoreOf 2 (conjJoin S L) ∧
  ((S.relIndex T = 2 ∧ CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ T ∧
      (IsAltType L 3 → conjJoin S L = L →
        Nonempty (H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
    (IsAltType L 3 ∧ conjJoin S L = L ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
      IsDihedralOrSemidihedral T) ∨
    (((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) ∧
      CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ (normT T S) ∧
      (∃ f : ↥(T ⊓ Subgroup.normalizer (normT T S : Set G)) →* DihedralGroup 4,
        Function.Surjective f ∧
          f.ker = (CFSG.Quasithin.thompsonJ S).subgroupOf
            (T ⊓ Subgroup.normalizer (normT T S : Set G))) ∧
      ∀ A₁ : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A₁ → A₁ ≠ pCoreOf 2 H →
        (∀ x ∈ normT T S, x ∉ S → A₁ ≠ conjR (pCoreOf 2 H) x) →
          Nat.card S ≤ Nat.card ↥(T ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) :
            Set G))))

theorem lemma245_3_iff : Lemma245_3 ↔
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
      (IsAltType L 3 ∨ (conjJoin S L = L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5))) →
        C61Concl T H S L :=
  Iff.rfl

@[expose] def C61SingleTail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) → ¬ IsAltType L 5 →
      ((IsAltType L 3 → Nat.card (blockD S L) ≤ 2 ^ 1) ∧
        ∀ n : ℕ, 1 < n → IsLin2Type L n → Nat.card (blockD S L) ≤ 2 ^ n) ∧
      ((S.relIndex T = 2 ∧ CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ T ∧
          (IsAltType L 3 → conjJoin S L = L →
            Nonempty (H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
        (IsAltType L 3 ∧ conjJoin S L = L ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
          IsDihedralOrSemidihedral T) ∨
        (((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) ∧
          CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ (normT T S) ∧
          (∃ f : ↥(T ⊓ Subgroup.normalizer (normT T S : Set G)) →* DihedralGroup 4,
            Function.Surjective f ∧
              f.ker = (CFSG.Quasithin.thompsonJ S).subgroupOf
                (T ⊓ Subgroup.normalizer (normT T S : Set G))) ∧
          ∀ A₁ : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A₁ → A₁ ≠ pCoreOf 2 H →
            (∀ x ∈ normT T S, x ∉ S → A₁ ≠ conjR (pCoreOf 2 H) x) →
              Nat.card S ≤ Nat.card ↥(T ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) :
                Set G))))

@[expose] def C61SingleAlternatives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) → ¬ IsAltType L 5 →
      ((S.relIndex T = 2 ∧ CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ T ∧
          (IsAltType L 3 → conjJoin S L = L →
            Nonempty (H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
        (IsAltType L 3 ∧ conjJoin S L = L ∧ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧
          IsDihedralOrSemidihedral T) ∨
        (((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) ∧
          CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ (normT T S) ∧
          (∃ f : ↥(T ⊓ Subgroup.normalizer (normT T S : Set G)) →* DihedralGroup 4,
            Function.Surjective f ∧
              f.ker = (CFSG.Quasithin.thompsonJ S).subgroupOf
                (T ⊓ Subgroup.normalizer (normT T S : Set G))) ∧
          ∀ A₁ : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian S A₁ → A₁ ≠ pCoreOf 2 H →
            (∀ x ∈ normT T S, x ∉ S → A₁ ≠ conjR (pCoreOf 2 H) x) →
              Nat.card S ≤ Nat.card ↥(T ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) :
                Set G))))

@[expose] def C61OtherCases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    (IsAltType L 3 ∨ (conjJoin S L = L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5))) →
      ¬ (conjJoin S L = L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) ∧
        ¬ IsAltType L 5) → C61Concl T H S L

end CFSG.QuasithinUnique
