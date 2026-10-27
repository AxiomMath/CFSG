module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def conjR (X : Subgroup G) (g : G) : Subgroup G :=
  X.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def blockU0 (S L : Subgroup G) : Subgroup G :=
  conjJoin S (blockU L)

@[expose] def blockD (S L : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.centralizer (conjJoin S L : Set G)

@[expose] def baumD (S L : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.baum S ⊓ Subgroup.centralizer (conjJoin S L : Set G)

@[expose] def normT (T S : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.normalizer (S : Set G)

@[expose] def IsDihedralOrSemidihedral (P : Subgroup G) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m))) ∨
    ∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* CFSG.Open.SemidihedralGroup n)

@[expose] def Lemma244 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ∀ S₀ : Subgroup G, S₀ ≠ ⊥ → S₀ ≤ S → H ≤ Subgroup.normalizer (S₀ : Set G) →
      T ⊓ Subgroup.normalizer (S₀ : Set G) = S

@[expose] def Lemma245_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    blockU0 S L = pCoreOf 2 (conjJoin S L)

@[expose] def Lemma245_C55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S ≠ M₀ → M₀ ≤ Subgroup.normalizer (S : Set G) →
      ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H

@[expose] def Lemma245_C56_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ∀ M₀ : Subgroup G, S ≤ M₀ → M₀ ≤ T → S.relIndex M₀ = 2 →
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

@[expose] def Lemma245_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    (IsAltType L 3 ∨ (conjJoin S L = L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5))) →
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

@[expose] def Lemma246 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (conjJoin S L : Set G)

@[expose] def Lemma246Chi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) →
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (L : Set G)

end CFSG.QuasithinUnique
