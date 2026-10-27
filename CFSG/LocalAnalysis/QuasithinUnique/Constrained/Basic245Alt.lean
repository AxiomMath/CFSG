module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def C61Six (T H S L : Subgroup G) : Prop :=
  (S.relIndex T = 2 ∧ CFSG.Quasithin.thompsonJ S = CFSG.Quasithin.thompsonJ T ∧
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
            Set G)))

@[expose] def C61Lin2Alternatives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    conjJoin S L = L → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) → C61Six T H S L

theorem c61SingleAlternatives
    (h : C61Lin2Alternatives) : C61SingleAlternatives := by
  intro G _ _ T M H S L hcs hj hL _
  rcases hL with ⟨n, hn, hlin⟩ | h3
  · exact h G T M H S L hcs hj ⟨n, hn, hlin⟩
  · exact (singleA3Excluded G T M H S L hcs h3 hj).elim

end CFSG.QuasithinUnique
