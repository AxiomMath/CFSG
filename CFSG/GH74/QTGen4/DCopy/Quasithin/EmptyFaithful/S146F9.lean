module

public import CFSG.Quasithin.EmptyFaithful.S146F9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Input14617UK_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13One T M H p H₂) →
          ∀ u : G, (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) → u ∉ quasithinOmegaOneCenter T →
            T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u → IsInvU T M H u →
              ∃ g' : G, u ∈ conjSubgroup (uK T M H) g' ∧
                ⁅uK T M H, conjSubgroup (uK T M H) g'⁆ ≠ ⊥

section Four2

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem input14617Four_of_F4 (h2 : Stage1461Two) (h4 : Stage1463Four) (iTrans : Input14617Trans)
    (iSing : Input14617Singular) (iUK : Input14617UK_F4) : Input14617Four_F4 := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hcase u huK hu huZ huT hInv
  have hp3 : p = 3 := hcase.elim (fun c => c.1) (fun c => c.1)
  have hOF : IsOFourPlusOn T M H := hcase.elim (fun c => c.2.1) (fun c => c.2.1)
  have hH : IsHTM T M H := hred.isHTM
  have h1 := stage1463_one_proof G T M S H hH u hInv
  have h4' := h4 G T M S H hH u hInv
  exact hdec.isI_of_inputs S h2 hred hp3
    (fun u u' hu huZ hu' hu'Z => iTrans G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec u u' hu huZ hu' hu'Z)
    (fun w hw hw1 hw2 => iSing G T M S H PQ p hred hp3 hOF H₀ H₁ H₂ t hdec w hw hw1 hw2)
    huK hu huZ ⟨h1.1, h1.2.1⟩ ⟨h4'.2.1, h4'.2.2⟩
    (iUK G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec hcase u hu huZ huT hInv)

end Four2

end CFSG.Quasithin
