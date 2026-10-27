module

public import CFSG.Quasithin.EmptyFaithful.S146F14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Final

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem stage14616_of_named_inputs_F4 (h14 : Stage14614_F4) (h15 : Stage14615_F4) (iNorm : Input14616Norm)
    (iWeak : Input14616Weak) (iOne : Input14616One) : Stage14616_F4 := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec
  have hp3 : p = 3 := h15 G T M S H PQ p hred hmax
  refine ⟨hdec.relIndex_inf_normalizer_eq_two hred, ?_⟩
  have hAt := (stage14614At_iff T H p).mp (stage14614At_of_F4 h14 S hred hmax)
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hTN := hdec.le_normalizer_inf hred
  rcases hAt with c1 | c2 | c3 | c4
  · exact hdec.normalizer_eq_of_case_one S hred hp3 c1
      (iOne G T M S H PQ p hred hp3 c1 H₀ H₁ H₂ t hdec)
  · refine le_antisymm ?_ (le_inf hTN hTG)
    have hH := iWeak G T M S H PQ p hred hp3 (Or.inl c2) H₀ H₁ H₂ t hdec
    have hNH := iNorm G T M S H PQ p hred H₀ H₁ H₂ t hdec
    exact fun x hx => hNH.le ⟨hx.1, hH hx⟩
  · refine le_antisymm ?_ (le_inf hTN hTG)
    have hH := iWeak G T M S H PQ p hred hp3 (Or.inr c3) H₀ H₁ H₂ t hdec
    have hNH := iNorm G T M S H PQ p hred H₀ H₁ H₂ t hdec
    exact fun x hx => hNH.le ⟨hx.1, hH hx⟩
  · exact absurd c4.1 (by omega)

end Final

end CFSG.Quasithin
