module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClLinear
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSymp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSp6
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOm12
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

namespace I1434.Cl

theorem i1434Cl_PSp_false {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSp n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂)
    (hd : Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 1 ∨
      Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 3) :
    False := by
  obtain ⟨-, -, -, F, _, _, _, e, A, hF4, hxA, hA5, hA1, hker⟩ := i1434Cl_PSp hm hℓ D
  obtain ⟨Q', hxQ', hd'⟩ := transport_lines e Q D.mem hd
  rw [hxA] at hxQ' hd'
  have h6 := dsp6_lines hF4 Q' A hxQ' hA5 hA1 hker
  omega

theorem i1434Cl_POmega_false {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel K t n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂)
    (hd : Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 1 ∨
      Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 3) :
    False := by
  obtain ⟨-, -, -, -, F, _, _, _, b, c, hF2, hirr, e, A, hxA, hA5, hA1, hker⟩ :=
    i1434Cl_POmega ht hm hℓ D
  obtain ⟨Q', hxQ', hd'⟩ := transport_lines e Q D.mem hd
  rw [hxA] at hxQ' hd'
  have h4 := domega12_lines hF2 hirr Q' A hxQ' hA5 hA1 hker
  omega

end I1434.Cl

open I1434.Cl in
theorem i1434ClassicalCase_holds : I1434ClassicalCase := by
  intro K _ _ t n ℓ f hm hℓ hs hna Q x J₁ J₂ D hd
  cases t
  · exact (i1434Cl_PSL hm hℓ D).elim
  · exact i1434Cl_PSU_iso hm hℓ D
  · exact (i1434Cl_PSp_false hm hℓ D hd).elim
  · exact (i1434Cl_POmega_false (Or.inl rfl) hm hℓ D hd).elim
  · exact (i1434Cl_POmega_false (Or.inr (Or.inl rfl)) hm hℓ D hd).elim
  · exact (i1434Cl_POmega_false (Or.inr (Or.inr rfl)) hm hℓ D hd).elim
  all_goals exact hm.2.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
