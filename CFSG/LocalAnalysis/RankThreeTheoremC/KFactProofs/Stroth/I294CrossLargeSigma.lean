module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem I294CrossLarge.le_pRank_of_sylow_sigmaModel {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] {e a N : ℕ} (ha : 1 ≤ a) (hN : p ≤ N / e)
    (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) :
    p ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : 1 < (Nat.digits p (N / e)).length := by
    rw [Nat.lt_digits_length_iff hp.one_lt]
    simpa using hN
  have hne : N / e ≠ 0 := by have := hp.pos; omega
  let i₁ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
  have hi₁ : 1 ≤ (i₁ : ℕ) := by
    show 1 ≤ (Nat.digits p (N / e)).length - 1
    omega
  have hpos : 0 < (Nat.digits p (N / e))[i₁] := by
    have hlast := Nat.getLast_digit_ne_zero p hne
    have heq : (Nat.digits p (N / e))[i₁] =
        (Nat.digits p (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
      rw [List.getLast_eq_getElem]
      rfl
    rw [heq]
    exact Nat.pos_of_ne_zero hlast
  let j₁ : Fin (Nat.digits p (N / e))[i₁] := ⟨0, hpos⟩
  obtain ⟨E, hE, hEcard⟩ := SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
  obtain ⟨φ⟩ := h S
  let Ψ : wreathTower p (Multiplicative (ZMod (p ^ a))) i₁ →* G :=
    (S : Subgroup G).subtype.comp (φ.symm.toMonoidHom.comp (SigmaDich.sigmaEmbed p e a N i₁ j₁))
  have hΨ : Function.Injective Ψ :=
    Subtype.coe_injective.comp
      (φ.symm.injective.comp (SigmaDich.sigmaEmbed_injective p e a N i₁ j₁))
  exact CFSG.SectionRank.le_pRank hp.one_lt (le_top : E.map Ψ ≤ ⊤)
    ((isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE) (k := p)
    (by rw [Subgroup.card_map_of_injective hΨ]; exact hEcard)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
