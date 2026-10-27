module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypModule
public import Mathlib.FieldTheory.Finiteness

public section

open scoped IsMulCommutative

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {J : Type} [Group J] [Finite J]

theorem four_le_card_of_hyperplane_action {A : Type} [Group A] [Finite A] {p q n : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (hn : 2 ≤ n) [IsElementaryAbelian q A]
    [MulDistribMulAction J A] {U : Subgroup J} (hU : Nat.card U = p ^ n)
    (hexp : ∀ u ∈ U, u ^ p = 1) (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {σ : J}
    (hσ : MovesHyperplanes p U σ) (hnt : ∃ u ∈ U, ∃ a : A, u • a ≠ a) :
    q ^ 4 ≤ Nat.card A := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hpF : ((p : ℕ) : ZMod q) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  let ρ : J →* Module.End (ZMod q) (Additive A) :=
    Theory.Representation.ofElementaryAbelianAction (p := q) (A := J) (G := A)
  have hρ : ∀ (g : J) (a : A), ρ g (Additive.ofMul a) = Additive.ofMul (g • a) :=
    fun g a => Theory.Representation.ofElementaryAbelianAction_apply_ofMul g a
  obtain ⟨H, hHU, hHc, a, haH, u, hu, hua⟩ := HypModule.exists_hyperplane_fixed_not_fixed
    (HypModule.not_dvd_card_of_isElementaryAbelian hpq) hexp hcomm hnt
  have hHyp : HypModule.IsHyp p U H := ⟨hHU, hHc⟩
  have hne : CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModule.proj ρ U H ≠ 0 :=
    HypModule.hproj_ne_zero_of_fixed hpF ρ hU hHyp (v := Additive.ofMul a)
      (fun h hh => by rw [hρ, haH h hh])
      ⟨u, hu, fun h => hua (by rw [hρ] at h; exact Additive.ofMul.injective h)⟩
  have h4 := HypModule.four_le_finrank_hyp hpF ρ hU hcomm hσ hHyp hne
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive A)
  rw [Nat.card_zmod] at hcard
  have : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
  rw [this] at hcard
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : q.Prime).pos h4

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
