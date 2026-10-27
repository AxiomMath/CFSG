module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open Module CFSG.LinearAlgebra.SteinbergBQ

private theorem perm_pow_three_or_four {α : Type*} [Finite α] (hα : Nat.card α ≤ 4)
    (σ : Equiv.Perm α) : σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin (Fintype.card α)) :=
    Equiv.permCongrHom (Fintype.equivFin α)
  have key : ∀ n, n ≤ 4 → ∀ τ : Equiv.Perm (Fin n), τ ^ 3 = 1 ∨ τ ^ 4 = 1 := by
    intro n hn
    interval_cases n <;> decide
  rcases key _ (by rwa [← Nat.card_eq_fintype_card]) (φ σ) with h | h
  · exact Or.inl (φ.injective (by rw [map_pow, h, map_one]))
  · exact Or.inr (φ.injective (by rw [map_pow, h, map_one]))

theorem automizer_pow_three_or_four {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W]
    [Module K W] [Module.Finite K W] (hW : Module.finrank K W ≤ 4) {p : ℕ} [Fact p.Prime]
    (hpK : ¬ p ∣ Nat.card K) {P : Subgroup (Module.End K W)ˣ} (hP : IsPGroup p P)
    (hab : IsMulCommutative P) {g : (Module.End K W)ˣ}
    (hg : g ∈ Subgroup.normalizer (P : Set (Module.End K W)ˣ)) :
    (∀ x ∈ P, g ^ 3 * x * (g ^ 3)⁻¹ = x) ∨ (∀ x ∈ P, g ^ 4 * x * (g ^ 4)⁻¹ = x) := by
  classical
  set L := AlgebraicClosure K
  have : Finite (Module.End K W) := Module.finite_of_finite K
  have hpL : (p : L) ≠ 0 := by
    have : Fintype K := Fintype.ofFinite K
    intro hp0
    have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
      rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card,
        FiniteField.cast_card_eq_zero K, map_zero]
    have hcop : Nat.Coprime p (Nat.card K) :=
      (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpK
    exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hcop ((ringChar.spec L p).mp hp0)
      ((ringChar.spec L _).mp hK0))
  have hAchar : ((Nat.card P : ℕ) : L) ≠ 0 := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hpL
  have hAcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm : ∀ a ∈ (⊤ : Subgroup P), ∀ b ∈ (⊤ : Subgroup P),
      bcRep L P a * bcRep L P b = bcRep L P b * bcRep L P a := by
    intro a _ b _
    rw [← map_mul, ← map_mul, hab.is_comm.comm a b]
  have hchar : ((Nat.card (⊤ : Subgroup P) : ℕ) : L) ≠ 0 := by
    rwa [Subgroup.card_top]
  obtain ⟨hfin, hcard⟩ := CFSG.Walter.JT.finite_weights_and_card_le (bcRep L P) ⊤ hcomm hchar
  rw [Module.finrank_baseChange] at hcard
  have hker := ker_weightPermGL L hAcomm hAchar
  set g' : Subgroup.normalizer (P : Set (Module.End K W)ˣ) := ⟨g, hg⟩ with hg'
  have key : ∀ m : ℕ, weightPermGL L P g' ^ m = 1 → ∀ x ∈ P, g ^ m * x * (g ^ m)⁻¹ = x := by
    intro m hm x hx
    have h1 : g' ^ m ∈ (weightPermGL L P).ker := by rw [MonoidHom.mem_ker, map_pow, hm]
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    have h2 : x * g ^ m = g ^ m * x := by simpa [hg'] using h1 x hx
    rw [← h2, mul_inv_cancel_right]
  rcases perm_pow_three_or_four (hcard.trans hW) (weightPermGL L P g') with h | h
  · exact Or.inl (key 3 h)
  · exact Or.inr (key 4 h)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
