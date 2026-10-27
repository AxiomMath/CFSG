module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneOddStabilizer
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv MulAction CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem catalog_of_le_range_of_kProper {D : Type} [Group D]
    (hK : Assembly.KProper Catalog D) {Y : Subgroup D} (hY : Y ≠ ⊤) {X : Type} [Group X]
    (φ : Y →* X) {S : Subgroup X} (hS : S ≤ φ.range) (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : Catalog S := by
  let e : ↥(S.subgroupOf φ.range) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS
  have : IsSimpleGroup ↥(S.subgroupOf φ.range) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnab
  exact SectionRank.catalog_of_mulEquiv e.symm
    (EvenSmallLie.CatalogOrders.catalog_of_kProper_of_le_quotient hK hY φ.rangeRestrict
      φ.rangeRestrict_surjective (S.subgroupOf φ.range)
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩)

section Certificates

theorem odd_stabilizer_two_transitive_kProper_of_dvd {D : Type} [Group D]
    (hK : Assembly.KProper Catalog D) {Y : Subgroup D} (hY : Y ≠ ⊤)
    {Ω : Type} [Finite Ω] (φ : Y →* Perm Ω) (N : Subgroup (Perm Ω)) (hN : N ≤ φ.range)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    {n : ℕ} (hn : 1 ≤ n) (hΩ : Nat.card Ω = 2 ^ n) (α : Ω)
    (hodd : Odd (Nat.card ↥(N ⊓ stabilizer (Perm Ω) α)))
    (hdvd : Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) ∣ (2 ^ n - 1) * n) :
    (∃ A : Subgroup (Perm Ω), A ≤ N ∧ (A.subgroupOf N).Normal ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 2 ^ n ∧
        ∀ β γ : Ω, ∃! a : A, (a : Perm Ω) β = γ) ∨
    (n = 3 ∧ Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) = 21 ∧ Nat.card N = 168 ∧
      IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧ ⁅N, N⁆ = N ∧
      StatedClassicalModel N .PSL 3 2 1 ∧ LieModel N .PSL 3 2 1) :=
  odd_stabilizer_two_transitive_catalog_of_dvd N h2 hn hΩ α hodd hdvd
    fun _ hSN _ hs hnab => catalog_of_le_range_of_kProper hK hY φ (hSN.trans hN) hs hnab

end Certificates

end CFSG.SeitzReduction.RankOne
