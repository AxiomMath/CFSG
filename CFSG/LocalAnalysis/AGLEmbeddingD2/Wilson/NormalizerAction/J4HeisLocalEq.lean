module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Q11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalEq

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem inf_centralizer_eq_zpowers {G : Type*} [Group G] (Q : Subgroup G) (x y z : G)
    (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Q) (hzc : ∀ h ∈ Q, h * z = z * h)
    (hcen : ∀ g ∈ Q, g * x = x * g → g * y = y * g → ∃ k : ℕ, g = z ^ k) :
    Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro g ⟨hgQ, hgC⟩
    have h1 : x * g = g * x := Subgroup.mem_centralizer_iff.1 hgC x hx
    have h2 : y * g = g * y := Subgroup.mem_centralizer_iff.1 hgC y hy
    obtain ⟨k, hk⟩ := hcen g hgQ h1.symm h2.symm
    exact ⟨(k : ℤ), by simpa using hk.symm⟩
  · rw [Subgroup.zpowers_le]
    refine ⟨hz, ?_⟩
    show z ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hzc h hh

theorem inf_centralizer_Q11 :
    Q11 ⊓ Subgroup.centralizer (Q11 : Set J) = Subgroup.zpowers qz :=
  inf_centralizer_eq_zpowers (G := J) Q11 qx qy qz qx_mem qy_mem qz_mem
    (fun _ hh => qz_commute_of_mem hh) (fun _ hg h1 h2 => eq_pow_of_commute hg h1 h2)

theorem card_inf_centralizer_Q11 :
    Nat.card ↥(Q11 ⊓ Subgroup.centralizer (Q11 : Set J)) = 11 := by
  rw [inf_centralizer_Q11, Nat.card_zpowers, orderOf_qz]

theorem commutator_Q11_eq :
    ⁅Q11, Q11⁆ = Q11 ⊓ Subgroup.centralizer (Q11 : Set J) := by
  rw [inf_centralizer_Q11, ← Subgroup.map_subtype_commutator, commutator_Q11, center_Q11]

theorem heisLocalEq_Q11 :
    HeisLocalEq 11 Q11 :=
  ⟨card_Q11, centralizer_Q11_le, card_inf_centralizer_Q11, commutator_Q11_eq,
    fun _ hg => pow_eleven_of_mem hg, isSolvable_normalizer_Q11, torus_Q11⟩

theorem heisLocalEq_Q11Sylow :
    HeisLocalEq 11 (Q11Sylow : Subgroup J) := by
  rw [Q11Sylow_coe]
  exact heisLocalEq_Q11

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
