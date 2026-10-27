module

public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem exists_mul_ne_mul_of_glaPComponent {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    by_contra hne
    exact h ⟨a, b, hne⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI := isQuasisimple_nontrivial hq
  have hQc : ∀ a b : PQuot p L, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm x y)
  have hbot : commutator (PQuot p L) = ⊥ :=
    (commutator_eq_bot_iff (G := PQuot p L)).2 (isMulCommutative_iff.2 hQc)
  obtain ⟨x, hx⟩ := exists_ne (1 : PQuot p L)
  have hmem : x ∈ (⊤ : Subgroup (PQuot p L)) := Subgroup.mem_top x
  rw [← hq.1, hbot, Subgroup.mem_bot] at hmem
  exact hx hmem

end CFSG.LocalAnalysis.GLTheoremA

end
