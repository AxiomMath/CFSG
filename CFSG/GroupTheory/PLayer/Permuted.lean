module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma72

public section

namespace CFSG

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {G : Type} [Group G] [Finite G]

@[expose] def HasPermutedFixedComponent (p : ℕ) (X : Subgroup G) (x : G) : Prop :=
  ∃ I : Subgroup (PQuot p X),
    GLAPComponent p (CFSG.LocalAnalysis.GLTheoremA.fixedBar p X (Subgroup.zpowers x)) I

theorem glaPLayer_inf_centralizer_ne_bot_of_permuted {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} {x : G} (hx : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (X : Set G))
    (hfix : HasPermutedFixedComponent p X x) :
    GLAPLayer p (X ⊓ Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
  obtain ⟨I, hI⟩ := hfix
  have hFp : IsPGroup p (Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    change (x ^ k) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hFN : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.2 hxN
  have h := CFSG.LocalAnalysis.GLTheoremA.glaPLayer_inf_centralizer_ne_bot hp hFp hFN ⟨I, hI⟩
  have hz : Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [hz] at h

end CFSG

end
