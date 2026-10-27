module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4Edge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

namespace MuTab

section G2D4

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem dEdgeless_of_g2d4 {t : StatedLieTag} {k : ℕ} (M : Ih8Model p f Ω t k e)
    (hΩ : HypOmegaMod p f Ω) (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (ht : t = .G2 ∨ t = .trialityD4) : DEdgeless Ω := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have hsurj : Function.Surjective M.ψ := M.surj
  rcases ht with ht2 | ht2
  · subst ht2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    subst hk
    have hqe : 5 ≤ p ^ e := by
      rcases M.exp_eq with h' | ⟨h', -⟩
      · rw [h']
        exact hq
      · exact absurd h' (by decide)
    exact dEdgeless_of_model M.ψ hinj hsurj M.mem_iff htrans fun Q hQ =>
      eq_of_isMaxPGroup_le_normalizer_g2 hp2 hqe M.admissible Q (M.cls_sub hQ)
  · subst ht2
    have hk : k = 0 := M.admissible.2.2
    subst hk
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hq
    have h60 : ∀ Q ∈ M.cls, 60 ≤ Nat.card Q := by
      intro Q hQ
      obtain ⟨z, hz⟩ := hΩ.classical _ (M.map_mem hQ)
      obtain ⟨φ⟩ := hz.nonempty_equiv
      have h1 : Nat.card SL(2, GaloisField p f) ≤ Nat.card (Q.map M.ψ) :=
        calc Nat.card SL(2, GaloisField p f)
            = Nat.card ((Q.map M.ψ) ⧸ classicalInvolutionOddCore (Q.map M.ψ)) :=
              Nat.card_congr φ.toEquiv.symm
          _ ≤ Nat.card (Q.map M.ψ) :=
              Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
      rw [Subgroup.card_map_of_injective hinj, RouteD.G2D4.card_sl2_field,
        GaloisField.card p f hf] at h1
      have h25 : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      have h24 : 24 ≤ (p ^ f) ^ 2 - 1 := by omega
      calc 60 ≤ 5 * 24 := by norm_num
        _ ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul hq h24
        _ ≤ Nat.card Q := h1
    exact dEdgeless_of_model M.ψ hinj hsurj M.mem_iff htrans fun Q hQ =>
      eq_of_isMaxPGroup_le_normalizer_td4 hp2 M.admissible Q (M.cls_sub hQ) (h60 Q hQ)

theorem muKind_g2 (π : Bool) : muKind π .G2 0 = .s3 := by cases π <;> simp [muKind]

theorem muKind_trialityD4 (π : Bool) : muKind π .trialityD4 0 = .s3 := by
  cases π <;> simp [muKind]

end G2D4

end MuTab

end CFSG.ClassicalInvolution.Asc77
