module

public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8B14A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag
import CFSG.ClassicalInvolution.Q3.Q3T8B14Core
public import CFSG.ClassicalInvolution.Q3.Q3T8B14C
public import CFSG.ClassicalInvolution.Q3.Q3T8B15
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

section Alpha

variable {G : Type} [Group G] [Finite G]

theorem alphaOf_eq_bot_of_psl4 {c z w : G} {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hBgen : B = Subgroup.closure ({z, w, c} : Set G))
    (hc1 : c ≠ 1) (hz1 : z ≠ 1) (hzc : z ≠ c) (hzC : z ∈ Subgroup.centralizer ({c} : Set G))
    (hwC : w ∈ Subgroup.centralizer ({c} : Set G)) (ψ : SL(4, 𝔽₃) →* OddQuot c)
    (hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃)) {y' : SL(4, 𝔽₃)} {Dm : GL (Fin 4) 𝔽₃}
    (hDm2 : Dm * Dm = 1) (hy'2 : y' * y' = 1)
    (hDy : (Dm : Matrix (Fin 4) (Fin 4) 𝔽₃) * (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) =
      (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) * Dm)
    (hzb : oddQuotMk c ⟨z, hzC⟩ ∈ ψ.range)
    (hzy : ∃ e' ∈ Subgroup.center (OddQuot c), oddQuotMk c ⟨z, hzC⟩ = ψ y' * e')
    (hw : ∀ g, oddQuotMk c ⟨w, hwC⟩ * ψ g * (oddQuotMk c ⟨w, hwC⟩)⁻¹ = ψ (conjSLAut Dm g))
    (hnormal : ψ.range.Normal) {L : Subgroup (OddQuot c)} (hL : L = ψ.range)
    (hmov : MovedByAll B c L) : alphaOf (inducedImage L (modOdd c B)) = ⊥ := by
  subst hL
  classical
  have hzB : z ∈ B := hBgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hcB : c ∈ B :=
    hBgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hmovz : ∃ y ∈ ψ.range, oddQuotMk c ⟨z, hzC⟩ * y ≠ y * oddQuotMk c ⟨z, hzC⟩ :=
    hmov _ (oddQuotMk_mem_modOdd hzB hzC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
  have hne : ∃ x ∈ inducedImage ψ.range (modOdd c B), x ≠ 1 :=
    ⟨toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, Subgroup.le_normalizer hzb⟩,
      ⟨_, oddQuotMk_mem_modOdd hzB hzC, rfl⟩, Q3T6D.inducedAut_ne_one hzC hzb hmovz⟩
  have hwN : oddQuotMk c ⟨w, hwC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnormal]
    exact Subgroup.mem_top _
  have hE : ∀ e ∈ modOdd c B, ∃ d ∈ ({1, oddQuotMk c ⟨z, hzC⟩, oddQuotMk c ⟨w, hwC⟩,
      oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨w, hwC⟩} : Set (OddQuot c)),
      ∃ e' ∈ Subgroup.center (OddQuot c), e = d * e' := by
    intro e he
    obtain ⟨d, hd, hdC, e', he', hde⟩ := exists_mul_central_of_mem_modOdd hB hBgen he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · refine ⟨1, by simp, e', he', ?_⟩
      rw [hde, show oddQuotMk c ⟨1, hdC⟩ = 1 from map_one _]
    · exact ⟨_, by simp, e', he', hde⟩
    · exact ⟨_, by simp, e', he', hde⟩
    · have h4 : oddQuotMk c ⟨z * w, hdC⟩ =
          oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨w, hwC⟩ := by
        rw [← map_mul]
        rfl
      exact ⟨oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨w, hwC⟩, by simp, e', he', by rw [hde, h4]⟩
  have hP := psl4Class_inducedImage ψ (modOdd c B) hDm2 hy'2 hDy hzb hzy hwN hw hE
  exact alphaOf_inducedImage_eq_bot_of_rows hB (PSL4Class ψ) (autOddFreeOn_psl4 ψ hker) hne hP

end Alpha

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
