module

public import CFSG.ClassicalInvolution.Q3.Q3TIYQSL
public import CFSG.ClassicalInvolution.Q3.Q3TIYPRank
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TIV
  CFSG.ClassicalInvolution.RouteD.TWY CFSG.ClassicalInvolution.RouteD.TwinY


@[expose] def TwinYSl4Small3 : Prop :=
  OddThreeFreeInput → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, LocalOddCentral (conjClass3 K) {e.u} →
            LocalOddThreeFree3 (conjClass3 K) e.u →
              ∀ (ι : Type) [Finite ι]
                (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)),
                Nat.card ι = 1 → ∀ i : ι, ∀ (t' : StatedLieTag) (n' : ℕ),
                  D.kind i = CompData.model t' n' →
                    ((t' = .PSp ∧ n' = 2) ∨ (t' = .PSL ∧ n' = 4) ∨ (t' = .PSU ∧ n' = 4) ∨
                      (t' = .POmegaOdd ∧ n' = 3)) → False

theorem twinYModel3_psl4 : twinYModel 3 .PSL 4 = (.POmegaMinus, 4) := by
  simp [twinYModel]

theorem twinYRank3_sl4_of_small (hSmall : TwinYSl4Small3) : TwinYRank3On TwinRowSL4 := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e hP1u hO3u ι _ D hcard i t' n' hk
    hrow'
  obtain ⟨rfl, rfl⟩ := hP
  classical
  obtain ⟨J, t, A, hJ, hJK, hJT, hJu, hJ₂u, hcount⟩ := rank_setup3_sl4 h3 hnab hR hshape hT clsT e
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hadm' := twinRow_admissible3 hrow'
  obtain ⟨hft, hG2, hD4, -, -⟩ := twinRow_tag_facts3 hrow'
  have hsc := EX.singleClass_of_kind hk hft hadm' hG2 hD4
  have hpc := EX.powCop3_of_kind hk hft hadm' hG2 hD4
  obtain ⟨R₀, hR₀, -, hcardR⟩ := exists_corr_commuting3 hΩ hex hP1u hO3u D i hone hsc hpc hJu
  rw [hcount] at hcardR
  obtain ⟨R₀', hR₀', hcard'⟩ := card_of_kind hk hR₀ hcardR
  rw [twinYModel3_psl4]
  have hS := hSmall h3 G hnab K z hR hshape T hT clsT e hP1u hO3u ι D hcard i
  rcases hrow' with ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, -, hk'⟩ := layerCount3_plus hadm' hR₀' hcard'
    have h0 : framesPlus 3 j = 0 := by omega
    exact (framesPlus_ne_zero (q := 3) (by norm_num) j h0).elim
  · exact (hS _ _ hk (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
  · obtain ⟨j, hj, hk'⟩ := layerCount3_odd hadm' hR₀' hcard'
    rcases j with _ | j
    · exact (hS _ _ hk (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))).elim
    · have h0 : cOdd 3 (j + 1) = 0 := by omega
      exact (framesOdd_ne_zero (q := 3) (by norm_num) j h0).elim
  · exact (hS _ _ hk (Or.inl ⟨rfl, rfl⟩)).elim
  · obtain ⟨j, hj, hk'⟩ := layerCount3_minus hadm' hR₀' hcard'
    rcases j with _ | j
    · exact ⟨rfl, by show n' = 4; omega⟩
    · have h0 : cMinus 3 (j + 1) = 0 := by omega
      exact (framesMinus_ne_zero (q := 3) (by norm_num) j h0).elim
  · exact (hS _ _ hk (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).elim

theorem twinYType3On_sl4_of_small (h3 : OddThreeFreeInput) (hSmall : TwinYSl4Small3) :
    Q3TY.TwinYType3On TwinRowSL4 :=
  twinYType3On_of_inputs h3 twinYNoCentral3_sl4 twinYKind3_sl4 (twinYRank3_sl4_of_small hSmall)

end CFSG.ClassicalInvolution.Q3.Q3TIY
