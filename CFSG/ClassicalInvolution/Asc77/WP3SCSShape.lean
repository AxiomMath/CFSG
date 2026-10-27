module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import CFSG.ClassicalInvolution.Asc77.WP3SCSLift

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Shape

variable {p f : ℕ} [Fact p.Prime]

theorem TwinShapeData.exists_big {X : Type} [Group X] {Φ : Set (Subgroup X)}
    {D : LieSystemData p f X Φ} (hD : TwinShapeData D) :
    ∃ a₁ : Fin D.card, ListedTwin (D.tag a₁) (D.rank a₁) ∧
      ¬ (D.tag a₁ = .PSL ∧ D.rank a₁ = 2) ∧
      ∀ j, j ≠ a₁ → (D.tag j = .PSL ∧ D.rank j = 2) := by
  obtain ⟨hcard, a₀, a₁, a₂, h01, h12, h02, t0, r0, t2, r2, hlist⟩ := hD
  refine ⟨a₁, hlist, ?_, fun j hj => ?_⟩
  · rintro ⟨h1, h2⟩
    rcases hlist with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h1] at h
      cases h
    · omega
    all_goals (rw [h1] at h; cases h)
  · rcases eq_cases_of_card_three hcard h01 h12 h02 j with h | h | h
    · rw [h]
      exact ⟨t0, r0⟩
    · exact absurd h hj
    · rw [h]
      exact ⟨t2, r2⟩

end Shape

section Zbar

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem XCtx.A1_contains_zbar (X : XCtx p f Ω z) (hD : TwinShapeData X.D) {K' : Subgroup G}
    (hK' : K' ∈ Ω) (hK'z : IsClassicalMember p f K' z) (hne : K' ≠ X.K) :
    ∀ j : Fin X.D.card, (X.D.tag j = .PSL ∧ X.D.rank j = 2) →
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (X.psi j).range := by
  classical
  obtain ⟨a₁, -, hna, hothers⟩ := hD.exists_big
  have hzC := XCtx.hzC z
  obtain ⟨j₀, hj₀, hjK⟩ := X.exists_A1_of_K
  obtain ⟨j₂, hj₂, hjK'⟩ := X.exists_A1_of_member hK' hK'z
  have hzK : oddQuotMk z ⟨z, hzC⟩ ∈ (X.psi j₀).range := by
    rw [← hjK]
    exact oddQuotMk_mem_modOdd (X.involution_mem_exactCore X.K_tq X.K_cl) hzC
  have hzK' : oddQuotMk z ⟨z, hzC⟩ ∈ (X.psi j₂).range := by
    rw [← hjK']
    exact oddQuotMk_mem_modOdd hK'z.mem hzC
  have hne' : j₀ ≠ j₂ := by
    intro h
    subst h
    have hKz : IsUniqueInvolution X.K z := X.hKz
    have hK'z' : IsUniqueInvolution K' z := ConnectedA2.isUniqueInvolution_of_isClassicalMember
      X.hp X.hq hK'z
    have hc := X.hΩ.comm_le_oddCore_of_twin X.hK hK' hne.symm hKz hK'z'
    refine X.range_not_comm_of_A1 j₀ hj₀ hzK ?_
    intro a ha b hb
    rw [← hjK, X.exactCore_K] at ha
    rw [← hjK'] at hb
    obtain ⟨k, hk, rfl⟩ := (mem_modOdd_iff).mp ha
    obtain ⟨y, hy, rfl⟩ := (mem_modOdd_iff).mp hb
    have hcomm : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ ⁅X.K, K'⁆ :=
      Subgroup.commutator_mem_commutator hk hy
    have hO : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ oddCoreIn (Subgroup.centralizer
        ({z} : Set G)) :=
      oddCoreIn_le_of_isSubnormal X.K_cl.subnormal (hc hcomm).1
    obtain ⟨w, hw, hwc⟩ := hO
    have hweq : w = k * y * k⁻¹ * y⁻¹ := Subtype.ext hwc
    have h1 : oddQuotMk z w = 1 := oddQuotMk_eq_one_iff.mpr hw
    rw [hweq, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  intro j hj
  have hj1 : j ≠ a₁ := fun h => hna (h ▸ hj)
  have hne0 : j₀ ≠ a₁ := fun h => hna (h ▸ hj₀)
  have hne2 : j₂ ≠ a₁ := fun h => hna (h ▸ hj₂)
  have hcard := (show X.D.card = 3 from by
    obtain ⟨hcard, -⟩ := hD
    exact hcard)
  have hlt := j.2
  have hlt0 := j₀.2
  have hlt2 := j₂.2
  have hlt1 := a₁.2
  have n1 : j.val ≠ a₁.val := fun e => hj1 (Fin.ext e)
  have n2 : j₀.val ≠ a₁.val := fun e => hne0 (Fin.ext e)
  have n3 : j₂.val ≠ a₁.val := fun e => hne2 (Fin.ext e)
  have n4 : j₀.val ≠ j₂.val := fun e => hne' (Fin.ext e)
  have hcases : j = j₀ ∨ j = j₂ := by
    by_contra hcon
    push Not at hcon
    have a1 : j.val ≠ j₀.val := fun e => hcon.1 (Fin.ext e)
    have a2 : j.val ≠ j₂.val := fun e => hcon.2 (Fin.ext e)
    omega
  rcases hcases with rfl | rfl
  · exact hzK
  · exact hzK'

end Zbar

end CFSG.ClassicalInvolution.Asc77
