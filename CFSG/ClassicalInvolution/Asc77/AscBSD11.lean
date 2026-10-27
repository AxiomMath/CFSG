module

public import CFSG.ClassicalInvolution.Asc77.AscBSD10
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExcl

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem no_trialityD4_of_card {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    {z : G} (hS : BootSetting p f K z) (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (b : Fin D.card) (hD4 : D.tag b = .trialityD4) (hcard : 3 ≤ D.card) : False := by
  have hno := noFuzzyFrame hS
  let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hD4' : C.D.tag b = .trialityD4 := hD4
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hD4'] at h
    exact absurd h.1 (by decide)
  obtain ⟨j₀, hj₀, hK₀⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  have hcard' : 3 ≤ C.D.card := hcard
  obtain ⟨e, hej, heb⟩ := Fin.exists_ne_and_ne_of_two_lt j₀ b (by omega : 2 < C.D.card)
  obtain ⟨he, hall⟩ := nbar_eq_of_A1 C hno hb heb
  obtain ⟨me⟩ := exists_compMem C e
  have hme := hall me
  obtain ⟨hTcl, hTmod⟩ := classical_of_nbar_eq C he me hme
  have hTK : me.N ≠ C.K := twin_ne_K C hj₀ hK₀ hej he me hme
  obtain ⟨mb⟩ := exists_compMem C b
  obtain ⟨g, -, hg⟩ := exists_conj_of_compMem C mb
  have hKr : modOdd z C.K = (C.psi j₀).range := by rw [← hK₀, C.exactCore_K]
  obtain ⟨hK'tq, hK'cl, R₁, hR₁, himg₁, -⟩ :=
    exists_fund_conj_twin hno hb mb hg C.hK C.K_cl fun y hy =>
      nb_comm_of_range hj₀b mb (hKr ▸ hy)
  obtain ⟨hT'tq, hT'cl, R₂, hR₂, himg₂, -⟩ :=
    exists_fund_conj_twin hno hb mb hg me.hN.1 hTcl fun y hy =>
      nb_comm_of_range heb mb (hTmod ▸ hy)
  have hne : conjSub g⁻¹ me.N ≠ conjSub g⁻¹ C.K := fun h => hTK (conjSub_inj g⁻¹ h)
  exact false_of_trialityD4_sec hS.odd hS.five C.hΩ C.hc2 C.D b hD4' hK'tq hT'tq hK'cl hT'cl hne
    (by rw [himg₁]; exact Subgroup.map_le_range _ _)
    (by rw [himg₂]; exact Subgroup.map_le_range _ _)

theorem bootNoG2D4 (hTwin : BootNoG2Twin p f) (hSingle : BootNoG2D4Single p f) :
    BootNoG2D4 p f := by
  intro G _ _ _ K z hS D b hb
  by_cases hcard : 3 ≤ D.card
  · rcases hb with hG2 | hD4
    · exact hTwin G K z hS D b hG2 hcard
    · exact no_trialityD4_of_card hS D b hD4 hcard
  · exact hSingle G K z hS D b hb (by omega)

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
