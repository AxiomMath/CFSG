module

public import CFSG.ClassicalInvolution.RouteD.TWEBigLift
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Stmt
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.ModelFacts.Orth15SylowFrame
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Balance.WeakFrameExistsBasic
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Balance.WeakFrame

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.Big

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

set_option linter.unusedSectionVars false

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem XCtx.z_not_mem_map_fund (C : XCtx p f Ω z) (j : Fin C.D.card)
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    oddQuotMk z ⟨z, XCtx.hzC z⟩ ∉ R.map (C.psi j) := by
  intro hmem
  have hzC := XCtx.hzC z
  obtain ⟨r, hrR, hr⟩ := hmem
  have hr1 : r = 1 := by
    refine CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j)
      (C.D.exp j) (C.D.isFundTag j) (C.D.admissible j) hj R hR r hrR fun y => C.psi_ker j ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hr]
    have := oddQuotMk_central hzC (C.psi j y)
    calc oddQuotMk z ⟨z, hzC⟩ * C.psi j y * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹
        = (C.psi j y * oddQuotMk z ⟨z, hzC⟩) * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹ := by
          rw [this]
      _ = 1 := by group
  rw [hr1, map_one] at hr
  exact C.hKz.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) hr.symm))

namespace TwinShapeCtx

variable (C : TwinShapeCtx p f Ω z)

include C

theorem listed_not_A1 : ¬ (C.D.tag C.i₁ = .PSL ∧ C.D.rank C.i₁ = 2) := by
  rintro ⟨h1, h2⟩
  rcases C.listed with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [h1] at h
    cases h
  · rw [h2] at h
    cases h
  all_goals (rw [h1] at h; cases h)

end TwinShapeCtx

end Basic

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtx p f Ω z} (L : TwinLift C)

namespace TwinLift

theorem t_ne_z : L.t ≠ z := by
  intro h
  have hmem := oddQuotMk_mem_modOdd (C.involution_mem_exactCore L.hJ L.hJt) L.ht
  rw [L.hJimg] at hmem
  apply XCtx.z_not_mem_map_fund C.toXCtx C.i₁ C.listed_not_A1 L.hR₁
  have : (⟨L.t, L.ht⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = ⟨z, XCtx.hzC z⟩ :=
    Subtype.ext h
  rwa [this] at hmem

theorem T₁_ne_K₁ (S : C.Spec) : L.T₁ ≠ L.K₁ := fun h =>
  C.rng_ne S (by rw [← L.hK₁img, ← L.hT₁img, h])

theorem frameData (S : C.Spec) : TwinFrameData Ω L.K₁ L.T₁ z L.u L.J L.t where
  mem := L.hK₁
  hz := L.hK₁z
  hK' := ⟨L.hT₁, z, L.hK₁z, L.hT₁z⟩
  hne := L.T₁_ne_K₁ S
  hu := L.hu_mem
  hu2 := L.hu2
  hu1 := L.hu1
  huz := L.huz
  hJ := ⟨L.hJ.1, fun M hM => by
    obtain ⟨hMΩ, w, hwK, hwM⟩ := hM
    have hwz : w = z := (L.hK₁z.eq hwK).symm
    subst hwz
    have hne : L.J ≠ M := by
      intro hJM
      rw [← hJM] at hwM
      exact L.t_ne_z ((ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt).eq hwM)
    exact mem_omegaNbr_of_trivialOnQuot C.hp C.hq C.hΩ hMΩ hwM L.hJ.1 hne L.hJ.2⟩
  ht := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt
  htu := L.hut

end TwinLift

end Frame

end CFSG.ClassicalInvolution.RouteD.TWE.Big
