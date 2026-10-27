module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.AbelianAmbientTauTwoFitting
import CFSG.FeitThompson.Local.AbelianActionNormalFixedDisplacement

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem centralizerWithin_subgroupOf_eq {N P X : Subgroup G} (hX : X ≤ N) :
    (CFSG.FeitThompson.centralizerWithin P X).subgroupOf N
      = P.subgroupOf N ⊓ centralizer ((X.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  ext x
  constructor
  · intro hx
    rw [mem_subgroupOf, CFSG.FeitThompson.mem_centralizerWithin] at hx
    obtain ⟨hxP, hxc⟩ := hx
    exact ⟨mem_subgroupOf.2 hxP,
      mem_centralizer_iff.2 fun y hy => Subtype.ext (hxc y (mem_subgroupOf.1 hy))⟩
  · intro hx
    obtain ⟨h1, h2⟩ := hx
    rw [mem_subgroupOf, CFSG.FeitThompson.mem_centralizerWithin]
    refine ⟨mem_subgroupOf.1 h1, fun y hy => ?_⟩
    exact congrArg Subtype.val
      (mem_centralizer_iff.1 h2 ⟨y, hX hy⟩ (by simpa [mem_subgroupOf] using hy))

theorem commutator_le_centralizer_subgroupOf {P : Subgroup G}
    (h : ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤ centralizer (P : Set G)) :
    _root_.commutator ↥(normalizer (P : Set G)) ≤
      centralizer ((P.subgroupOf (normalizer (P : Set G)) :
        Subgroup ↥(normalizer (P : Set G))) : Set ↥(normalizer (P : Set G))) := by
  intro x hx
  have hxG : (x : G) ∈ ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  have hxc := h hxG
  rw [mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (mem_centralizer_iff.1 hxc y (mem_subgroupOf.1 hy))

theorem FBG_abelian_ambient_normalizer_fixed_displacement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_abelian_ambient_normalizer_fixed_displacement.{u} := by
  intro G _ _ hG M p A E P hsetup X hXN
  obtain ⟨-, hNF, hFC, -, -, -⟩ :=
    FBG_abelian_ambient_tau_two_fitting h₁ h₂ h₃ h₄ G hG M p A E P hsetup
  have hcomm : ⁅normalizer (P : Set G), normalizer (P : Set G)⁆ ≤ centralizer (P : Set G) :=
    hNF.trans hFC
  have hPnormal : (P.subgroupOf (normalizer (P : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have hN := commutator_le_centralizer_subgroupOf hcomm
  refine ⟨?_, ?_⟩
  · rw [centralizerWithin_subgroupOf_eq hXN]
    exact normal_inf_centralizer_of_commutator_le_centralizer hN _
  · rw [← commutator_subgroupOf le_normalizer hXN]
    exact normal_commutator_of_commutator_le_centralizer hN _

end

end CFSG.FeitThompson.Proofs
