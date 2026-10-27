module

public import CFSG.ClassicalInvolution.Q3.Q3SBasic
public import CFSG.ClassicalInvolution.Q3.Q3ExcComp
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem commute_of_component_of_member {Y G F : Type} [Group Y] [Finite Y] [Group G] [Field F]
    [Finite F] (h4 : 4 ≤ Nat.card F) {z : Y} {L : Subgroup Y} (hz : IsClassicalMember3 L z)
    {T : Subgroup Y} [hTn : T.Normal] (ε : T ≃* G) {τ : G} (hτ : ((ε.symm τ : T) : Y) = z)
    (Φ : SL(2, F) →* G) (hΦ : Function.Injective Φ) (hΦτ : ∀ B, Φ B * τ = τ * Φ B)
    (hnorm : ∀ c : G, c * τ = τ * c → ∀ B, ∃ B', c * Φ B * c⁻¹ = Φ B') :
    ∀ x ∈ L, ∀ B, x * ((ε.symm (Φ B) : T) : Y) = ((ε.symm (Φ B) : T) : Y) * x := by
  obtain ⟨j, hj⟩ : ∃ j : G →* Y, j = T.subtype.comp ε.symm.toMonoidHom := ⟨_, rfl⟩
  have hjapp : ∀ x, j x = ((ε.symm x : T) : Y) := fun x => by rw [hj]; rfl
  have hjinj : Function.Injective j := fun x y hxy => by
    rw [hjapp, hjapp] at hxy
    exact ε.symm.injective (Subtype.ext hxy)
  have hjτ : j τ = z := by rw [hjapp, hτ]
  simp only [← hjapp]
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup Y, C = Subgroup.centralizer ({z} : Set Y) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup Y, E = (j.comp Φ).range := ⟨_, rfl⟩
  have hEC : E ≤ C := by
    intro y hy
    rw [hEdef] at hy
    obtain ⟨B, rfl⟩ := hy
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← hjτ, ← map_mul,
      ← map_mul, hΦτ]
  have hET : E ≤ T := by
    intro y hy
    rw [hEdef] at hy
    obtain ⟨B, rfl⟩ := hy
    rw [MonoidHom.comp_apply, hjapp]
    exact (ε.symm _).2
  have hCmem : ∀ y ∈ C, y * z = z * y := fun y hy => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy
  have hEn : (E.subgroupOf (T ⊓ C)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, hEdef] at hn ⊢
    obtain ⟨B, hB⟩ := hn
    have hgC : (g : Y) * z = z * (g : Y) := hCmem _ g.2.2
    obtain ⟨c, hc⟩ : ∃ c : G, c = ε ⟨g, g.2.1⟩ := ⟨_, rfl⟩
    have hjc : j c = g := by rw [hjapp, hc, MulEquiv.symm_apply_apply]
    have hcτ : c * τ = τ * c := hjinj (by rw [map_mul, map_mul, hjc, hjτ, hgC])
    obtain ⟨B', hB'⟩ := hnorm c hcτ B
    refine ⟨B', ?_⟩
    rw [MonoidHom.comp_apply] at hB ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← hjc, ← hB, ← map_inv, ← map_mul, ← map_mul, hB']⟩
  have hDn : ((T ⊓ C).subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hTn.conj_mem _ hn.1 _, C.mul_mem (C.mul_mem g.2 hn.2) (C.inv_mem g.2)⟩⟩
  have hEsub : IsSubnormal E C := IsSubnormal.step (le_inf hET hEC) hEn
    (IsSubnormal.step inf_le_right hDn (IsSubnormal.refl C))
  have hEqs : CFSG.IsQuasisimple (E.subgroupOf C) := by
    have e1 : SL(2, F) ≃* E := by
      rw [hEdef]
      exact MonoidHom.ofInjective (hjinj.comp hΦ)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (Subgroup.subgroupOfEquivOfLe hEC).symm)
      (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hLC : L ≤ C := by rw [hCdef]; exact hz.le_centralizer
  have hLs : Group.IsSolvable (L.subgroupOf C) := by
    have := hz.isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLC).injective
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hLs
    (exc3_isSubnormal_subgroupOf (hCdef ▸ hz.subnormal))).1 (E.subgroupOf C)
    ⟨hEqs, exc3_isSubnormal_subgroupOf hEsub⟩
  intro x hx B
  have hBE : j (Φ B) ∈ E := by rw [hEdef]; exact ⟨B, rfl⟩
  have hm := Subgroup.commutator_mem_commutator
    (Subgroup.mem_subgroupOf.2 hBE : (⟨_, hEC hBE⟩ : C) ∈ E.subgroupOf C)
    (Subgroup.mem_subgroupOf.2 hx : (⟨x, hLC hx⟩ : C) ∈ L.subgroupOf C)
  rw [hcomm, Subgroup.mem_bot] at hm
  exact (congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hm)).symm

end CFSG.ClassicalInvolution.Q3.Q3T
