module

public import CFSG.ClassicalInvolution.Q3.Q3TY23
public import CFSG.ClassicalInvolution.Q3.Q3TY18
public import CFSG.ClassicalInvolution.Q3.Q3TY17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}


theorem exists_bridge_members_td5_3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {u}) (hO3 : LocalOddThreeFree3 Ω u)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaMinus 5).1
      (twinYModel 3 .POmegaMinus 5).2) Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember3 K z) (hs : IsClassicalMember3 β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes K N₂ ∧ Commutes β N₂ ∧ ¬ Commutes N₁ N₂ ∧
      N₁ ≠ N₂ ∧ ∃ n₂, IsClassicalMember3 N₂ n₂ ∧ conjSub n₂ N₁ = N₁ := by
  classical
  have hmod : twinYModel 3 .POmegaMinus 5 = (.POmegaPlus, 6) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := yData3_plus (by norm_num : 4 ≤ 6) hadm
  have : Finite (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc hK hshape
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K) R₀ R₁ :=
    e.modelAdj hY hΩ hex hP1 hO3 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hY hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c10, c11, c20, c21, hne, hnc, hnorm⟩ :
      ∃ T₁ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D,
        ∃ T₂ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D,
          Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧ T₁ ≠ T₂ ∧
          ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ :=
    exists_bridge_spin_plus3 hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N₁, hN₁, hN₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hN₂T⟩ := e.comp T₂ hT₂
  obtain ⟨n₂, hn₂⟩ := hΩ.classical N₂ hN₂.1
  have hwx : n₂ ∈ locLayer Ω u := le_centralizingLayer hN₂ hn₂.mem
  obtain ⟨r, hr, hrφ⟩ := e.exists_involution hY hN₂ hT₂ hN₂T hn₂
  have hrr : r⁻¹ = r := by
    refine inv_eq_of_mul_eq_one_right ?_
    have := pow_orderOf_eq_one r
    rwa [hr.2, pow_two] at this
  have hT₁r : T₁.map (MulAut.conj r).toMonoidHom = T₁ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hnorm r hr y hy
    · intro y hy
      refine ⟨r⁻¹ * y * r, ?_, ?_⟩
      · have := hnorm r hr y hy
        rw [hrr] at this ⊢
        exact this
      · show r * (r⁻¹ * y * r) * r⁻¹ = y
        group
  have hcomp : (MulAut.conj (e.φ r)).toMonoidHom.comp e.φ =
      e.φ.comp (MulAut.conj r).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hnu : n₂ * u * n₂⁻¹ = u := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn₂.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemc : conjSub n₂ N₁ ∈ centralizingMembers Ω {u} := by
    have := centralizingMembers_conj hΩ.conjInvariant n₂ u
    rw [hnu] at this
    rw [this]
    exact ⟨N₁, hN₁, rfl⟩
  have key : locImg Ω u (conjSub n₂ N₁) = locImg Ω u N₁ := by
    rw [locImg_conjSub_layer (Ω := Ω) (x := u) N₁ ⟨n₂, hwx⟩, hN₁T, Subgroup.map_map]
    have hφr : locMk Ω u ⟨n₂, hwx⟩ = e.φ r := hrφ.symm
    rw [hφr, hcomp, ← Subgroup.map_map, hT₁r]
  refine ⟨N₁, hN₁, N₂, hN₂, ?_, ?_, ?_, ?_, ?_, ?_, n₂, hn₂,
    locImg_injOn3 hΩ hex hP1 hO3 hmemc hN₁ key⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₁ hK hT₁ hN₁T hKR).mpr c10)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₁ hβ hT₁ hN₁T hβR).mpr c11)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₂ hK hT₂ hN₂T hKR).mpr c20)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₂ hβ hT₂ hN₂T hβR).mpr c21)
  · exact fun h => hnc ((e.commutes_iff hY hΩ hex hP1 hO3 hN₁ hN₂ hT₁ hN₁T hN₂T).mp h)
  · intro h
    exact hne (eq_of_map_eq_of_pow3 e.φ e.ker_le (e.ker_cop hY) (hY.pow3 T₁ hT₁)
      (hY.pow3 T₂ hT₂) (by rw [← hN₁T, ← hN₂T, h]))

end Layer

end CFSG.ClassicalInvolution.Q3.Q3TY
