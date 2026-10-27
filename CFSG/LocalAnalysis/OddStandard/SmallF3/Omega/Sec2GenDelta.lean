module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenChain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem invType_eq_two_minus {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [FiniteDimensional (ZMod 3) U] {R : QuadraticForm (ZMod 3) U} (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) U = 4) {b : OGroup R} (hbb : b * b = 1)
    (hbΩ : b ∈ omegaGroup hR) (hb1 : b ≠ 1) (hbπ : b ≠ piOrth R) : invType b = (2, -1) := by
  obtain ⟨hev, hsgn⟩ := (involution_mem_omegaGroup_iff hR hbb).mp hbΩ
  have h0 : invDim b ≠ 0 := fun h => hb1 ((invDim_eq_zero_iff hbb).mp h)
  have h4 : invDim b ≠ Module.finrank (ZMod 3) U := fun h =>
    hbπ ((invDim_eq_finrank_iff hbb).mp h)
  have hle := invDim_le b
  have h2 : invDim b = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  refine Prod.ext h2 ?_
  change invSign b = -1
  rw [hsgn, h2]
  decide

theorem blockInr_apply_fixSp {s : OGroup Q} (hs : s * s = 1)
    (b : OGroup (Q.restrict (commSp s))) {w : V} (hw : w ∈ fixSp s) :
    ((blockInr hs b : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w := by
  have happ := blockHom_apply hs (1, b) ⟨w, hw⟩ 0
  have h0 : w + ((0 : commSp s) : V) = w := by simp
  rw [blockInr_apply, ← h0]
  rw [happ]
  simp

theorem blockInr_apply_commSp {s : OGroup Q} (hs : s * s = 1)
    (b : OGroup (Q.restrict (commSp s))) (x : commSp s) :
    ((blockInr hs b : OGroup Q) : V ≃ₗ[ZMod 3] V) (x : V) =
      (((b : commSp s ≃ₗ[ZMod 3] commSp s) x : commSp s) : V) := by
  have happ := blockHom_apply hs (1, b) 0 x
  have h0 : (((0 : fixSp s) : V) + (x : V)) = (x : V) := by simp
  rw [blockInr_apply, ← h0, happ]
  simp

theorem exists_delta_data (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    {y : omegaGroup hQ} (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (4, 1)) :
    ∃ D : Set (omegaGroup hQ),
      (∀ d ∈ D, (d : OGroup Q) * d = 1 ∧ invType (d : OGroup Q) = (2, -1) ∧
        omegaToProj hQ d ∈ genPocketCore (omegaToProj hQ y) ∧
        ∀ w ∈ fixSp (y : OGroup Q), ((d : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w) ∧
      (∀ a ∈ commSp (y : OGroup Q), Q a ≠ 0 →
        ∃ d ∈ D, ((d : OGroup Q) : V ≃ₗ[ZMod 3] V) a = a) ∧
      (∀ c : ZMod 3, ∃ a ∈ commSp (y : OGroup Q), Q a = c) := by
  have hU4 : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp (y : OGroup Q))) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)) := by omega
  have hW : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)) := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) (y : OGroup Q)
    omega
  have hR := nondegenerate_restrict_commSp hQ hyy
  obtain ⟨κL, κR, hLΩ, hRΩ, hLinj, hRinj, hLπ, hRπ, hLn, hRn, hcomm, hrep, hfix, hne⟩ :=
    exists_plus4_block hR hU4 hs
  have hpL := genPocket_of_block hQ hyy hU hW κL hLΩ hLinj hLπ hLn
  have hpR := genPocket_of_block hQ hyy hU hW κR hRΩ hRinj hRπ hRn
  have hmemΩ : ∀ A B : SL2F3, blockInr hyy (κL A * κR B) ∈ omegaGroup hQ := fun A B =>
    blockInr_mem_omegaGroup hQ hyy hU (mul_mem (hLΩ A) (hRΩ B))
  refine ⟨{d | ∃ A B : SL2F3, A * A = sl2f3NegOne ∧ B * B = sl2f3NegOne ∧
    (d : OGroup Q) = blockInr hyy (κL A * κR B)}, ?_, ?_, ?_⟩
  · rintro d ⟨A, B, hA, hB, hd⟩
    have hbb : (κL A * κR B) * (κL A * κR B) = 1 := by
      calc (κL A * κR B) * (κL A * κR B) = κL A * (κR B * κL A) * κR B := by group
        _ = κL A * (κL A * κR B) * κR B := by rw [← hcomm A B]
        _ = (κL A * κL A) * (κR B * κR B) := by group
        _ = κL (A * A) * κR (B * B) := by rw [map_mul, map_mul]
        _ = 1 := by rw [hA, hB, hLπ, hRπ, piOrth_mul_self]
    obtain ⟨hb1, hbπ⟩ := hne A B hA hB
    have hbtype : invType (κL A * κR B) = (2, -1) :=
      invType_eq_two_minus hR hU4 hbb (mul_mem (hLΩ A) (hRΩ B)) hb1 hbπ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd, ← map_mul, hbb, map_one]
    · rw [hd, invType_blockInr hQ hyy hbb, hbtype]
    · have hdeq : d = ⟨blockInr hyy (κL A), blockInr_mem_omegaGroup hQ hyy hU (hLΩ A)⟩ *
          ⟨blockInr hyy (κR B), blockInr_mem_omegaGroup hQ hyy hU (hRΩ B)⟩ := by
        apply Subtype.ext
        rw [hd, map_mul]
        rfl
      have hL : omegaToProj hQ ⟨blockInr hyy (κL A),
          blockInr_mem_omegaGroup hQ hyy hU (hLΩ A)⟩ ∈ genPocketCore (omegaToProj hQ y) :=
        Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (q8SL.map _)
          (Subgroup.mem_iSup_of_mem hpL ⟨A, mem_q8SL_of_mul_self hA, rfl⟩))
      have hR' : omegaToProj hQ ⟨blockInr hyy (κR B),
          blockInr_mem_omegaGroup hQ hyy hU (hRΩ B)⟩ ∈ genPocketCore (omegaToProj hQ y) :=
        Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (q8SL.map _)
          (Subgroup.mem_iSup_of_mem hpR ⟨B, mem_q8SL_of_mul_self hB, rfl⟩))
      rw [hdeq, map_mul]
      exact mul_mem hL hR'
    · intro w hw
      rw [hd]
      exact blockInr_apply_fixSp hyy _ hw
  · intro a ha hQa
    obtain ⟨A, B, hA, hB, hfixa⟩ := hfix ⟨a, ha⟩ hQa
    refine ⟨⟨blockInr hyy (κL A * κR B), hmemΩ A B⟩, ⟨A, B, hA, hB, rfl⟩, ?_⟩
    have h1 := blockInr_apply_commSp hyy (κL A * κR B) ⟨a, ha⟩
    have h2 := congrArg Subtype.val hfixa
    exact h1.trans (by simpa using h2)
  · intro c
    obtain ⟨a, ha⟩ := hrep c
    exact ⟨a, a.2, ha⟩

end CFSG.OddStandard.SmallF3.Omega
