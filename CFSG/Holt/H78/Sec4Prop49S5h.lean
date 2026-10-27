module

public import CFSG.Holt.H78.Sec4Prop49S5f
public import CFSG.Holt.H78.Sec4Prop49S5g
public import CFSG.Holt.H78.Sec4Prop49End

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

namespace P49Config

section CoordLine

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

theorem P95Data.Torus.V_le_lineKer (P : C.P95Data) (h : C.P95) (T : P.Torus) :
    T.V ≤ lineKer G C.line α C.line := fun _ heV =>
  mem_lineKer.mpr ⟨P.E_le_K (T.V_le_E heV), fun _ hA hAL =>
    (mem_fixingSubgroup_iff G).mpr (P.mem_Wl.mp (P95Data.Torus.V_le_Wl P h T hA hAL heV)).2⟩

theorem P95.exists_mem_lineKer_smul_ne (h : C.P95) {y : Ω} (hy : y ∈ C.line) (hyα : y ≠ α) :
    ∃ k ∈ lineKer G C.line α C.line, k • y ≠ y := by
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨T⟩ := P.nonempty_torus h
  obtain ⟨zt, hzt, htz⟩ := h.exists_lineActs_rootZ (Subgroup.subset_closure P.t_mem)
  obtain ⟨e, heV, hez⟩ := T.exists_mem_V_lineActs h hzt
  refine ⟨e, P95Data.Torus.V_le_lineKer P h T heV, ?_⟩
  obtain ⟨ψ, rfl⟩ := hy
  rw [hez ψ, ← htz ψ]
  exact fun h1 => hyα (P.t_mem.1.2.unique h1 P.t_mem.2)

theorem P95.exists_mem_lineGroup_lineActs (h : C.P95) {m : Equiv.Perm (C.D.Ψc C.i)}
    (hm : m ∈ C.D.M C.i) : ∃ g ∈ lineGroup G C.line C.line, C.LineActs g m := by
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨T⟩ := P.nonempty_torus h
  set H : Subgroup (Equiv.Perm (C.D.Ψc C.i)) :=
    { carrier := {π | ∃ g ∈ lineGroup G C.line C.line, C.LineActs g π}
      mul_mem' := fun {a b} ⟨g, hg, hga⟩ ⟨g', hg', hgb⟩ => ⟨g * g', mul_mem hg hg', hga.mul hgb⟩
      one_mem' := ⟨1, one_mem _, C.lineActs_one⟩
      inv_mem' := fun {a} ⟨g, hg, hga⟩ => ⟨g⁻¹, inv_mem hg, hga.inv⟩ }
  have hmemH : ∀ {π}, π ∈ H ↔ ∃ g ∈ lineGroup G C.line C.line, C.LineActs g π := Iff.rfl
  set N : Subgroup (C.D.M C.i) := H.subgroupOf (C.D.M C.i)
  have hN : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨g, hg, hgn⟩ := hmemH.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨c, -, hcx⟩ := C.exists_lineActs_of_mem x.2
    refine Subgroup.mem_subgroupOf.mpr (hmemH.mpr ⟨c * g * c⁻¹, ?_, ?_⟩)
    · have := conj_mem_lineGroup (Λ := C.line) hg c
      rwa [hcx.smul_line] at this
    · exact (hcx.mul hgn).mul hcx.inv
  obtain ⟨zt, hzt, htz⟩ := h.exists_lineActs_rootZ (Subgroup.subset_closure P.t_mem)
  obtain ⟨e, heV, hez⟩ := T.exists_mem_V_lineActs h hzt
  have hztM : zt ∈ C.D.M C.i :=
    seRadical_le (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hzt)
  have hztN : (⟨zt, hztM⟩ : C.D.M C.i) ∈ N :=
    Subgroup.mem_subgroupOf.mpr (hmemH.mpr ⟨e, lineKer_le_lineGroup C.α_mem_line
      (P95Data.Torus.V_le_lineKer P h T heV), hez⟩)
  have hzt1 : zt ≠ 1 := by
    rintro rfl
    have h1 := htz.smul_β
    rw [Equiv.Perm.one_apply, C.lpt_coord_b] at h1
    exact C.ne (P.t_mem.1.2.unique h1 P.t_mem.2).symm
  have hNtop : N = ⊤ := by
    have := C.D.isSimpleGroup_M C.i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · rw [hbot] at hztN
      exact absurd (congrArg Subtype.val ((Subgroup.mem_bot).mp hztN)) hzt1
    · exact htop
  have hmN : (⟨m, hm⟩ : C.D.M C.i) ∈ N := hNtop ▸ Subgroup.mem_top _
  exact hmemH.mp (Subgroup.mem_subgroupOf.mp hmN)

theorem P95.exists_mem_lineGroup_smul_eq (h : C.P95) {y z : Ω} (hy : y ∈ C.line)
    (hz : z ∈ C.line) : ∃ m ∈ lineGroup G C.line C.line, m • y = z := by
  obtain ⟨ψ, rfl⟩ := hy
  obtain ⟨ψ', rfl⟩ := hz
  obtain ⟨m, hm, hmψ⟩ := C.exists_mem_M_apply_eq' ψ ψ'
  obtain ⟨g, hg, hgm⟩ := h.exists_mem_lineGroup_lineActs hm
  exact ⟨g, hg, by rw [hgm ψ, hmψ]⟩

theorem P95.isCoordLine (h : C.P95) : IsCoordLine G C.line where
  jClosed g := (C.isJClosed_line h.setting h.transitive).smul g
  eq_of_mem_of_mem := by
    intro A B hA hB x y hxA hxB hyA hyB hxy
    have htr := h.setting.star.isPretransitive
    obtain ⟨g, hg⟩ := exists_smul_eq G α x
    have hgx : g⁻¹ • x = α := by rw [inv_smul_eq_iff, hg]
    have hA' : g⁻¹ • A ∈ linesThrough G C.line α := by
      have := smul_mem_linesThrough (⟨hA, hxA⟩ : A ∈ linesThrough G C.line x) g⁻¹
      rwa [hgx] at this
    have hB' : g⁻¹ • B ∈ linesThrough G C.line α := by
      have := smul_mem_linesThrough (⟨hB, hxB⟩ : B ∈ linesThrough G C.line x) g⁻¹
      rwa [hgx] at this
    have hyα : g⁻¹ • y ≠ α := fun h1 => hxy (by rw [← hg, ← h1, smul_inv_smul])
    have e := h.eq_of_mem_of_mem hA' hB' (Set.smul_mem_smul_set hyA)
      (Set.smul_mem_smul_set hyB) hyα
    calc A = g • g⁻¹ • A := (smul_inv_smul g A).symm
      _ = g • g⁻¹ • B := by rw [e]
      _ = B := smul_inv_smul g B
  lineFix_eq_bot := h.lineFix_eq_bot
  exists_smul_ne := by
    intro x A hA y hy hyx
    obtain ⟨g, hgα, hgA⟩ := exists_smul_α_eq C hA
    have hy' : g⁻¹ • y ∈ C.line := by
      rw [← hgA] at hy
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hy
    have hy'α : g⁻¹ • y ≠ α := fun h1 => hyx (by rw [← hgα, ← h1, smul_inv_smul])
    obtain ⟨k, hk, hky⟩ := h.exists_mem_lineKer_smul_ne hy' hy'α
    refine ⟨g * k * g⁻¹, ?_, fun h1 => hky ?_⟩
    · have := conj_mem_lineKer hk g
      rwa [hgα, hgA] at this
    · rw [mul_smul, mul_smul, ← eq_inv_smul_iff] at h1
      exact h1
  exists_smul_eq := by
    rintro A ⟨g, rfl⟩ y z hy hz
    obtain ⟨m, hm, hmyz⟩ := h.exists_mem_lineGroup_smul_eq
      (Set.mem_smul_set_iff_inv_smul_mem.mp hy) (Set.mem_smul_set_iff_inv_smul_mem.mp hz)
    refine ⟨g * m * g⁻¹, conj_mem_lineGroup hm g, ?_⟩
    rw [mul_smul, mul_smul, hmyz, smul_inv_smul]
  exists_ne := by
    rintro x A ⟨⟨g, rfl⟩, ⟨w, -, rfl⟩⟩
    by_cases hwα : w = α
    · exact ⟨g • C.β, Set.smul_mem_smul_set C.β_mem_line,
        fun h1 => C.ne ((smul_left_cancel g h1).trans hwα).symm⟩
    · exact ⟨g • α, Set.smul_mem_smul_set C.α_mem_line,
        fun h1 => hwα (smul_left_cancel g h1).symm⟩

theorem P95.false (h : C.P95) : False := by
  obtain ⟨ω, hω⟩ := exists_notMem_line C
  exact hω ((IsCoordLine.eq_univ h.setting h.isCoordLine C.α_mem_line) ▸ Set.mem_univ ω)

end CoordLine

end P49Config

section Step95

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.p49Step95 (hS : Sec4Setting G Ω) : P49Step95 G Ω :=
  fun C hT => P49Config.P95.false (C := C) ⟨hS, hT⟩

end Step95

end CFSG.Holt.H78
