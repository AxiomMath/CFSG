module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3C269G9

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem psl_conj_check : Core.pslLit.all (fun c => c == Core.cid || !(Core.cmul c c == Core.cid) ||
    Core.pslLit.any fun h => Core.cmul h c == Core.cmul Core.zbC h) = true := by
  decide +kernel

theorem psl29_conj_zb {z : P10} (hz : z ∈ A6Models.psl29) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ h ∈ A6Models.psl29, h * z * h⁻¹ = zb := by
  have hall := psl_conj_check
  rw [List.all_eq_true] at hall
  have h1 := hall (code z) ((mem_psl29_iff z).1 hz)
  rw [beq_cid_false hz1, beq_sq_true hz2] at h1
  simp only [Bool.false_or, Bool.not_true, List.any_eq_true] at h1
  obtain ⟨c, hc, hcz⟩ := h1
  obtain ⟨h, hh, rfl⟩ := exists_psl29_of_code hc
  refine ⟨h, hh, ?_⟩
  have hhz : h * z = zb * h := by
    apply code_injective
    rw [code_mul, code_mul, zb_code]
    exact beq_iff_eq.mp hcz
  rw [hhz, mul_inv_cancel_right]

theorem q8_check : Core.p0Lit.all (fun a => !(Core.cmul a a == Core.zbC) ||
    Core.p0Lit.all fun b => !(Core.cmul b b == Core.zbC) || !(Core.cmul (Core.cmul a b) a == b) ||
      (!(Core.inS6 a && Core.inS6 b) && !(Out21.A6.inPglC a && Out21.A6.inPglC b))) = true := by
  decide +kernel

theorem not_mem_s6_pgl29_of_q8 {a b : P10} (ha : a ∈ P0) (hb : b ∈ P0) (haa : a * a = zb)
    (hbb : b * b = zb) (hab : a * b * a = b) :
    ¬(a ∈ s6 ∧ b ∈ s6) ∧ ¬(a ∈ A6Models.pgl29 ∧ b ∈ A6Models.pgl29) := by
  have hall := q8_check
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) ((mem_P0_iff a).1 ha)
  have haa' : (Core.cmul (code a) (code a) == Core.zbC) = true := by
    rw [beq_iff_eq, ← code_mul, haa, zb_code]
  rw [haa'] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 (code b) ((mem_P0_iff b).1 hb)
  have hbb' : (Core.cmul (code b) (code b) == Core.zbC) = true := by
    rw [beq_iff_eq, ← code_mul, hbb, zb_code]
  have hab' : (Core.cmul (Core.cmul (code a) (code b)) (code a) == code b) = true := by
    rw [beq_iff_eq, ← code_mul, ← code_mul, hab]
  rw [hbb', hab'] at h2
  rw [mem_s6_iff, mem_s6_iff, Out21.A6.mem_pgl29_iff_code, Out21.A6.mem_pgl29_iff_code]
  revert h2
  generalize Core.inS6 (code a) = x1
  generalize Core.inS6 (code b) = x2
  generalize Out21.A6.inPglC (code a) = x3
  generalize Out21.A6.inPglC (code b) = x4
  revert x1 x2 x3 x4
  decide

@[expose] def s0 : P10 := A6Models.perm10 [[0, 3], [1, 2], [4, 5], [6, 9]]

@[expose] def s0C : List ℕ := [3, 2, 1, 0, 5, 4, 9, 7, 8, 6]

theorem s0_code : code s0 = s0C := by decide +kernel

theorem qm_conj_check : Out21.A6.qmL.all (fun y => y == Core.cid || y == Core.zbC ||
    !(Core.cmul y y == Core.cid) || Out21.A6.qmL.any fun c => Core.cmul c y == Core.cmul s0C c) =
      true := by
  decide +kernel

theorem exists_conj_s0 {y : P10} (hy : y ∈ P0 ⊓ A6Models.m10) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyz : y ≠ zb) : ∃ c ∈ P0 ⊓ A6Models.m10, c * y * c⁻¹ = s0 := by
  have hall := qm_conj_check
  rw [List.all_eq_true] at hall
  have h1 := hall (code y) ((Out21.A6.mem_Qm_iff y).1 hy)
  have hyz' : (code y == Core.zbC) = false := by
    rw [← zb_code]
    exact beq_ne_false hyz
  rw [beq_cid_false hy1, hyz', beq_sq_true hy2] at h1
  simp only [Bool.false_or, Bool.not_true, List.any_eq_true] at h1
  obtain ⟨c, hc, hcy⟩ := h1
  obtain ⟨x, hx, rfl⟩ := Out21.A6.surj_Qm c hc
  refine ⟨x, hx, ?_⟩
  have hxy : x * y = s0 * x := by
    apply code_injective
    rw [code_mul, code_mul, s0_code]
    exact beq_iff_eq.mp hcy
  rw [hxy, mul_inv_cancel_right]

theorem m10_le_autA6 : A6Models.m10 ≤ A6Models.autA6 := by
  rw [Out21.A6.m10_eq, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ Out21.A6.m10Gens := hg
  simp only [Out21.A6.m10Gens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl
  · exact psl29_le_autA6 Out21.A6.tAdd_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tSq_mem_psl29
  · exact psl29_le_autA6 Out21.A6.tInv_mem_psl29
  · exact Out21.A6.tMulFrob_mem_autA6

@[expose] def u1 : P10 := A6Models.perm10 [[0, 5, 3, 7, 9, 4, 6, 8], [1, 2]]

@[expose] def u2 : P10 := A6Models.perm10 [[0, 7, 6, 5, 9, 8, 3, 4], [1, 2]]

@[expose] def u3 : P10 := A6Models.perm10 [[0, 4, 9, 5], [3, 7, 6, 8]]

@[expose] def u4 : P10 := A6Models.perm10 [[0, 8, 9, 7], [3, 4, 6, 5]]

@[expose] def v1 : P10 := A6Models.perm10 [[0, 6, 3, 9], [1, 4, 2, 5]]

@[expose] def v2 : P10 := A6Models.perm10 [[0, 1, 6, 4, 3, 2, 9, 5], [7, 8]]

theorem gens_words : A6Models.tAdd = u1 * v1 * u2 * v2 * u3 ∧ A6Models.tSq = u1 * v1 * u4 ∧
    A6Models.tMulFrob = u1 * v2 * u2 := by
  decide +kernel

theorem words_comm : u1 * zb = zb * u1 ∧ u2 * zb = zb * u2 ∧ u3 * zb = zb * u3 ∧
    u4 * zb = zb * u4 ∧ A6Models.tInv * zb = zb * A6Models.tInv ∧ v1 * s0 = s0 * v1 ∧
    v2 * s0 = s0 * v2 := by
  decide +kernel

theorem words_code_mem : Out21.A6.inM10C (code u1) = true ∧ Out21.A6.inM10C (code u2) = true ∧
    Out21.A6.inM10C (code u3) = true ∧ Out21.A6.inM10C (code u4) = true ∧
    Out21.A6.inM10C (code v1) = true ∧ Out21.A6.inM10C (code v2) = true ∧
    Out21.A6.inM10C (code A6Models.tInv) = true ∧ Out21.A6.inM10C (code s0) = true := by
  decide +kernel

theorem s0_mem_m10 : s0 ∈ A6Models.m10 :=
  (Out21.A6.mem_m10_iff_code s0).2 words_code_mem.2.2.2.2.2.2.2

theorem sup_centralizer_zb_s0 (hz : zb ∈ A6Models.m10) (hs : s0 ∈ A6Models.m10) :
    Subgroup.centralizer ({⟨zb, hz⟩} : Set ↥A6Models.m10) ⊔
      Subgroup.centralizer ({⟨s0, hs⟩} : Set ↥A6Models.m10) = ⊤ := by
  set K := Subgroup.centralizer ({⟨zb, hz⟩} : Set ↥A6Models.m10) ⊔
    Subgroup.centralizer ({⟨s0, hs⟩} : Set ↥A6Models.m10) with hK
  have hmem : ∀ w : P10, Out21.A6.inM10C (code w) = true →
      (w * zb = zb * w ∨ w * s0 = s0 * w) → w ∈ K.map A6Models.m10.subtype := by
    intro w hw hc
    refine ⟨⟨w, (Out21.A6.mem_m10_iff_code w).2 hw⟩, ?_, rfl⟩
    rcases hc with hc | hc
    · exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hc))
    · exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hc))
  obtain ⟨e1, e2, e3⟩ := gens_words
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := words_comm
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, -⟩ := words_code_mem
  have hle : Subgroup.closure {g | g ∈ Out21.A6.m10Gens} ≤ K.map A6Models.m10.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ Out21.A6.m10Gens := hg
    simp only [Out21.A6.m10Gens, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl
    · rw [e1]
      exact mul_mem (mul_mem (mul_mem (mul_mem (hmem _ m1 (.inl c1)) (hmem _ m5 (.inr c6)))
        (hmem _ m2 (.inl c2))) (hmem _ m6 (.inr c7))) (hmem _ m3 (.inl c3))
    · rw [e2]
      exact mul_mem (mul_mem (hmem _ m1 (.inl c1)) (hmem _ m5 (.inr c6))) (hmem _ m4 (.inl c4))
    · exact hmem _ m7 (.inl c5)
    · rw [e3]
      exact mul_mem (mul_mem (hmem _ m1 (.inl c1)) (hmem _ m6 (.inr c7))) (hmem _ m2 (.inl c2))
  rw [eq_top_iff]
  rintro x -
  have hx : (x : P10) ∈ Subgroup.closure {g | g ∈ Out21.A6.m10Gens} := by
    rw [← Out21.A6.m10_eq]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [show y = x from Subtype.ext hyx] at hy

end CFSG.ClassicalInvolution.Q3.TL4.E3C269G9
