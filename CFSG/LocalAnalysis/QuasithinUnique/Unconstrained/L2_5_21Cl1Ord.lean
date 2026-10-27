module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.QuasithinUnique.Out21.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem code_mem_cosetList {t x : P10}
    (hx : ∃ r ∈ [(1 : P10), t], x * r⁻¹ ∈ A6Models.psl29) : code x ∈ cosetList (code t) := by
  obtain ⟨r, hr, hxr⟩ := hx
  have hy := (mem_psl29_iff _).mp hxr
  simp only [cosetList, List.mem_append, List.mem_map]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h1 | h1
  · left
    subst h1
    simpa using hy
  · right
    refine ⟨code (x * r⁻¹), hy, ?_⟩
    subst h1
    rw [← code_mul]
    congr 1
    group

theorem noOrderSix_check_m10 :
    (cosetList (code A6Models.tMulFrob)).all (fun c =>
      !(Core.cpow c 6 == Core.cid) || Core.cpow c 2 == Core.cid || Core.cpow c 3 == Core.cid) =
      true := by
  decide +kernel

theorem noOrderSix_check_pgl29 :
    (cosetList (code A6Models.tMul)).all (fun c =>
      !(Core.cpow c 6 == Core.cid) || Core.cpow c 2 == Core.cid || Core.cpow c 3 == Core.cid) =
      true := by
  decide +kernel

theorem no_order_six_m10 {x : P10} (hx : x ∈ A6Models.m10) (h6 : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1)
    (h3 : x ^ 3 ≠ 1) : False := by
  have hmem : code x ∈ cosetList (code A6Models.tMulFrob) :=
    code_mem_cosetList ((mem_m10_iff x).mp hx)
  have hall := noOrderSix_check_m10
  rw [List.all_eq_true] at hall
  have h1 := hall _ hmem
  have h6' : Core.cpow (code x) 6 = Core.cid := by rw [← code_pow, h6, code_one]
  simp only [h6', beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at h1
  rcases h1 with h | h
  · apply h2
    apply code_injective
    rw [code_pow, code_one]
    exact h
  · apply h3
    apply code_injective
    rw [code_pow, code_one]
    exact h

theorem no_order_six_pgl29 {x : P10} (hx : x ∈ A6Models.pgl29) (h6 : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1)
    (h3 : x ^ 3 ≠ 1) : False := by
  have hmem : code x ∈ cosetList (code A6Models.tMul) :=
    code_mem_cosetList ((mem_pgl29_iff x).mp hx)
  have hall := noOrderSix_check_pgl29
  rw [List.all_eq_true] at hall
  have h1 := hall _ hmem
  have h6' : Core.cpow (code x) 6 = Core.cid := by rw [← code_pow, h6, code_one]
  simp only [h6', beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at h1
  rcases h1 with h | h
  · apply h2
    apply code_injective
    rw [code_pow, code_one]
    exact h
  · apply h3
    apply code_injective
    rw [code_pow, code_one]
    exact h

theorem false_of_order_six {B : Type*} [Group B]
    (hB : Nonempty (B ≃* ↥A6Models.m10) ∨ Nonempty (B ≃* ↥A6Models.pgl29)) {α : B}
    (h6 : α ^ 6 = 1) (h2 : α ^ 2 ≠ 1) (h3 : α ^ 3 ≠ 1) : False := by
  rcases hB with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · refine no_order_six_m10 (φ α).2 ?_ ?_ ?_
    · have := congrArg (fun z : ↥A6Models.m10 => (z : P10)) (show φ α ^ 6 = 1 by rw [← map_pow, h6, map_one])
      simpa using this
    · intro h
      apply h2
      apply φ.injective
      apply Subtype.ext
      simpa using h
    · intro h
      apply h3
      apply φ.injective
      apply Subtype.ext
      simpa using h
  · refine no_order_six_pgl29 (φ α).2 ?_ ?_ ?_
    · have := congrArg (fun z : ↥A6Models.pgl29 => (z : P10)) (show φ α ^ 6 = 1 by rw [← map_pow, h6, map_one])
      simpa using this
    · intro h
      apply h2
      apply φ.injective
      apply Subtype.ext
      simpa using h
    · intro h
      apply h3
      apply φ.injective
      apply Subtype.ext
      simpa using h

end CFSG.QuasithinUnique.Out21.A6
