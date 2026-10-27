module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

theorem ncard_eq_of_code_mem {X : Set P10} {E : List (List ℕ)} (hnd : E.Nodup)
    (hmem : ∀ x : P10, x ∈ X ↔ code x ∈ E) (hsurj : ∀ c ∈ E, ∃ x ∈ X, code x = c) :
    X.ncard = E.length := by
  have h1 : code '' X = ↑E.toFinset := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (hmem x).mp hx
    · intro hc
      have hc' : c ∈ E := by simpa using hc
      obtain ⟨x, hx, rfl⟩ := hsurj c hc'
      exact ⟨x, hx, rfl⟩
  calc X.ncard = (code '' X).ncard := (Set.ncard_image_of_injective _ code_injective).symm
    _ = (↑E.toFinset : Set (List ℕ)).ncard := by rw [h1]
    _ = E.length := by rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem orderOf_eq_ordC {x : P10} (hx : x ∈ P0) : orderOf x = Core.ordC (code x) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Core.ordC
  split_ifs with h1 h2' h3
  · have : x = 1 := code_injective (by rw [code_one]; exact beq_iff_eq.mp h1)
    rw [this, orderOf_one]
  · have hxx : x ^ 2 = 1 := by
      apply code_injective
      rw [sq, code_mul, code_one]
      exact beq_iff_eq.mp h2'
    have hx1 : x ≠ 1 := by
      intro h
      apply h1
      rw [h, code_one]
      simp
    exact orderOf_eq_prime hxx hx1
  · have hx4 : x ^ 4 = 1 := by
      apply code_injective
      rw [code_pow, code_one]
      exact beq_iff_eq.mp h3
    have hx2 : ¬ x ^ 2 = 1 := by
      intro h
      apply h2'
      have : x * x = 1 := by rw [← sq]; exact h
      rw [beq_iff_eq, ← code_mul, this, code_one]
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hx2) (by simpa using hx4)
    simpa using this
  · have hx4 : ¬ x ^ 4 = 1 := by
      intro h
      apply h3
      rw [beq_iff_eq, ← code_pow, h, code_one]
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using hx4)
      (by simpa using P0_pow_eight hx)
    simpa using this

theorem mem_masksOf : ∀ (n : ℕ) (m : List Bool), m.length = n → m ∈ Core.masksOf n := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [List.length_eq_zero_iff] at hm
    subst hm
    simp [Core.masksOf]
  | succ n ih =>
    intro m hm
    cases m with
    | nil => simp at hm
    | cons b m' =>
      have hm' : m'.length = n := by simpa using hm
      simp only [Core.masksOf, List.mem_flatMap]
      refine ⟨m', ih m' hm', ?_⟩
      cases b <;> simp

theorem class_sub {k : ℕ} {c : List ℕ} (hc : c ∈ Core.p0Classes.getD k []) : c ∈ Core.p0Lit := by
  have h := Core.cls_sub
  rw [List.all_eq_true] at h
  rcases getD_mem_or_default Core.p0Classes k [] with hk | hk
  · have h1 := h _ hk
    rw [List.all_eq_true] at h1
    exact List.contains_iff_mem.mp (h1 c hc)
  · rw [hk] at hc
    simp at hc

theorem class_orbit {k : ℕ} {c c' : List ℕ} (hc : c ∈ Core.p0Classes.getD k [])
    (hc' : c' ∈ Core.p0Classes.getD k []) :
    ∃ g ∈ Core.p0Lit, Core.cmul g c = Core.cmul c' g := by
  have h := Core.cls_orbit
  rw [List.all_eq_true] at h
  rcases getD_mem_or_default Core.p0Classes k [] with hk | hk
  · have h1 := h _ hk
    rw [List.all_eq_true] at h1
    have h2 := h1 c hc
    rw [List.all_eq_true] at h2
    have h3 := h2 c' hc'
    rw [List.any_eq_true] at h3
    obtain ⟨g, hg, hgc⟩ := h3
    exact ⟨g, hg, beq_iff_eq.mp hgc⟩
  · rw [hk] at hc
    simp at hc

theorem normal_subgroup_type {N : Subgroup P10} (hNP : N ≤ P0)
    (hnorm : ∀ g ∈ P0, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    ∃ t ∈ Core.p0Types, Nat.card N = t.1 ∧
      Set.ncard {x : P10 | x ∈ N ∧ orderOf x = 2} = t.2.1 ∧
      Set.ncard {x : P10 | x ∈ N ∧ orderOf x = 4} = t.2.2.1 ∧
      Set.ncard {x : P10 | x ∈ N ∧ orderOf x = 8} = t.2.2.2 := by
  classical
  set hit : ℕ → Prop := fun k => ∃ x ∈ N, code x ∈ Core.p0Classes.getD k [] with hhit
  have hclassN : ∀ k, hit k → ∀ c ∈ Core.p0Classes.getD k [], ∃ y ∈ N, code y = c := by
    rintro k ⟨x, hxN, hxk⟩ c hc
    obtain ⟨g, hg, hgc⟩ := class_orbit hxk hc
    obtain ⟨g', hg'P, rfl⟩ := exists_P0_of_code hg
    obtain ⟨z, hzP, rfl⟩ := exists_P0_of_code (class_sub hc)
    have e : g' * x = z * g' := by
      apply code_injective
      rw [code_mul, code_mul]
      exact hgc
    refine ⟨z, ?_, rfl⟩
    have : z = g' * x * g'⁻¹ := by rw [e]; group
    rw [this]
    exact hnorm g' hg'P x hxN
  let m : List Bool := (List.range 11).map fun k => decide (hit k)
  have hmlen : m.length = 11 := by simp [m]
  have hmget : ∀ k, k < 11 → m.getD k false = decide (hit k) := by
    intro k hk
    simp [m, List.getD_eq_getElem?_getD, hk]
  have hmU : ∀ c, c ∈ Core.maskU m ↔ ∃ k, k < 11 ∧ hit k ∧ c ∈ Core.p0Classes.getD k [] := by
    intro c
    unfold Core.maskU
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨k, hk, hc⟩
      rw [List.mem_range] at hk
      rw [hmget k hk] at hc
      by_cases h : hit k
      · simp only [h, decide_true, ite_true] at hc
        exact ⟨k, hk, h, hc⟩
      · simp only [h, decide_false, Bool.false_eq_true, ite_false] at hc
        simp at hc
    · rintro ⟨k, hk, h, hc⟩
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rw [hmget k hk]
      simp only [h, decide_true, ite_true]
      exact hc
  have hmemU : ∀ x : P10, x ∈ N ↔ code x ∈ Core.maskU m := by
    intro x
    rw [hmU]
    constructor
    · intro hx
      have hcx : code x ∈ Core.p0Lit := (mem_P0_iff x).1 (hNP hx)
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hcx
      have hj32 : j < 32 := by rw [Core.p0_length] at hj; exact hj
      have hspec := Core.cls_idx_spec
      rw [List.all_eq_true] at hspec
      have h1 := hspec j (List.mem_range.mpr hj32)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨hk, hmem⟩ := h1
      have hgetD : Core.p0Lit.getD j [] = code x := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        simpa using hjx
      rw [hgetD] at hmem
      exact ⟨Core.p0ClsIdx.getD j 0, hk, ⟨x, hx, List.contains_iff_mem.mp hmem⟩,
        List.contains_iff_mem.mp hmem⟩
    · rintro ⟨k, hk, hh, hc⟩
      obtain ⟨y, hyN, hy⟩ := hclassN k hh (code x) hc
      rwa [← code_injective hy]
  have hsurjU : ∀ c ∈ Core.maskU m, ∃ x ∈ N, code x = c := by
    intro c hc
    obtain ⟨k, hk, hh, hck⟩ := (hmU c).1 hc
    exact hclassN k hh c hck
  have hmemcl : ∀ i, i < 11 → Core.p0Classes.getD i [] ∈ Core.p0Classes := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Core.p0Classes_length]; exact hi)]
    exact List.getElem_mem _
  have hidx1 : ∀ j, j < 32 → Core.p0ClsIdx.getD j 0 < 11 ∧
      (Core.p0Classes.getD (Core.p0ClsIdx.getD j 0) []).contains (Core.p0Lit.getD j []) = true := by
    intro j hj
    have hspec := Core.cls_idx_spec
    rw [List.all_eq_true] at hspec
    have h1 := hspec j (List.mem_range.mpr hj)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h1
  have hidx2 : ∀ i, i < 11 → ∀ j, j < 32 → (Core.p0ProdTab.getD i []).getD j 0 < 11 ∧
      (Core.p0Classes.getD ((Core.p0ProdTab.getD i []).getD j 0) []).contains
        (Core.cmul ((Core.p0Classes.getD i []).headD []) (Core.p0Lit.getD j [])) = true := by
    intro i hi j hj
    have hspec := Core.prod_tab_spec
    rw [List.all_eq_true] at hspec
    have h1 := hspec i (List.mem_range.mpr hi)
    rw [List.all_eq_true] at h1
    have h2 := h1 j (List.mem_range.mpr hj)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h2
  have hcl : ∀ i, i < 11 → hit i → ∀ j, j < 32 → hit (Core.p0ClsIdx.getD j 0) →
      hit ((Core.p0ProdTab.getD i []).getD j 0) := by
    intro i hi hhi j hj hhj
    have hrep : (Core.p0Classes.getD i []).headD [] ∈ Core.p0Classes.getD i [] := by
      have hh := Core.cls_head
      rw [List.all_eq_true] at hh
      exact List.contains_iff_mem.mp (hh _ (hmemcl i hi))
    obtain ⟨r, hrN, hr⟩ := hclassN i hhi _ hrep
    obtain ⟨hk1, hmem1⟩ := hidx1 j hj
    obtain ⟨e, heN, he⟩ := hclassN _ hhj _ (List.contains_iff_mem.mp hmem1)
    obtain ⟨hk2, hmem2⟩ := hidx2 i hi j hj
    refine ⟨r * e, N.mul_mem hrN heN, ?_⟩
    rw [code_mul, hr, he]
    exact List.contains_iff_mem.mp hmem2
  have hclosed : Core.maskClosed m = true := by
    unfold Core.maskClosed
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · rw [hmget 0 (by norm_num)]
      have h0 : hit 0 := ⟨1, N.one_mem, by
        rw [code_one]; exact List.contains_iff_mem.mp Core.cls_zero⟩
      simp [h0]
    · intro i hi
      rw [List.mem_range] at hi
      rw [Bool.or_eq_true, Bool.not_eq_true', hmget i hi]
      by_cases hhi : hit i
      · right
        rw [List.all_eq_true]
        intro j hj
        rw [List.mem_range] at hj
        rw [Bool.or_eq_true, Bool.not_eq_true', hmget _ (hidx1 j hj).1,
          hmget _ (hidx2 i hi j hj).1]
        by_cases hhj : hit (Core.p0ClsIdx.getD j 0)
        · right
          exact decide_eq_true (hcl i hi hhi j hj hhj)
        · left
          exact decide_eq_false hhj
      · left
        exact decide_eq_false hhi
  have hmasks := Core.mask_types
  rw [List.all_eq_true] at hmasks
  have h1 := hmasks m (mem_masksOf 11 m hmlen)
  rw [hclosed] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hnd, htype⟩ := h1
  have hnd' : (Core.maskU m).Nodup := by simpa using hnd
  have hcardN : Nat.card N = (Core.maskU m).length := card_eq_of_code_mem hnd' hmemU hsurjU
  have hcnt : ∀ o, o = 2 ∨ o = 4 ∨ o = 8 → Set.ncard {x : P10 | x ∈ N ∧ orderOf x = o} =
      ((Core.maskU m).filter fun c => Core.ordC c == o).length := by
    intro o ho
    apply ncard_eq_of_code_mem
    · exact hnd'.filter _
    · intro x
      simp only [Set.mem_ofPred_eq, List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨hxN, hxo⟩
        refine ⟨(hmemU x).1 hxN, ?_⟩
        rw [← orderOf_eq_ordC (hNP hxN)]
        exact hxo
      · rintro ⟨hxU, hxo⟩
        have hxN : x ∈ N := (hmemU x).2 hxU
        refine ⟨hxN, ?_⟩
        rw [orderOf_eq_ordC (hNP hxN)]
        exact hxo
    · intro c hc
      simp only [List.mem_filter, beq_iff_eq] at hc
      obtain ⟨hcU, hco⟩ := hc
      obtain ⟨x, hxN, rfl⟩ := hsurjU c hcU
      refine ⟨x, ⟨hxN, ?_⟩, rfl⟩
      rw [orderOf_eq_ordC (hNP hxN)]
      exact hco
  refine ⟨Core.maskType m, List.contains_iff_mem.mp htype, hcardN, ?_, ?_, ?_⟩
  · rw [hcnt 2 (by norm_num)]; rfl
  · rw [hcnt 4 (by norm_num)]; rfl
  · rw [hcnt 8 (by norm_num)]; rfl

end CFSG.QuasithinUnique.A6Facts
