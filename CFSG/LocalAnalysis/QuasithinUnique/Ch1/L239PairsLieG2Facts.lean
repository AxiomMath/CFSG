module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LieType.Chevalley.EvenRootCommutatorG2
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def rA : Fin Tag.G2.rank → ℤ := ![1, 0]
@[expose] def rR : Fin Tag.G2.rank → ℤ := ![0, 1]
@[expose] def rU : Fin Tag.G2.rank → ℤ := ![1, 1]
@[expose] def rV : Fin Tag.G2.rank → ℤ := ![1, 2]
@[expose] def rB : Fin Tag.G2.rank → ℤ := ![1, 3]
@[expose] def rC : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem isRoot_pos_iff {α : Fin Tag.G2.rank → ℤ} :
    (IsRoot Tag.G2 α ∧ 0 < height α) ↔
      α = rA ∨ α = rR ∨ α = rU ∨ α = rV ∨ α = rB ∨ α = rC := by
  have h : (rootFinset Tag.G2).filter (fun β => 0 < height β) = {rA, rR, rU, rV, rB, rC} := by
    decide +kernel
  constructor
  · rintro ⟨h1, h2⟩
    have : α ∈ (rootFinset Tag.G2).filter (fun β => 0 < height β) :=
      Finset.mem_filter.2 ⟨mem_rootFinset.2 h1, h2⟩
    rw [h] at this
    simpa using this
  · intro h'
    have : α ∈ ({rA, rR, rU, rV, rB, rC} : Finset (Fin Tag.G2.rank → ℤ)) := by simpa using h'
    rw [← h] at this
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 this
    exact ⟨mem_rootFinset.1 h1, h2⟩

@[expose] def i0 : Fin Tag.G2.rank := ⟨0, by decide⟩
@[expose] def i1 : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem fin_two_cases : ∀ i : Fin Tag.G2.rank, i = i0 ∨ i = i1 := by decide

theorem single_i0 : Pi.single i0 (1 : ℤ) = rA := by
  funext i
  rcases fin_two_cases i with rfl | rfl <;> decide

theorem single_i1 : Pi.single i1 (1 : ℤ) = rR := by
  funext i
  rcases fin_two_cases i with rfl | rfl <;> decide

theorem radicalRoots_zero :
    parabolicRadicalRoots Tag.G2 ({i0} : Set (Fin Tag.G2.rank)) = {rR, rU, rV, rB, rC} := by
  ext α
  rw [mem_parabolicRadicalRoots_iff]
  constructor
  · rintro ⟨h1, h2, i, hi, hne⟩
    have hi' : i = i1 := by
      rcases fin_two_cases i with rfl | rfl
      · exact absurd (Set.mem_singleton _) hi
      · rfl
    subst hi'
    rcases isRoot_pos_iff.1 ⟨h1, h2⟩ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by decide) hne
    all_goals simp
  · intro h
    have hpos : α = rA ∨ α = rR ∨ α = rU ∨ α = rV ∨ α = rB ∨ α = rC := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto
    obtain ⟨h1, h2⟩ := isRoot_pos_iff.2 hpos
    refine ⟨h1, h2, i1, ?_, ?_⟩
    · intro hmem
      exact absurd (Set.mem_singleton_iff.1 hmem) (by decide)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem radicalRoots_one :
    parabolicRadicalRoots Tag.G2 ({i1} : Set (Fin Tag.G2.rank)) = {rA, rU, rV, rB, rC} := by
  ext α
  rw [mem_parabolicRadicalRoots_iff]
  constructor
  · rintro ⟨h1, h2, i, hi, hne⟩
    have hi' : i = i0 := by
      rcases fin_two_cases i with rfl | rfl
      · rfl
      · exact absurd (Set.mem_singleton _) hi
    subst hi'
    rcases isRoot_pos_iff.1 ⟨h1, h2⟩ with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact absurd (by decide) hne
    all_goals simp
  · intro h
    have hpos : α = rA ∨ α = rR ∨ α = rU ∨ α = rV ∨ α = rB ∨ α = rC := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto
    obtain ⟨h1, h2⟩ := isRoot_pos_iff.2 hpos
    refine ⟨h1, h2, i0, ?_, ?_⟩
    · intro hmem
      exact absurd (Set.mem_singleton_iff.1 hmem) (by decide)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

section Elements

variable {K : Type} [Field K] [CharP K 2]

noncomputable abbrev gX
    (d : Fin Tag.G2.rank → ℤ) (c : K) : ModGL Tag.G2 K := pinnedX Tag.G2 K d c

@[expose] def rNR : Fin Tag.G2.rank → ℤ := ![0, -1]

omit [CharP K 2] in
theorem gX_add
    (d : Fin Tag.G2.rank → ℤ) (x y : K) : gX d (x + y) = gX d x * gX d y :=
  pinnedX_add Tag.G2 K d x y

omit [CharP K 2] in
theorem gX_zero
    (d : Fin Tag.G2.rank → ℤ) : gX d (0 : K) = 1 := pinnedX_zero Tag.G2 K d

omit [CharP K 2] in
theorem gX_eq_one
    {d : Fin Tag.G2.rank → ℤ} {x : K} (h : gX d x = 1) : x = 0 :=
  pinnedX_injective Tag.G2 K d (h.trans (gX_zero d).symm)

theorem gX_self
    (d : Fin Tag.G2.rank → ℤ) (x : K) : gX d x * gX d x = 1 := by
  rw [← gX_add, CharTwo.add_self_eq_zero, gX_zero]

theorem gX_inv
    (d : Fin Tag.G2.rank → ℤ) (x : K) : (gX d x)⁻¹ = gX d x :=
  inv_eq_of_mul_eq_one_right (gX_self d x)

omit [CharP K 2] in
theorem gX_comm_self
    (d : Fin Tag.G2.rank → ℤ) (x y : K) :
    Commute (gX d x) (gX d y) := by
  show gX d x * gX d y = gX d y * gX d x
  rw [← gX_add, ← gX_add, add_comm]

theorem rel_ar
    (x y : K) : ⁅gX rA x, gX rR y⁆ =
    gX rU (x * y) * gX rV (x * y ^ 2) * gX rB (x * y ^ 3) * gX rC (x ^ 2 * y ^ 3) :=
  (g2_even_root_commutator_table x y).1

theorem rel_ru
    (x y : K) : ⁅gX rR x, gX rU y⁆ = gX rC (x * y ^ 2) * gX rB (x ^ 2 * y) :=
  (g2_even_root_commutator_table x y).2.1

theorem rel_rv
    (x y : K) : ⁅gX rR x, gX rV y⁆ = gX rB (x * y) :=
  (g2_even_root_commutator_table x y).2.2.1

theorem rel_ab
    (x y : K) : ⁅gX rA x, gX rB y⁆ = gX rC (x * y) :=
  (g2_even_root_commutator_table x y).2.2.2.1

theorem rel_uv
    (x y : K) : ⁅gX rU x, gX rV y⁆ = gX rC (x * y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.1

theorem rel_vnr
    (x y : K) :
    ⁅gX rV x, gX rNR y⁆ = gX rA (x * y ^ 2) * gX rC (x ^ 2 * y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.1

theorem comm_au
    (x y : K) : Commute (gX rA x) (gX rU y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.1

theorem comm_av
    (x y : K) : Commute (gX rA x) (gX rV y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.1

theorem comm_ac
    (x y : K) : Commute (gX rA x) (gX rC y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.1

theorem comm_rb
    (x y : K) : Commute (gX rR x) (gX rB y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.1

theorem comm_rc
    (x y : K) : Commute (gX rR x) (gX rC y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.1

theorem comm_ub
    (x y : K) : Commute (gX rU x) (gX rB y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_uc
    (x y : K) : Commute (gX rU x) (gX rC y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_vb
    (x y : K) : Commute (gX rV x) (gX rB y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_vc
    (x y : K) : Commute (gX rV x) (gX rC y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_bc
    (x y : K) : Commute (gX rB x) (gX rC y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

omit [CharP K 2] in
theorem prod_bc_eq_one
    {x y : K} (h : gX rB x * gX rC y = 1) : x = 0 ∧ y = 0 := by
  have hbc : rB ≠ rC := by decide
  have hnd : [rB, rC].Nodup := by simp [hbc]
  have hL : ∀ α ∈ [rB, rC], IsRoot Tag.G2 α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl
    · exact isRoot_pos_iff.2 (by simp)
    · exact isRoot_pos_iff.2 (by simp)
  have key := pinnedX_list_prod_injective (τ := Tag.G2) (R := K) [rB, rC] hnd hL
    (fun α => if α = rB then x else y) (fun _ => 0) (by
      simp [hbc.symm, pinnedX_zero]
      exact h)
  exact ⟨by simpa using key rB (by simp), by simpa [hbc.symm] using key rC (by simp)⟩

end Elements

section Radical

variable {K : Type} [Field K] [CharP K 2]

theorem radical_pos {J : Set (Fin Tag.G2.rank)} :
    ∀ α ∈ parabolicRadicalRoots Tag.G2 J, IsRoot Tag.G2 α ∧ 0 < height α := fun α hα => by
  obtain ⟨h1, h2, -⟩ := mem_parabolicRadicalRoots_iff.1 hα
  exact ⟨h1, h2⟩

theorem radical_closed
    {J : Set (Fin Tag.G2.rank)} :
    ∀ α ∈ parabolicRadicalRoots Tag.G2 J, ∀ β ∈ parabolicRadicalRoots Tag.G2 J, ∀ a b : ℕ,
      1 ≤ a → 1 ≤ b → IsRoot Tag.G2 (a • α + b • β) →
        a • α + b • β ∈ parabolicRadicalRoots Tag.G2 J :=
  fun α hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRoots (radical_pos α hα) hβ ha hb hr

omit [CharP K 2] in
theorem coords_zero
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i0}) :
    ∃ t₁ t₂ t₃ t₄ t₅ : K,
      g = gX rR t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))) := by
  have hinj : Function.Injective ![rR, rU, rV, rB, rC] := by decide
  have hrange : Set.range ![rR, rU, rV, rB, rC] = parabolicRadicalRoots Tag.G2 {i0} := by
    rw [radicalRoots_zero]
    ext x
    simp
    tauto
  obtain ⟨t, -, ht⟩ :=
    (bijOn_prod_pinnedX K radical_pos radical_closed ![rR, rU, rV, rB, rC] hinj hrange).surjOn hg
  refine ⟨t 0, t 1, t 2, t 3, t 4, ?_⟩
  rw [← ht]
  simp [List.ofFn_succ]

omit [CharP K 2] in
theorem coords_one
    {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) :
    ∃ t₁ t₂ t₃ t₄ t₅ : K,
      g = gX rA t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))) := by
  have hinj : Function.Injective ![rA, rU, rV, rB, rC] := by decide
  have hrange : Set.range ![rA, rU, rV, rB, rC] = parabolicRadicalRoots Tag.G2 {i1} := by
    rw [radicalRoots_one]
    ext x
    simp
    tauto
  obtain ⟨t, -, ht⟩ :=
    (bijOn_prod_pinnedX K radical_pos radical_closed ![rA, rU, rV, rB, rC] hinj hrange).surjOn hg
  refine ⟨t 0, t 1, t 2, t 3, t 4, ?_⟩
  rw [← ht]
  simp [List.ofFn_succ]

omit [CharP K 2] in
theorem mem_zero
    {d : Fin Tag.G2.rank → ℤ} (hd : d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC)
    (c : K) : gX d c ∈ parabolicRadical Tag.G2 K {i0} := by
  have : d ∈ parabolicRadicalRoots Tag.G2 ({i0} : Set (Fin Tag.G2.rank)) := by
    rw [radicalRoots_zero]; simpa using hd
  exact pinnedX_mem_rootSpan this c

omit [CharP K 2] in
theorem mem_one
    {d : Fin Tag.G2.rank → ℤ} (hd : d = rA ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC)
    (c : K) : gX d c ∈ parabolicRadical Tag.G2 K {i1} := by
  have : d ∈ parabolicRadicalRoots Tag.G2 ({i1} : Set (Fin Tag.G2.rank)) := by
    rw [radicalRoots_one]; simpa using hd
  exact pinnedX_mem_rootSpan this c

end Radical

section Center

theorem commute_of_mem_closure' {M : Type*} [Group M] {s : Set M} {g : M}
    (h : ∀ x ∈ s, Commute g x) {n : M} (hn : n ∈ Subgroup.closure s) : Commute g n :=
  Subgroup.closure_induction (p := fun n _ => Commute g n) h (Commute.one_right g)
    (fun _ _ _ _ hx hy => hx.mul_right hy) (fun _ _ hx => hx.inv_right) hn

theorem comm_mul_eq {M : Type*} [Group M] {Q N : Subgroup M}
    (hN : N ≤ Subgroup.centralizer (Q : Set M)) {x y g : M} (hx : x ∈ Q) (hyg : ⁅y, g⁆ ∈ N) :
    ⁅x * y, g⁆ = ⁅y, g⁆ * ⁅x, g⁆ := by
  have hc : x * ⁅y, g⁆ = ⁅y, g⁆ * x := Subgroup.mem_centralizer_iff.1 (hN hyg) x hx
  have h1 : ⁅x * y, g⁆ = x * ⁅y, g⁆ * x⁻¹ * ⁅x, g⁆ := by
    simp only [commutatorElement_def]; group
  rw [h1, hc, mul_inv_cancel_right]

theorem comm_five {M : Type*} [Group M] {Q N : Subgroup M}
    (hN : N ≤ Subgroup.centralizer (Q : Set M)) {x₁ x₂ x₃ x₄ x₅ g : M} (h₁ : x₁ ∈ Q)
    (h₂ : x₂ ∈ Q) (h₃ : x₃ ∈ Q) (h₄ : x₄ ∈ Q) (c₂ : ⁅x₂, g⁆ ∈ N)
    (c₃ : ⁅x₃, g⁆ ∈ N) (c₄ : ⁅x₄, g⁆ ∈ N) (c₅ : ⁅x₅, g⁆ ∈ N) :
    ⁅x₁ * (x₂ * (x₃ * (x₄ * x₅))), g⁆ = ⁅x₅, g⁆ * ⁅x₄, g⁆ * ⁅x₃, g⁆ * ⁅x₂, g⁆ * ⁅x₁, g⁆ := by
  have e4 := comm_mul_eq hN h₄ c₅
  have m4 : ⁅x₄ * x₅, g⁆ ∈ N := e4 ▸ N.mul_mem c₅ c₄
  have e3 := comm_mul_eq hN h₃ m4
  have m3 : ⁅x₃ * (x₄ * x₅), g⁆ ∈ N := e3 ▸ N.mul_mem m4 c₃
  have e2 := comm_mul_eq hN h₂ m3
  have m2 : ⁅x₂ * (x₃ * (x₄ * x₅)), g⁆ ∈ N := e2 ▸ N.mul_mem m3 c₂
  have e1 := comm_mul_eq hN h₁ m2
  rw [e1, e2, e3, e4]

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem rootSpan_commute
    {T : Set (Fin Tag.G2.rank → ℤ)} {x : ModGL Tag.G2 K}
    (h : ∀ β ∈ T, ∀ c : K, Commute (gX β c) x) {q : ModGL Tag.G2 K}
    (hq : q ∈ rootSpan Tag.G2 K T) : Commute q x := by
  have : rootSpan Tag.G2 K T ≤ Subgroup.centralizer ({x} : Set (ModGL Tag.G2 K)) := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (h β hβ c).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hq)

@[expose] noncomputable def N0
    : Subgroup (ModGL Tag.G2 K) :=
  Subgroup.closure (Set.range (gX rB) ∪ Set.range (gX rC))

@[expose] noncomputable def N1
    : Subgroup (ModGL Tag.G2 K) := Subgroup.closure (Set.range (gX rC))

omit [CharP K 2] in
theorem gX_b_mem_N0
    (y : K) : gX rB y ∈ (N0 : Subgroup (ModGL Tag.G2 K)) :=
  Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)

omit [CharP K 2] in
theorem gX_c_mem_N0
    (y : K) : gX rC y ∈ (N0 : Subgroup (ModGL Tag.G2 K)) :=
  Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)

omit [CharP K 2] in
theorem gX_c_mem_N1
    (y : K) : gX rC y ∈ (N1 : Subgroup (ModGL Tag.G2 K)) :=
  Subgroup.subset_closure ⟨y, rfl⟩

theorem N0_le_centralizer
    :
    (N0 : Subgroup (ModGL Tag.G2 K)) ≤
      Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K)) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : q ∈ rootSpan Tag.G2 K {rR, rU, rV, rB, rC} := by
    have : parabolicRadical Tag.G2 K {i0} = rootSpan Tag.G2 K {rR, rU, rV, rB, rC} := by
      unfold parabolicRadical; rw [radicalRoots_zero]
    rwa [this] at hq
  refine (commute_of_mem_closure' (g := q) ?_ hn).eq
  rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
  · refine rootSpan_commute (fun β hβ c => ?_) hq'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl | rfl | rfl
    · exact comm_rb c y
    · exact comm_ub c y
    · exact comm_vb c y
    · exact gX_comm_self _ c y
    · exact (comm_bc y c).symm
  · refine rootSpan_commute (fun β hβ c => ?_) hq'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl | rfl | rfl
    · exact comm_rc c y
    · exact comm_uc c y
    · exact comm_vc c y
    · exact comm_bc c y
    · exact gX_comm_self _ c y

theorem N1_le_centralizer
    :
    (N1 : Subgroup (ModGL Tag.G2 K)) ≤
      Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : q ∈ rootSpan Tag.G2 K {rA, rU, rV, rB, rC} := by
    have : parabolicRadical Tag.G2 K {i1} = rootSpan Tag.G2 K {rA, rU, rV, rB, rC} := by
      unfold parabolicRadical; rw [radicalRoots_one]
    rwa [this] at hq
  refine (commute_of_mem_closure' (g := q) ?_ hn).eq
  rintro x ⟨y, rfl⟩
  refine rootSpan_commute (fun β hβ c => ?_) hq'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl
  · exact comm_ac c y
  · exact comm_uc c y
  · exact comm_vc c y
  · exact comm_bc c y
  · exact gX_comm_self _ c y

theorem commutator_of_commute {M : Type*} [Group M] {a b : M} (h : Commute a b) : ⁅a, b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 h.eq

theorem nonabelian_zero
    :
    ∃ x ∈ parabolicRadical Tag.G2 K {i0}, ∃ y ∈ parabolicRadical Tag.G2 K {i0}, x * y ≠ y * x := by
  refine ⟨gX rR (1 : K), mem_zero (Or.inl rfl) 1, gX rU (1 : K),
    mem_zero (Or.inr (Or.inl rfl)) 1, fun h => ?_⟩
  have h1 : ⁅gX rR (1 : K), gX rU (1 : K)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [rel_ru] at h1
  have h2 : gX rB ((1 : K) ^ 2 * 1) * gX rC (1 * (1 : K) ^ 2) = 1 := by
    rw [(comm_bc ((1 : K) ^ 2 * 1) (1 * (1 : K) ^ 2)).eq]; exact h1
  have h3 := (prod_bc_eq_one h2).1
  simp at h3

theorem nonabelian_one
    :
    ∃ x ∈ parabolicRadical Tag.G2 K {i1}, ∃ y ∈ parabolicRadical Tag.G2 K {i1}, x * y ≠ y * x := by
  refine ⟨gX rA (1 : K), mem_one (Or.inl rfl) 1, gX rB (1 : K),
    mem_one (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1, fun h => ?_⟩
  have h1 : ⁅gX rA (1 : K), gX rB (1 : K)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [rel_ab] at h1
  have h3 := gX_eq_one h1
  simp at h3

theorem center_le_zero
    :
    parabolicRadical Tag.G2 K {i0} ⊓
        Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K)) ≤
      ⁅parabolicRadical Tag.G2 K {i0}, parabolicRadical Tag.G2 K {i0}⁆ := by
  rintro z ⟨hzQ, hzC⟩
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_zero hzQ
  have hN := N0_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i0} := fun hd c => mem_zero hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i0},
      ⁅gX rR t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N0 := N0.one_mem
  have hr : gX rR t₁ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i0} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i0} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have st1 := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
  have v1 : ⁅gX rR t₁, gX rV (1 : K)⁆ = gX rB (t₁ * 1) := rel_rv _ _
  have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
  have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
  have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [v2]; exact gX_c_mem_N0 _)
    (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
    v1, v2, v3, v4, v5] at st1
  simp only [one_mul, mul_one] at st1
  rw [← (comm_bc t₁ t₂).eq] at st1
  obtain ⟨rfl, rfl⟩ := prod_bc_eq_one st1
  have st2 := hzg (gX rR 1) (hmem (Or.inl rfl) 1)
  have w1 : ⁅gX rR (0 : K), gX rR (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
  have w2 : ⁅gX rU (0 : K), gX rR (1 : K)⁆ = 1 := by rw [gX_zero]; exact commutatorElement_one_left _
  have w3 : ⁅gX rV t₃, gX rR (1 : K)⁆ = gX rB (1 * t₃) := by
    rw [← commutatorElement_inv, rel_rv, gX_inv]
  have w4 : ⁅gX rB t₄, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rb 1 t₄).symm
  have w5 : ⁅gX rC t₅, gX rR (1 : K)⁆ = 1 := commutator_of_commute (comm_rc 1 t₅).symm
  rw [comm_five hN hr hu hv hb (by rw [w2]; exact h1N)
    (by rw [w3]; exact gX_b_mem_N0 _) (by rw [w4]; exact h1N) (by rw [w5]; exact h1N),
    w1, w2, w3, w4, w5] at st2
  simp only [one_mul, mul_one] at st2
  have ht3 : t₃ = 0 := by simpa using gX_eq_one st2
  subst ht3
  simp only [gX_zero, one_mul]
  have hb' : gX rB t₄ ∈ ⁅parabolicRadical Tag.G2 K {i0}, parabolicRadical Tag.G2 K {i0}⁆ := by
    have := Subgroup.commutator_mem_commutator (hmem (Or.inl rfl) t₄)
      (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    rwa [rel_rv, mul_one] at this
  have hc' : gX rC t₅ ∈ ⁅parabolicRadical Tag.G2 K {i0}, parabolicRadical Tag.G2 K {i0}⁆ := by
    have := Subgroup.commutator_mem_commutator (hmem (Or.inr (Or.inl rfl)) t₅)
      (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    rwa [rel_uv, mul_one] at this
  exact Subgroup.mul_mem _ hb' hc'

theorem center_le_one
    :
    parabolicRadical Tag.G2 K {i1} ⊓
        Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) ≤
      ⁅parabolicRadical Tag.G2 K {i1}, parabolicRadical Tag.G2 K {i1}⁆ := by
  rintro z ⟨hzQ, hzC⟩
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hzQ
  have hN := N1_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rA ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i1} := fun hd c => mem_one hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i1},
      ⁅gX rA t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N1 := N1.one_mem
  have ha : gX rA t₁ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i1} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have ht₁ : t₁ = 0 := by
    have st := hzg (gX rB 1) (hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1)
    have v1 : ⁅gX rA t₁, gX rB (1 : K)⁆ = gX rC (t₁ * 1) := rel_ab _ _
    have v2 : ⁅gX rU t₂, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_ub _ _)
    have v3 : ⁅gX rV t₃, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_vb _ _)
    have v4 : ⁅gX rB t₄, gX rB (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v5 : ⁅gX rC t₅, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_bc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₂ : t₂ = 0 := by
    have st := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    have v1 : ⁅gX rA t₁, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_av _ _)
    have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
    have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact gX_c_mem_N1 _)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₃ : t₃ = 0 := by
    have st := hzg (gX rU 1) (hmem (Or.inr (Or.inl rfl)) 1)
    have v1 : ⁅gX rA t₁, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_au _ _)
    have v2 : ⁅gX rU t₂, gX rU (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v3 : ⁅gX rV t₃, gX rU (1 : K)⁆ = gX rC (1 * t₃) := by
      rw [← commutatorElement_inv, rel_uv, gX_inv]
    have v4 : ⁅gX rB t₄, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_ub 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_uc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact gX_c_mem_N1 _) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₄ : t₄ = 0 := by
    have st := hzg (gX rA 1) (hmem (Or.inl rfl) 1)
    have v1 : ⁅gX rA t₁, gX rA (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v2 : ⁅gX rU t₂, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_au 1 t₂).symm
    have v3 : ⁅gX rV t₃, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_av 1 t₃).symm
    have v4 : ⁅gX rB t₄, gX rA (1 : K)⁆ = gX rC (1 * t₄) := by
      rw [← commutatorElement_inv, rel_ab, gX_inv]
    have v5 : ⁅gX rC t₅, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_ac 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact gX_c_mem_N1 _) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  subst ht₁ ht₂ ht₃ ht₄
  simp only [gX_zero, one_mul]
  have := Subgroup.commutator_mem_commutator (hmem (Or.inl rfl) t₅)
    (hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1)
  rwa [rel_ab, mul_one] at this

end Center

section Levi

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem rootOne_gX_i0
    (c : K) : xUnit Tag.G2 K i0 c = gX rA c := by
  rw [← pinnedX_single, single_i0]

omit [CharP K 2] in
theorem rootOne_gX_i1
    (c : K) : xUnit Tag.G2 K i1 c = gX rR c := by
  rw [← pinnedX_single, single_i1]

omit [CharP K 2] in
theorem rootOne_neg_i1
    (c : K) : yUnit Tag.G2 K i1 c = gX rNR c := by
  rw [← pinnedX_neg_single]
  congr 1
  funext i
  rcases fin_two_cases i with rfl | rfl
  · decide
  · decide

theorem rankOne_data
    (i : Fin Tag.G2.rank) :
    ∃ ρ : SL2 K →* ModGL Tag.G2 K, Function.Injective ρ ∧
      (∀ t, ρ (HSL t) = torusElt Tag.G2 K i t) ∧
      ρ.range = Subgroup.closure (Set.range (xUnit Tag.G2 K i) ∪ Set.range (yUnit Tag.G2 K i)) := by
  obtain ⟨ρ, -, -, hH, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image Tag.G2 K i
  refine ⟨ρ, ?_, hH, hrange⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hker g hg
  have hl1 : (l : K) = 1 := by
    have h2 : ((l : K) - 1) ^ 2 = 0 := by
      linear_combination hl + (1 - (l : K)) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hgl, hl1, one_smul]
  rfl

theorem torus_comm
    (i : Fin Tag.G2.rank) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β)
    (t : Kˣ) (c : K) :
    ⁅torusElt Tag.G2 K i t, gX β c⁆ =
      gX β ((((t ^ (∑ j, Tag.G2.cartan i j * β j) : Kˣ) : K) + 1) * c) := by
  have h := root_torus_conjugation (τ := Tag.G2) (R := K) i hβ t c
  rw [commutatorElement_def, h, gX_inv, ← gX_add]
  congr 1
  ring

theorem mem_of_torus
    {E : Subgroup (ModGL Tag.G2 K)} (i : Fin Tag.G2.rank)
    {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β) {t : Kˣ}
    (ht : (((t ^ (∑ j, Tag.G2.cartan i j * β j) : Kˣ) : K) ≠ 1))
    (hE : ∀ c : K, ⁅torusElt Tag.G2 K i t, gX β c⁆ ∈ E) (c : K) : gX β c ∈ E := by
  set w : K := ((t ^ (∑ j, Tag.G2.cartan i j * β j) : Kˣ) : K) with hwdef
  have hw : w + 1 ≠ 0 := by
    intro h
    apply ht
    have h' : w = -1 := eq_neg_of_add_eq_zero_left h
    rw [h', CharTwo.neg_eq]
  have := hE ((w + 1)⁻¹ * c)
  rwa [torus_comm i hβ t, ← mul_assoc, mul_inv_cancel₀ hw, one_mul] at this

omit [CharP K 2] in
theorem commutator_mem_of_normalizes {M : Type*} [Group M] {E : Subgroup M} {q : M}
    (hq : q ∈ Subgroup.normalizer (E : Set M)) {e : M} (he : e ∈ E) : ⁅q, e⁆ ∈ E := by
  have h1 : q * e * q⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hq e).1 he
  have : ⁅q, e⁆ = (q * e * q⁻¹) * e⁻¹ := by simp [commutatorElement_def]
  rw [this]
  exact E.mul_mem h1 (E.inv_mem he)

theorem leviL_data
    [Finite K] (hK4 : 4 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    ∃ L : Subgroup (ModGL Tag.G2 K), L ≤ parabolicSubgroup Tag.G2 K {i} ∧ ⁅L, L⁆ = L ∧
      (∀ c : K, xUnit Tag.G2 K i c ∈ L) ∧ (∀ c : K, yUnit Tag.G2 K i c ∈ L) ∧
      (∀ t : Kˣ, torusElt Tag.G2 K i t ∈ L) := by
  obtain ⟨ρ, hρ, hH, hrange⟩ := rankOne_data (K := K) i
  have h4 : ∃ s : Finset K, s.card = 4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK4
  refine ⟨ρ.range, ?_, ?_, fun c => ?_, fun c => ?_, fun t => ⟨HSL t, hH t⟩⟩
  · have hLM : ρ.range ≤ parabolicLevi Tag.G2 K {i} := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact xUnit_mem_parabolicLevi (Set.mem_singleton i) c
      · exact yUnit_mem_parabolicLevi (Set.mem_singleton i) c
    exact hLM.trans (parabolicLevi_le_parabolicSubgroup {i})
  · have := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) h4
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  · rw [hrange]; exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  · rw [hrange]; exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

omit [CharP K 2] in
theorem exists_units_ne_one
    [Finite K] (hK4 : 4 ≤ Nat.card K) : ∃ t : Kˣ, t ≠ 1 := by
  obtain ⟨u, hu⟩ := CFSG.LieType.BorelTits.exists_units_sq_ne_one hK4
  exact ⟨u, fun h => hu (by rw [h]; simp)⟩

omit [CharP K 2] in
theorem zpow_val_ne_one {t : Kˣ} (ht : t ≠ 1) {m : ℤ} (hm : m = 1 ∨ m = -1) :
    (((t ^ m : Kˣ)) : K) ≠ 1 := by
  rcases hm with rfl | rfl
  · simpa using ht
  · simpa using ht

theorem generated_zero
    [Finite K] (hK4 : 4 ≤ Nat.card K) :
    parabolicRadical Tag.G2 K {i0} ≤
      ⁅parabolicRadical Tag.G2 K {i0},
        CFSG.Quasithin.perfectCore (parabolicSubgroup Tag.G2 K {i0})⁆ := by
  obtain ⟨L, hLP, hL, hx, hy, hh⟩ := leviL_data hK4 i0
  obtain ⟨t, ht⟩ := exists_units_ne_one (K := K) hK4
  set P := parabolicSubgroup Tag.G2 K {i0} with hPdef
  set Q := parabolicRadical Tag.G2 K {i0} with hQdef
  set E := ⁅Q, CFSG.Quasithin.perfectCore P⁆ with hEdef
  have hLcore : L ≤ CFSG.Quasithin.perfectCore P := CFSG.Quasithin.le_perfectCore_of_perfect hLP hL
  have hQP : Q ≤ P := (parabolicRadical_le_posUnipotent {i0}).trans
    (posUnipotent_le_parabolicSubgroup {i0})
  have hQN : Q ≤ Subgroup.normalizer (E : Set (ModGL Tag.G2 K)) :=
    le_normalizer_commutator_of_le_normalizer Q Q _ Subgroup.le_normalizer
      (hQP.trans (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P)))
  have hLQ : ∀ ℓ ∈ L, ∀ q ∈ Q, ⁅ℓ, q⁆ ∈ E := by
    intro ℓ hℓ q hq
    rw [← commutatorElement_inv q ℓ]
    exact E.inv_mem (Subgroup.commutator_mem_commutator hq (hLcore hℓ))
  have hQL : ∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ E := fun q hq ℓ hℓ =>
    Subgroup.commutator_mem_commutator hq (hLcore hℓ)
  have hrad : ∀ β, (β = rR ∨ β = rU ∨ β = rV ∨ β = rB ∨ β = rC) → IsRoot Tag.G2 β := by
    intro β hβ
    have : β = rA ∨ β = rR ∨ β = rU ∨ β = rV ∨ β = rB ∨ β = rC := by tauto
    exact (isRoot_pos_iff.2 this).1
  have htor : ∀ β, (β = rR ∨ β = rU ∨ β = rB ∨ β = rC) →
      (∑ j, Tag.G2.cartan i0 j * β j = 1 ∨ ∑ j, Tag.G2.cartan i0 j * β j = -1) := by
    intro β hβ
    rcases hβ with rfl | rfl | rfl | rfl
    · right; decide
    · left; decide
    · right; decide
    · left; decide
  have hXtor : ∀ β, (β = rR ∨ β = rU ∨ β = rB ∨ β = rC) → ∀ c : K, gX β c ∈ E := by
    intro β hβ c
    exact mem_of_torus i0 (hrad β (by tauto)) (t := t)
      (zpow_val_ne_one ht (htor β hβ))
      (fun c' => hLQ _ (hh t) _ (mem_zero (by tauto) c')) c
  have hXv : ∀ c : K, gX rV c ∈ E := by
    intro c
    have h1 : ⁅gX rA c, gX rR (1 : K)⁆ ∈ E :=
      hLQ _ (by rw [← rootOne_gX_i0]; exact hx c) _ (mem_zero (Or.inl rfl) 1)
    rw [rel_ar] at h1
    have e1 : gX rU (c * 1) ∈ E := hXtor rU (by tauto) _
    have e2 : gX rB (c * 1 ^ 3) ∈ E := hXtor rB (by tauto) _
    have e3 : gX rC (c ^ 2 * 1 ^ 3) ∈ E := hXtor rC (by tauto) _
    have : gX rV (c * 1 ^ 2) = (gX rU (c * 1))⁻¹ *
        (gX rU (c * 1) * gX rV (c * 1 ^ 2) * gX rB (c * 1 ^ 3) * gX rC (c ^ 2 * 1 ^ 3)) *
        (gX rB (c * 1 ^ 3) * gX rC (c ^ 2 * 1 ^ 3))⁻¹ := by group
    have h2 : gX rV (c * 1 ^ 2) ∈ E := by
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem e1) h1) (E.inv_mem (E.mul_mem e2 e3))
    simpa using h2
  have hQeq : Q = rootSpan Tag.G2 K {rR, rU, rV, rB, rC} := by
    rw [hQdef]; unfold parabolicRadical; rw [radicalRoots_zero]
  rw [hQeq]
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl
  · exact hXtor rR (by tauto) c
  · exact hXtor rU (by tauto) c
  · exact hXv c
  · exact hXtor rB (by tauto) c
  · exact hXtor rC (by tauto) c

theorem generated_one
    [Finite K] (hK4 : 4 ≤ Nat.card K) :
    parabolicRadical Tag.G2 K {i1} ≤
      ⁅parabolicRadical Tag.G2 K {i1},
        CFSG.Quasithin.perfectCore (parabolicSubgroup Tag.G2 K {i1})⁆ := by
  obtain ⟨L, hLP, hL, hx, hy, hh⟩ := leviL_data hK4 i1
  obtain ⟨t, ht⟩ := exists_units_ne_one (K := K) hK4
  set P := parabolicSubgroup Tag.G2 K {i1} with hPdef
  set Q := parabolicRadical Tag.G2 K {i1} with hQdef
  set E := ⁅Q, CFSG.Quasithin.perfectCore P⁆ with hEdef
  have hLcore : L ≤ CFSG.Quasithin.perfectCore P := CFSG.Quasithin.le_perfectCore_of_perfect hLP hL
  have hQP : Q ≤ P := (parabolicRadical_le_posUnipotent {i1}).trans
    (posUnipotent_le_parabolicSubgroup {i1})
  have hQN : Q ≤ Subgroup.normalizer (E : Set (ModGL Tag.G2 K)) :=
    le_normalizer_commutator_of_le_normalizer Q Q _ Subgroup.le_normalizer
      (hQP.trans (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P)))
  have hLQ : ∀ ℓ ∈ L, ∀ q ∈ Q, ⁅ℓ, q⁆ ∈ E := by
    intro ℓ hℓ q hq
    rw [← commutatorElement_inv q ℓ]
    exact E.inv_mem (Subgroup.commutator_mem_commutator hq (hLcore hℓ))
  have hQL : ∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ E := fun q hq ℓ hℓ =>
    Subgroup.commutator_mem_commutator hq (hLcore hℓ)
  have hrad : ∀ β, (β = rA ∨ β = rU ∨ β = rV ∨ β = rB ∨ β = rC) → IsRoot Tag.G2 β := by
    intro β hβ
    have : β = rA ∨ β = rR ∨ β = rU ∨ β = rV ∨ β = rB ∨ β = rC := by tauto
    exact (isRoot_pos_iff.2 this).1
  have htor : ∀ β, (β = rU ∨ β = rV) →
      (∑ j, Tag.G2.cartan i1 j * β j = 1 ∨ ∑ j, Tag.G2.cartan i1 j * β j = -1) := by
    intro β hβ
    rcases hβ with rfl | rfl
    · right; decide
    · left; decide
  have hXtor : ∀ β, (β = rU ∨ β = rV) → ∀ c : K, gX β c ∈ E := by
    intro β hβ c
    exact mem_of_torus i1 (hrad β (by tauto)) (t := t)
      (zpow_val_ne_one ht (htor β hβ))
      (fun c' => hLQ _ (hh t) _ (mem_one (by tauto) c')) c
  have hXc : ∀ c : K, gX rC c ∈ E := by
    intro c
    have h1 : ⁅gX rU c, gX rV (1 : K)⁆ ∈ E :=
      commutator_mem_of_normalizes (hQN (mem_one (Or.inr (Or.inl rfl)) c)) (hXtor rV (by tauto) 1)
    rw [rel_uv] at h1
    simpa using h1
  have hXb : ∀ c : K, gX rB c ∈ E := by
    intro c
    have h1 : ⁅gX rR c, gX rV (1 : K)⁆ ∈ E :=
      hLQ _ (by rw [← rootOne_gX_i1]; exact hx c) _ (mem_one (Or.inr (Or.inr (Or.inl rfl))) 1)
    rw [rel_rv] at h1
    simpa using h1
  have hXa : ∀ c : K, gX rA c ∈ E := by
    intro c
    have h1 : ⁅gX rV c, gX rNR (1 : K)⁆ ∈ E :=
      hQL _ (mem_one (Or.inr (Or.inr (Or.inl rfl))) c) _ (by rw [← rootOne_neg_i1]; exact hy 1)
    rw [rel_vnr] at h1
    have e : gX rC (c ^ 2 * 1) ∈ E := hXc _
    have : gX rA (c * 1 ^ 2) = (gX rA (c * 1 ^ 2) * gX rC (c ^ 2 * 1)) * (gX rC (c ^ 2 * 1))⁻¹ := by
      group
    have h2 : gX rA (c * 1 ^ 2) ∈ E := by
      rw [this]; exact E.mul_mem h1 (E.inv_mem e)
    simpa using h2
  have hQeq : Q = rootSpan Tag.G2 K {rA, rU, rV, rB, rC} := by
    rw [hQdef]; unfold parabolicRadical; rw [radicalRoots_one]
  rw [hQeq]
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl
  · exact hXa c
  · exact hXtor rU (by tauto) c
  · exact hXtor rV (by tauto) c
  · exact hXb c
  · exact hXc c

end Levi

section Facts

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem levi_hom
    (hK4 : 4 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    ∃ (T : Type) (_ : Group T)
      (g : ↥(CFSG.Quasithin.perfectCore (parabolicSubgroup Tag.G2 K {i})) →* T),
      IsSimpleGroup T ∧ Function.Surjective g ∧
        ∀ x, g x = 1 → (x : ModGL Tag.G2 K) ∈ parabolicRadical Tag.G2 K {i} := by
  have h4 : ∃ s : Finset K, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK4
  obtain ⟨ρ, hρ, hLM, hL, hMinf⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.levi_data h4 i
  have hQP : parabolicRadical Tag.G2 K {i} ≤ parabolicSubgroup Tag.G2 K {i} :=
    (parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})
  obtain ⟨g, hg, hk⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom hQP
    (parabolicSubgroup_le_normalizer_parabolicRadical {i}) (parabolicRadical_inf_parabolicLevi {i})
    (parabolicRadical_sup_parabolicLevi {i}) hLM hL hMinf
  have hsimple : IsSimpleGroup (SL2 K) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple h4
  exact ⟨↥ρ.range, inferInstance, g, (MonoidHom.ofInjective hρ).symm.isSimpleGroup, hg, hk⟩

omit [CharP K 2] in
theorem pGroup_radical
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (J : Set (Fin Tag.G2.rank)) :
    IsPGroup 2 ↥(parabolicRadical Tag.G2 K J) := by
  refine IsPGroup.of_card (n := f * (parabolicRadicalRoots Tag.G2 J).ncard) ?_
  rw [card_parabolicRadical, hK, ← pow_mul]

theorem parabolicFacts_zero
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ParabolicFacts (parabolicSubgroup Tag.G2 K {i0}) (parabolicRadical Tag.G2 K {i0}) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hJ : ({i0} : Set (Fin Tag.G2.rank)) ≠ Set.univ := fun h =>
    absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ i1)) (by decide)
  exact
    { le := (parabolicRadical_le_posUnipotent {i0}).trans (posUnipotent_le_parabolicSubgroup {i0})
      normalizes := parabolicSubgroup_le_normalizer_parabolicRadical {i0}
      pGroup := pGroup_radical hK {i0}
      selfCentralizing :=
        (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2
      center_le := center_le_zero
      nonabelian := nonabelian_zero
      levi := Or.inr ⟨generated_zero hK4, levi_hom hK4 i0⟩ }

theorem parabolicFacts_one
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ParabolicFacts (parabolicSubgroup Tag.G2 K {i1}) (parabolicRadical Tag.G2 K {i1}) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hJ : ({i1} : Set (Fin Tag.G2.rank)) ≠ Set.univ := fun h =>
    absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ i0)) (by decide)
  exact
    { le := (parabolicRadical_le_posUnipotent {i1}).trans (posUnipotent_le_parabolicSubgroup {i1})
      normalizes := parabolicSubgroup_le_normalizer_parabolicRadical {i1}
      pGroup := pGroup_radical hK {i1}
      selfCentralizing :=
        (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2
      center_le := center_le_one
      nonabelian := nonabelian_one
      levi := Or.inr ⟨generated_one hK4, levi_hom hK4 i1⟩ }

end Facts

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
