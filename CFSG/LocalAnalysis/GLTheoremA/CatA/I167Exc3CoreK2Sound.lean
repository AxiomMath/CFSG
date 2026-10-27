module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreK2Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_orthRow_testBit {τ : Tag} (hτ : NoG2 τ) {k : ℕ} (hk : k < τ.artifactRoots.length)
    (l : ℕ) :
    (exc3core_orthRow τ k).testBit l = decide (l < τ.artifactRoots.length ∧
      iform (RD.rt τ k) (RD.rt τ l) = 0) := by
  have hrow := RD.rowOf_spec (τ := τ) k l
  rw [exc3core_orthRow]
  change ((2 ^ τ.artifactRoots.length - 1) ^^^ RD.rowM2 τ (2 ^ k)).testBit l = decide
    (l < τ.artifactRoots.length ∧ iform (RD.rt τ k) (RD.rt τ l) = 0)
  rw [Nat.testBit_xor, RD.rowM2_pow hτ, Nat.testBit_two_pow_sub_one]
  by_cases hl : l < τ.artifactRoots.length
  · by_cases h : iform (RD.rt τ k) (RD.rt τ l) = 0
    · have hb : (RD.rowOf τ k).testBit l = false := by
        cases hbit : (RD.rowOf τ k).testBit l
        · rfl
        · exact absurd h ((hrow.mp hbit).2.2)
      rw [hb, decide_eq_true hl, Bool.true_xor]
      simp [hb, hl, h]
    · have hb : (RD.rowOf τ k).testBit l = true := hrow.mpr ⟨hk, hl, h⟩
      rw [hb, decide_eq_true hl, Bool.true_xor]
      simp [hb, hl, h]
  · have hb : (RD.rowOf τ k).testBit l = false := by
      cases hbit : (RD.rowOf τ k).testBit l
      · rfl
      · exact absurd hbit (fun hb' => hl (hrow.mp hb').2.1)
    rw [decide_eq_false hl, Bool.false_xor, hb]
    simp [hl]

private theorem exc3core_orthSet_testBit_aux1 (τ : Tag) (V l : ℕ) :
    ∀ (L : List ℕ) (acc : ℕ),
      (L.foldl (fun acc δ => if V.testBit δ then Nat.lor acc (RD.rowM2 τ (2 ^ δ)) else acc)
        acc).testBit l = true ↔
        acc.testBit l = true ∨ ∃ δ ∈ L, V.testBit δ = true ∧ (RD.rowM2 τ (2 ^ δ)).testBit l = true := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons δ L ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases hV : V.testBit δ = true
    · rw [if_pos hV, ih (Nat.lor acc (RD.rowM2 τ (2 ^ δ)))]
      rw [show Nat.lor acc (RD.rowM2 τ (2 ^ δ)) = (acc ||| RD.rowM2 τ (2 ^ δ)) from rfl,
        Nat.testBit_lor, Bool.or_eq_true]
      constructor
      · rintro ((h | h) | ⟨δ', hδ', hv', hb'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨δ, List.mem_cons_self, hV, h⟩
        · exact Or.inr ⟨δ', List.mem_cons_of_mem _ hδ', hv', hb'⟩
      · rintro (h | ⟨δ', hδ', hv', hb'⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hδ' with hδ'' | hδ'
          · subst δ'
            exact Or.inl (Or.inr hb')
          · exact Or.inr ⟨δ', hδ', hv', hb'⟩
    · rw [if_neg hV, ih acc]
      constructor
      · rintro (h | ⟨δ', hδ', hv', hb'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨δ', List.mem_cons_of_mem _ hδ', hv', hb'⟩
      · rintro (h | ⟨δ', hδ', hv', hb'⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hδ' with rfl | hδ'
          · exact absurd hv' hV
          · exact Or.inr ⟨δ', hδ', hv', hb'⟩

private theorem exc3core_orthSet_testBit_aux2 {τ : Tag} (hτ : NoG2 τ) (V l : ℕ) :
    (exc3core_unionRows τ V).testBit l =
      decide (l < τ.artifactRoots.length ∧ ∃ δ, δ < τ.artifactRoots.length ∧
        V.testBit δ = true ∧ iform (RD.rt τ δ) (RD.rt τ l) ≠ 0) := by
  have hU : (exc3core_unionRows τ V).testBit l = true ↔
      l < τ.artifactRoots.length ∧ ∃ δ, δ < τ.artifactRoots.length ∧ V.testBit δ = true ∧
        iform (RD.rt τ δ) (RD.rt τ l) ≠ 0 := by
    rw [exc3core_unionRows, exc3core_orthSet_testBit_aux1]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range]
    constructor
    · rintro ⟨δ, hδ, hv, hb⟩
      rw [RD.rowM2_pow hτ, RD.rowOf_spec] at hb
      exact ⟨hb.2.1, δ, hδ, hv, hb.2.2⟩
    · rintro ⟨hl, δ, hδ, hv, hne⟩
      exact ⟨δ, hδ, hv, by rw [RD.rowM2_pow hτ, RD.rowOf_spec]; exact ⟨hδ, hl, hne⟩⟩
  by_cases hb : (exc3core_unionRows τ V).testBit l = true
  · rw [hb, decide_eq_true (hU.mp hb)]
  · have hbf : (exc3core_unionRows τ V).testBit l = false := by simpa using hb
    rw [hbf, decide_eq_false (fun hp => hb (hU.mpr hp))]

private theorem exc3core_orthSet_testBit_aux3 {τ : Tag} (hτ : NoG2 τ) (V l : ℕ) :
    (exc3core_orthSet τ V).testBit l = true ↔
      (l < τ.artifactRoots.length ∧ ∀ δ, δ < τ.artifactRoots.length → V.testBit δ = true →
        iform (RD.rt τ δ) (RD.rt τ l) = 0) := by
  rw [exc3core_orthSet]
  rw [show Nat.xor (2 ^ τ.artifactRoots.length - 1) (exc3core_unionRows τ V) =
    ((2 ^ τ.artifactRoots.length - 1) ^^^ exc3core_unionRows τ V) from rfl,
    Nat.testBit_xor, Nat.testBit_two_pow_sub_one, exc3core_orthSet_testBit_aux2 hτ]
  by_cases hl : l < τ.artifactRoots.length
  · have hP : (l < τ.artifactRoots.length ∧ ∃ δ, δ < τ.artifactRoots.length ∧ V.testBit δ = true ∧
        iform (RD.rt τ δ) (RD.rt τ l) ≠ 0) ↔
        (∃ δ, δ < τ.artifactRoots.length ∧ V.testBit δ = true ∧
          iform (RD.rt τ δ) (RD.rt τ l) ≠ 0) := and_iff_right hl
    have hQ : (l < τ.artifactRoots.length ∧ ∀ δ, δ < τ.artifactRoots.length → V.testBit δ = true →
        iform (RD.rt τ δ) (RD.rt τ l) = 0) ↔
        (∀ δ, δ < τ.artifactRoots.length → V.testBit δ = true →
          iform (RD.rt τ δ) (RD.rt τ l) = 0) := and_iff_right hl
    rw [decide_eq_true hl, Bool.true_xor, not_decide_eq_true, hP, hQ]
    constructor
    · rintro h δ hδ hv
      by_contra hne
      exact h ⟨δ, hδ, hv, hne⟩
    · rintro h ⟨δ, hδ, hv, hne⟩
      exact hne (h δ hδ hv)
  · have hdl : decide (l < τ.artifactRoots.length) = false := decide_eq_false hl
    have hP : ¬ (l < τ.artifactRoots.length ∧ ∃ δ, δ < τ.artifactRoots.length ∧ V.testBit δ = true ∧
        iform (RD.rt τ δ) (RD.rt τ l) ≠ 0) := fun h => hl h.1
    rw [hdl, Bool.false_xor, decide_eq_false hP, Bool.false_eq_true]
    exact ⟨fun h => h.elim, fun h => absurd h.1 hl⟩

theorem exc3core_orthSet_testBit {τ : Tag} (hτ : NoG2 τ) (V l : ℕ) :
    (exc3core_orthSet τ V).testBit l = decide (l < τ.artifactRoots.length ∧
      ∀ δ, δ < τ.artifactRoots.length → V.testBit δ = true → iform (RD.rt τ δ) (RD.rt τ l) = 0) := by
  have hiff := exc3core_orthSet_testBit_aux3 hτ V l
  by_cases hb : (exc3core_orthSet τ V).testBit l = true
  · rw [hb, decide_eq_true (hiff.mp hb)]
  · have hbf : (exc3core_orthSet τ V).testBit l = false := by simpa using hb
    rw [hbf, decide_eq_false (fun hp => hb (hiff.mpr hp))]

theorem exc3core_k2Obs_unpack {τ : Tag} {V : ℕ} (h : exc3core_k2Obs τ V = true) :
    ∃ k, k < τ.artifactRoots.length ∧ V = exc3core_orthRow τ k ∧
      RD.cnt2 3 (exc3core_orthSet τ V) = 2 := by
  rw [exc3core_k2Obs, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.any_eq_true] at h1
  obtain ⟨k, hk, hk'⟩ := h1
  rw [List.mem_range] at hk
  exact ⟨k, hk, beq_iff_eq.mp hk', beq_iff_eq.mp h2⟩

theorem exc3core_orth_class_iff {τ : Tag} (hτ : NoG2 τ) {k : ℕ} (hk : k < τ.artifactRoots.length) :
    ∀ α, IsRoot τ α → (iform α (RD.rt τ k) = 0 ↔
      α ∈ RD.rt τ '' RD.bitsSet (exc3core_orthRow τ k)) := by
  intro α hα
  obtain ⟨l, hl, rfl⟩ := RD.isRoot_iff_exists_rt.1 hα
  constructor
  · intro h0
    refine ⟨l, ?_, rfl⟩
    simp only [RD.bitsSet, Set.mem_setOf_eq]
    rw [exc3core_orthRow_testBit hτ hk l]
    exact decide_eq_true ⟨hl, by rwa [iform_comm]⟩
  · rintro ⟨x, hx, hxl⟩
    simp only [RD.bitsSet, Set.mem_setOf_eq] at hx
    have hdec : decide (x < τ.artifactRoots.length ∧ iform (RD.rt τ k) (RD.rt τ x) = 0) = true :=
      (exc3core_orthRow_testBit hτ hk x).symm.trans hx
    have hif : iform (RD.rt τ k) (RD.rt τ l) = 0 := by
      have h := (of_decide_eq_true hdec).2
      rwa [hxl] at h
    rwa [iform_comm] at hif

private theorem exc3core_orth_orth_aux1 {τ : Tag} (hτ : NoG2 τ) {k : ℕ}
    (hk : k < τ.artifactRoots.length) :
    k ∈ RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k)) := by
  simp only [RD.bitsSet, Set.mem_setOf_eq]
  rw [exc3core_orthSet_testBit hτ (exc3core_orthRow τ k) k]
  refine decide_eq_true ⟨hk, ?_⟩
  intro δ _ hVδ
  have hdec : decide (δ < τ.artifactRoots.length ∧ iform (RD.rt τ k) (RD.rt τ δ) = 0) = true := by
    rw [← exc3core_orthRow_testBit hτ hk δ]; exact hVδ
  rw [iform_comm]
  exact (of_decide_eq_true hdec).2

private theorem exc3core_orth_orth_aux2 {τ : Tag} (hτ : NoG2 τ) {k k' : ℕ}
    (hk : k < τ.artifactRoots.length) (hk' : k' < τ.artifactRoots.length)
    (hneg : -RD.rt τ k = RD.rt τ k') :
    k' ∈ RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k)) := by
  simp only [RD.bitsSet, Set.mem_setOf_eq]
  rw [exc3core_orthSet_testBit hτ (exc3core_orthRow τ k) k']
  refine decide_eq_true ⟨hk', ?_⟩
  intro δ _ hVδ
  have hdec : decide (δ < τ.artifactRoots.length ∧ iform (RD.rt τ k) (RD.rt τ δ) = 0) = true := by
    rw [← exc3core_orthRow_testBit hτ hk δ]; exact hVδ
  have hif : iform (RD.rt τ k) (RD.rt τ δ) = 0 := (of_decide_eq_true hdec).2
  have hiff : iform (RD.rt τ δ) (RD.rt τ k') = -iform (RD.rt τ k) (RD.rt τ δ) := by
    rw [hneg.symm, iform_neg_right, iform_comm]
  simp only [hiff, hif, neg_zero]

private theorem exc3core_orth_orth_aux3 {τ : Tag} (hτ : NoG2 τ) {k k' : ℕ}
    (hk : k < τ.artifactRoots.length) (hk' : k' < τ.artifactRoots.length)
    (hneg : -RD.rt τ k = RD.rt τ k')
    (h2 : RD.cnt2 3 (exc3core_orthSet τ (exc3core_orthRow τ k)) = 2) :
    RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k)) = {k, k'} := by
  have hS2 : (RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k))).ncard = 2 := by
    have h := (RD.cnt2_spec 3 (exc3core_orthSet τ (exc3core_orthRow τ k))).2
      (by rw [h2]; norm_num)
    simpa [h2] using h
  have hkk' : k ≠ k' := by
    intro hEq
    have hneg' : -RD.rt τ k = RD.rt τ k := by rw [← hEq] at hneg; exact hneg
    have hpos := iform_self_pos_of_isRoot (RD.isRoot_rt hk)
    have he : iform (RD.rt τ k) (RD.rt τ k) = -iform (RD.rt τ k) (RD.rt τ k) := by
      rw [← iform_neg_right, hneg']
    linarith
  have hsub : ({k, k'} : Set ℕ) ⊆ RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact exc3core_orth_orth_aux1 hτ hk
    · exact exc3core_orth_orth_aux2 hτ hk hk' hneg
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (RD.bitsSet_finite _)).symm
  simp [hS2, Set.ncard_pair hkk']

theorem exc3core_orth_orth {τ : Tag} (hτ : NoG2 τ) {k : ℕ} (hk : k < τ.artifactRoots.length)
    (h2 : RD.cnt2 3 (exc3core_orthSet τ (exc3core_orthRow τ k)) = 2) :
    ∀ ε, IsRoot τ ε →
      (∀ δ ∈ RD.rt τ '' RD.bitsSet (exc3core_orthRow τ k), iform ε δ = 0) →
        ε = RD.rt τ k ∨ ε = -RD.rt τ k := by
  intro ε hε horth
  obtain ⟨k', hk', hneg⟩ :=
    RD.isRoot_iff_exists_rt.1 (CFSG.LieType.Chevalley.IsRoot.neg (RD.isRoot_rt hk))
  have hSeq := exc3core_orth_orth_aux3 hτ hk hk' hneg h2
  obtain ⟨l, hl, rfl⟩ := RD.isRoot_iff_exists_rt.1 hε
  have hlS : l ∈ RD.bitsSet (exc3core_orthSet τ (exc3core_orthRow τ k)) := by
    simp only [RD.bitsSet, Set.mem_setOf_eq]
    rw [exc3core_orthSet_testBit hτ (exc3core_orthRow τ k) l]
    refine decide_eq_true ⟨hl, ?_⟩
    intro δ _ hVδ
    rw [iform_comm]
    exact horth (RD.rt τ δ) ⟨δ, hVδ, rfl⟩
  rw [hSeq] at hlS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlS
  rcases hlS with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hneg.symm

theorem exc3core_class_extractG {τ : Tag} (hτ : NoG2 τ) (ok : List ℕ → ℕ → Bool)
    (h : ∀ d ∈ RD.allVecs τ.rank,
      RD.compLoop2 (RD.rowM2 τ) (RD.kerMaskFast τ d) (τ.artifactRoots.length + 1) (ok d)
        τ.artifactRoots.length (RD.kerMaskFast τ d) = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (ω₀ : Lˣ) (e : Fin τ.rank → ℕ) (V b k : ℕ) (hkκ : RD.rt τ k ∈ kernelRoots (rootCharHom a)),
      ω₀ ^ 3 = 1 ∧ (∀ j, e j < 3) ∧ (∀ j, a j = ω₀ ^ e j) ∧ (ω₀ = 1 → ∀ j, e j = 0) ∧
      i = Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨RD.rt τ k, hkκ⟩ ∧ V.testBit k = true ∧
      RD.IsComp (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) V b ∧
      ok (List.ofFn e) V = true ∧
      RD.Spec (rootCharHom a) (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) := by
  obtain ⟨ω₀, e, hω₀, he3, hae, he0⟩ := RD.exists_exps a ha
  have hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0 := by
    by_cases h1 : ω₀ = 1
    · exact Or.inr (he0 h1)
    · exact Or.inl h1
  have hdig : ∀ x ∈ List.ofFn e, x < 3 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact he3 j
  have hSpec : RD.Spec (rootCharHom a) (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) :=
    ⟨RD.rowOf_spec, fun l => by
      rw [RD.kerMaskFast_eq _ hdig]
      exact RD.kerMask_spec a ω₀ e hω₀ hae hprim l⟩
  induction i using Quotient.inductionOn with
  | _ x =>
    obtain ⟨α, hα⟩ := x
    obtain ⟨k, hk, rfl⟩ := RD.isRoot_iff_exists_rt.1 hα.1
    have hKk : (RD.kerMaskFast τ (List.ofFn e)).testBit k = true := (hSpec.K_iff k).2 ⟨hk, hα⟩
    have hd := h _ (RD.ofFn_mem_allVecs _ e he3)
    obtain ⟨V, b, hkV, hV, hok⟩ := RD.compLoop2_sound (fun x => RD.rowM2_pow hτ x) _ _ _ _ _
      hd (fun x hx => hx) k hKk
    exact ⟨ω₀, e, V, b, k, hα, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩

theorem exc3core_k2_of_check {τ : Tag} (hτ : NoG2 τ) (cap : ℕ) (hcap : τ.artifactRoots.length < cap)
    (u : ℕ → Bool) (h : ∀ d ∈ RD.allVecs τ.rank, exc3core_k2Check τ cap u d = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hu : u (componentRoots (rootCharHom a) i).ncard = true) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧
      (∀ α, IsRoot τ α → (iform α β = 0 ↔ α ∈ componentRoots (rootCharHom a) i)) ∧
      ∀ ε, IsRoot τ ε → (∀ δ ∈ componentRoots (rootCharHom a) i, iform ε δ = 0) →
        ε = β ∨ ε = -β := by
  obtain ⟨ω₀, e, V, b, k, hkκ, -, -, -, -, hi, hkV, hV, hok, hSpec⟩ :=
    exc3core_class_extractG (τ := τ) hτ (fun _ V => exc3core_k2C τ cap u V) h a ha i
  subst i
  change exc3core_k2C τ cap u V = true at hok
  have hn := RD.ncard_componentRoots_eq hSpec hV hkV hkκ
  have hbnd : (RD.bitsSet V).ncard ≤ τ.artifactRoots.length := by
    have := Set.ncard_le_ncard (s := RD.bitsSet V) (t := Set.Iio τ.artifactRoots.length)
      (fun x hx => ((hSpec.K_iff x).1 (hV.reach x hx).1).1) (Set.finite_Iio _)
    simpa using this
  have hlt : RD.cnt2 cap V < cap := by
    by_contra hc
    have hcv : RD.cnt2 cap V = cap := le_antisymm (RD.cnt2_le cap V) (not_lt.1 hc)
    have := (RD.cnt2_spec cap V).1 hcv
    omega
  have hn' : (RD.bitsSet V).ncard = RD.cnt2 cap V := (RD.cnt2_spec cap V).2 hlt
  have hu' : u (RD.cnt2 cap V) = true := by
    rw [← hn', ← hn]
    exact hu
  have hk2 : exc3core_k2Obs τ V = true := by
    have h := hok
    unfold exc3core_k2C at h
    rw [hu'] at h
    simpa using h
  obtain ⟨k', hk'len, hVeq, hcnt⟩ := exc3core_k2Obs_unpack hk2
  have himg := RD.componentRoots_eq_image hSpec hV hkV hkκ
  refine ⟨RD.rt τ k', RD.isRoot_rt hk'len, ?_, ?_⟩
  · intro α hα
    rw [himg, hVeq]
    exact exc3core_orth_class_iff hτ hk'len α hα
  · intro ε hε horth
    have hcnt' : RD.cnt2 3 (exc3core_orthSet τ (exc3core_orthRow τ k')) = 2 := by
      rw [← hVeq]; exact hcnt
    refine exc3core_orth_orth hτ hk'len hcnt' ε hε ?_
    intro δ hδ
    exact horth δ (by rw [himg, hVeq]; exact hδ)


end CFSG.LocalAnalysis.GLTheoremA.I167

end
