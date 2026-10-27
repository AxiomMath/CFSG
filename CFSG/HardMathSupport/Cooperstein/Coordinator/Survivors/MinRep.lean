module

public import CFSG.LieType.Steinberg.Minuscule.Group
public import CFSG.Quasithin.Background.SmithCurtisMain

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.Quasithin.SmithCurtis

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (K : Type) [Field K]

@[expose] def minRep : Representation K (hV.minGroup K) (Fin D.d →₀ K) where
  toFun := hV.endo K
  map_one' := hV.endo_one K
  map_mul' := hV.endo_mul K

variable {K}

theorem minRep_apply (g : hV.minGroup K) : minRep hV K g = hV.endo K g := rfl

theorem minRep_xm (γ : Fin τ.rank → ℤ) (c : K) :
    minRep hV K (hV.xm K γ c) = 1 + c • D.rootOp K γ := hV.endo_xm K γ c

theorem minRep_nm_single (i : Fin τ.rank) (a : Fin D.d) :
    minRep hV K (hV.nm K i) (Finsupp.single a 1) =
      if D.wt a i = 1 then -Finsupp.single (hV.sRefl i a) 1
      else Finsupp.single (hV.sRefl i a) 1 := by
  rw [minRep_apply, hV.endo_nm]
  exact hV.nOp_single i a

theorem minRep_hm_single (i : Fin τ.rank) (t : Kˣ) (a : Fin D.d) :
    minRep hV K (hV.hm K i t) (Finsupp.single a 1) =
      ((t ^ D.wt a i : Kˣ) : K) • Finsupp.single a 1 := by
  rw [minRep_apply, hV.endo_hm]
  exact D.hDiag_single K i t a

include hV in
theorem rootOp_single_coeff (i : Fin τ.rank) (v : Fin D.d →₀ K) (a : Fin D.d)
    (ha : D.wt a i = -1) : D.rootOp K (Pi.single i 1) v (hV.sRefl i a) = v a := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single b c =>
    have h1 : Finsupp.single b c = c • (Finsupp.single b 1 : Fin D.d →₀ K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hV.rootOp_single_apply]
    by_cases hb : D.wt b i = -1
    · simp only [hb, ite_true]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      by_cases hba : b = a
      · subst hba; simp
      · have : ¬ (hV.sRefl i b = hV.sRefl i a) := fun h => hba (hV.sRefl_injective i h)
        simp [hba, this]
    · have hba : ¬ b = a := fun h => hb (h ▸ ha)
      simp [hb, hba]

include hV in
theorem eq_smul_of_rootOp_eq_zero {a₀ : Fin D.d}
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) {v : Fin D.d →₀ K}
    (hv : ∀ i, D.rootOp K (Pi.single i 1) v = 0) :
    v = v a₀ • Finsupp.single a₀ (1 : K) := by
  ext b
  by_cases hb : ∀ i, D.wt b i ≠ -1
  · have := hdom b hb
    subst this
    simp
  · push Not at hb
    obtain ⟨i, hi⟩ := hb
    have h := rootOp_single_coeff hV i v b hi
    rw [hv i, Finsupp.zero_apply] at h
    by_cases hba : b = a₀
    · subst hba; simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply]
      simp only [show ¬ a₀ = b from fun e => hba e.symm, ite_false, smul_zero]
      exact h.symm

include hV in
theorem minRep_prod_nm_single (l : List (Fin τ.rank)) (b : Fin D.d) :
    ∃ ε : K, IsSign ε ∧ minRep hV K ((l.map (hV.nm K)).prod) (Finsupp.single b 1) =
      ε • Finsupp.single (l.foldr (fun i b => hV.sRefl i b) b) 1 := by
  induction l with
  | nil => exact ⟨1, isSign_one, by simp⟩
  | cons i l ih =>
    obtain ⟨ε, hε, h⟩ := ih
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, List.foldr_cons]
    rw [h, map_smul, minRep_nm_single]
    split_ifs
    · exact ⟨ε * -1, hε.mul isSign_neg_one, by rw [smul_neg, mul_neg_one, neg_smul]⟩
    · exact ⟨ε * 1, hε.mul isSign_one, by rw [mul_one]⟩

@[expose] def reachStep (D : MinData τ) (S : List ℕ) : List ℕ :=
  (S ++ S.flatMap fun a => (List.finRange τ.rank).map fun i => D.weyl a i).eraseDups

@[expose] def reachIter (D : MinData τ) (a₀ : ℕ) : ℕ → List ℕ
  | 0 => [a₀]
  | N + 1 => reachStep D (reachIter D a₀ N)

@[expose] def reachCheck (D : MinData τ) (a₀ N : ℕ) : Bool :=
  (List.range D.d).all fun a => decide (a ∈ reachIter D a₀ N)

section Gen

variable {hV}

theorem span_reach {a₀ : Fin D.d} (N : ℕ) :
    ∀ a ∈ reachIter D a₀ N, ∃ h : a < D.d,
      Finsupp.single (⟨a, h⟩ : Fin D.d) (1 : K) ∈ orbitSpan (minRep hV K) (Finsupp.single a₀ 1) := by
  induction N with
  | zero =>
    intro a ha
    simp only [reachIter, List.mem_singleton] at ha
    subst ha
    exact ⟨a₀.2, mem_orbitSpan_self _ _⟩
  | succ N ih =>
    intro a ha
    simp only [reachIter, reachStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at ha
    rcases ha with ha | ⟨b, hb, i, rfl⟩
    · exact ih a ha
    · obtain ⟨hbd, hbs⟩ := ih b hb
      have hs := orbitSpan_stable (minRep hV K) (Finsupp.single a₀ 1) (hV.nm K i) hbs
      rw [minRep_nm_single] at hs
      have hlt : D.weyl b i < D.d := (hV.sRefl_val i ⟨b, hbd⟩) ▸ (hV.sRefl i ⟨b, hbd⟩).2
      refine ⟨hlt, ?_⟩
      have e : (⟨D.weyl b i, hlt⟩ : Fin D.d) = hV.sRefl i ⟨b, hbd⟩ := Fin.ext (hV.sRefl_val i ⟨b, hbd⟩).symm
      rw [e]
      split_ifs at hs
      · simpa using Submodule.neg_mem _ hs
      · exact hs

theorem orbitSpan_minRep {a₀ : Fin D.d} {N : ℕ} (hN : reachCheck D a₀ N = true) :
    orbitSpan (minRep hV K) (Finsupp.single a₀ 1) = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun v => ?_
  induction v using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single b c =>
    have hb : (b : ℕ) ∈ reachIter D a₀ N := by
      simp only [reachCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hN
      exact hN b b.2
    obtain ⟨h, hs⟩ := span_reach (hV := hV) (K := K) N b hb
    have := Submodule.smul_mem _ c hs
    rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at this

end Gen

instance instFiniteMinGroup [Finite K] : Finite (hV.minGroup K) := by
  have : Finite (Module.End K (Fin D.d →₀ K)) := Module.finite_of_finite K
  infer_instance

section Datum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K]
  (ψ : G →* hV.minGroup K) (D' : CurtisDatum G cs p) {a₀ : Fin D.d}

@[expose] def pullRep : Representation K G (Fin D.d →₀ K) := (minRep hV K).comp ψ

theorem pullRep_apply (g : G) : pullRep hV ψ g = minRep hV K (ψ g) := rfl

include hV in
theorem rootOp_eq_zero_of_mem_fixU
    (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    {v : Fin D.d →₀ K} (hv : v ∈ D'.fixU (pullRep hV ψ)) (i : Fin τ.rank) :
    D.rootOp K (Pi.single i 1) v = 0 := by
  obtain ⟨g, hg, hψ⟩ := hX i
  have h := (D'.mem_fixU _).1 hv g hg
  rw [pullRep_apply, hψ, minRep_xm] at h
  simpa using h

include hV in
theorem fixU_le_line (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) :
    ∀ x ∈ D'.fixU (pullRep hV ψ), ∃ c : K, x = c • Finsupp.single a₀ 1 := fun x hx =>
  ⟨x a₀, eq_smul_of_rootOp_eq_zero hV hdom (rootOp_eq_zero_of_mem_fixU hV ψ D' hX hx)⟩

include hV in
theorem single_mem_fixU [Finite G] (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) :
    (Finsupp.single a₀ (1 : K)) ∈ D'.fixU (pullRep hV ψ) := by
  have : Nontrivial (Fin D.d →₀ K) := ⟨⟨Finsupp.single a₀ 1, 0, fun h => by
    have := congrArg (fun v : Fin D.d →₀ K => v a₀) h
    simp at this⟩⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (D'.fixU_ne_bot (p := p) (pullRep hV ψ))
  obtain ⟨c, rfl⟩ := fixU_le_line hV ψ D' hX hdom x hx
  have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

include hV in
theorem orbitSpan_pullRep (hψ : Function.Surjective ψ) (y : Fin D.d →₀ K) :
    orbitSpan (pullRep hV ψ) y = orbitSpan (minRep hV K) y := by
  unfold orbitSpan
  congr 1
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ψ g, rfl⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨g, rfl⟩ := hψ h
    exact ⟨g, rfl⟩

include hV in
theorem isSimpleRep_pullRep [Finite G] (hψ : Function.Surjective ψ)
    (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) {N : ℕ}
    (hN : reachCheck D a₀ N = true) : IsSimpleRep (pullRep hV ψ) := by
  have : Nontrivial (Fin D.d →₀ K) := ⟨⟨Finsupp.single a₀ 1, 0, fun h => by
    have := congrArg (fun v : Fin D.d →₀ K => v a₀) h
    simp at this⟩⟩
  exact D'.isSimpleRep_of_fixU (p := p) (pullRep hV ψ) (y := Finsupp.single a₀ 1)
    (fixU_le_line hV ψ D' hX hdom)
    (by rw [orbitSpan_pullRep hV ψ hψ]; exact orbitSpan_minRep (hV := hV) hN)

include hV in
theorem pullRep_H_smul [Finite G] (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) {h : G} (hh : h ∈ D'.H) :
    pullRep hV ψ h (Finsupp.single a₀ 1) =
      (pullRep hV ψ h (Finsupp.single a₀ 1) a₀) • Finsupp.single a₀ (1 : K) := by
  obtain ⟨c, hc⟩ := fixU_le_line hV ψ D' hX hdom _
    (D'.act_H_mem_fixU (pullRep hV ψ) hh (single_mem_fixU hV ψ D' hX hdom))
  rw [hc]
  simp

end Datum

section Hecke

variable {a₀ : Fin D.d}

include hV in
theorem minRep_xm_nm_apply (s : Fin τ.rank) (c : K) (v : Fin D.d →₀ K) :
    minRep hV K (hV.xm K (Pi.single s 1) c * hV.nm K s) v =
      minRep hV K (hV.nm K s) v +
        c • D.rootOp K (Pi.single s 1) (minRep hV K (hV.nm K s) v) := by
  rw [map_mul, Module.End.mul_apply, minRep_xm]
  simp

include hV in
theorem minRep_xm_nm_of_wt_zero {s : Fin τ.rank} (h : D.wt a₀ s = 0) (c : K) :
    minRep hV K (hV.xm K (Pi.single s 1) c * hV.nm K s) (Finsupp.single a₀ 1) =
      Finsupp.single a₀ 1 := by
  rw [minRep_xm_nm_apply hV, minRep_nm_single, if_neg (by omega), hV.sRefl_eq_self h,
    hV.rootOp_single_apply, if_neg (by omega), smul_zero, add_zero]

include hV in
theorem minRep_xm_nm_of_wt_one {s : Fin τ.rank} (h : D.wt a₀ s = 1) (c : K) :
    minRep hV K (hV.xm K (Pi.single s 1) c * hV.nm K s) (Finsupp.single a₀ 1) =
      -Finsupp.single (hV.sRefl s a₀) 1 - c • Finsupp.single a₀ 1 := by
  rw [minRep_xm_nm_apply hV, minRep_nm_single, if_pos h, map_neg, hV.rootOp_single_apply,
    if_pos (by rw [hV.wt_sRefl_self, h]), hV.sRefl_sRefl]
  simp [sub_eq_add_neg]

theorem card_smul_eq_zero' (K : Type) [Field K] [Fintype K] {V : Type*} [AddCommGroup V]
    [Module K V] (x : V) : Fintype.card K • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K, Nat.cast_card_eq_zero K, zero_smul]

include hV in
theorem sum_xm_nm_of_wt_zero [Fintype K] {s : Fin τ.rank} (h : D.wt a₀ s = 0) :
    ∑ c : K, minRep hV K (hV.xm K (Pi.single s 1) c * hV.nm K s) (Finsupp.single a₀ 1) = 0 := by
  simp only [minRep_xm_nm_of_wt_zero hV h, Finset.sum_const, Finset.card_univ]
  exact card_smul_eq_zero' K _

include hV in
theorem sum_xm_nm_of_wt_one [Fintype K] {s : Fin τ.rank} (h : D.wt a₀ s = 1) :
    ∑ c : K, minRep hV K (hV.xm K (Pi.single s 1) c * hV.nm K s) (Finsupp.single a₀ 1) =
      -(∑ c : K, c) • Finsupp.single a₀ 1 := by
  simp only [minRep_xm_nm_of_wt_one hV h, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ]
  rw [card_smul_eq_zero' K, neg_zero, zero_sub, ← Finset.sum_smul, neg_smul]

theorem sum_eq_one_of_units_eq_one [Fintype K] (h : ∀ u : Kˣ, (u : K) = 1) : ∑ c : K, c = 1 := by
  rw [Finset.sum_eq_single (1 : K)]
  · intro c _ hc
    by_contra hc0
    exact hc (h (Units.mk0 c hc0))
  · intro h1
    exact absurd (Finset.mem_univ _) h1

end Hecke

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
