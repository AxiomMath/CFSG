module

public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.CGT.T75N.L29Rad
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open CFSG.Open.StatedAPI Matrix

section

variable {m : ℕ} {K : Type} [Field K]

private lemma independent_pair_of_notMem_span {b s : Fin m → K} (hb : b ≠ 0)
    (hs : s ∉ Submodule.span K {b}) :
    ∀ a d : K, a • s + d • b = 0 → a = 0 ∧ d = 0 := by
  intro a d h
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul, zero_add] at h
    exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hb⟩
  · exfalso
    apply hs
    have hs_eq : s = -(a⁻¹ * d) • b := by
      have h' : a • s = -(d • b) := eq_neg_of_add_eq_zero_left h
      calc s = a⁻¹ • (a • s) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = -(a⁻¹ * d) • b := by rw [h', smul_neg, smul_smul, neg_smul]
    rw [hs_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton b))

private lemma mem_span_pair_of_not_forall {b s w : Fin m → K}
    (hsb : ∀ a d : K, a • s + d • b = 0 → a = 0 ∧ d = 0)
    (h : ¬ ∀ a c d : K, a • s + c • w + d • b = 0 → a = 0 ∧ c = 0) :
    w ∈ Submodule.span K ({s, b} : Set (Fin m → K)) := by
  push Not at h
  obtain ⟨a, c, d, hrel, ha_or_c⟩ := h
  have hc : c ≠ 0 := by
    rintro rfl
    have ha : a = 0 := (hsb a d (by simpa using hrel)).1
    exact ha_or_c ha rfl
  have hmem : c • w ∈ Submodule.span K ({s, b} : Set (Fin m → K)) := by
    have hcw : c • w = -(a • s + d • b) := by
      rw [eq_neg_iff_add_eq_zero]
      calc c • w + (a • s + d • b) = a • s + c • w + d • b := by abel
        _ = 0 := hrel
    rw [hcw]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert s {b})))
      (Submodule.smul_mem _ d (Submodule.subset_span
        (Set.mem_insert_iff.mpr (Or.inr rfl)))))
  have := Submodule.smul_mem (Submodule.span K ({s, b} : Set (Fin m → K))) c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

private lemma exists_notMem_span_pair {b s : Fin m → K} (hm : 3 ≤ m)
    (hsb : ∀ a d : K, a • s + d • b = 0 → a = 0 ∧ d = 0) :
    ∃ u : Fin m → K, u ∉ Submodule.span K ({s, b} : Set (Fin m → K)) := by
  have hli : LinearIndependent K ![s, b] := LinearIndependent.pair_iff.mpr hsb
  have hspan : Module.finrank K (Submodule.span K ({s, b} : Set (Fin m → K))) = 2 := by
    have h := finrank_span_eq_card hli
    have hrange : Set.range ![s, b] = ({s, b} : Set (Fin m → K)) := by
      ext x
      simp [or_comm]
    rw [hrange] at h
    simpa using h
  have hproper : Submodule.span K ({s, b} : Set (Fin m → K)) ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank K (Submodule.span K ({s, b} : Set (Fin m → K))) = m := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    omega
  by_contra h
  push Not at h
  exact hproper (Submodule.eq_top_iff'.mpr h)

private lemma independent_of_notMem_span_pair {x y z : Fin m → K}
    (hxz : ∀ a d : K, a • x + d • z = 0 → a = 0 ∧ d = 0)
    (hy : y ∉ Submodule.span K ({x, z} : Set (Fin m → K))) :
    ∀ a c d : K, a • x + c • y + d • z = 0 → a = 0 ∧ c = 0 := by
  intro a c d hrel
  have hc : c = 0 := by
    by_contra hc
    apply hy
    have hmem : c • y ∈ Submodule.span K ({x, z} : Set (Fin m → K)) := by
      have hcy : c • y = -(a • x + d • z) := by
        rw [eq_neg_iff_add_eq_zero]
        calc c • y + (a • x + d • z) = a • x + c • y + d • z := by abel
          _ = 0 := hrel
      rw [hcy]
      exact Submodule.neg_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert x {z})))
        (Submodule.smul_mem _ d (Submodule.subset_span
          (Set.mem_insert_iff.mpr (Or.inr rfl)))))
    have := Submodule.smul_mem (Submodule.span K ({x, z} : Set (Fin m → K))) c⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  subst hc
  simp only [zero_smul, zero_add, add_zero] at hrel
  exact ⟨(hxz a d hrel).1, rfl⟩

private lemma exists_statedSL_mulVec_eq_of_independent_fixing
    {b s w : Fin m → K}
    (hind : ∀ a c d : K, a • s + c • w + d • b = 0 → a = 0 ∧ c = 0) :
    ∃ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ b = b ∧
      (g : Matrix (Fin m) (Fin m) K) *ᵥ s = w := by
  classical
  set p : Submodule K (Fin m → K) := Submodule.span K {b} with hp
  set q : (Fin m → K) →ₗ[K] (Fin m → K) ⧸ p := p.mkQ with hq
  have hq_ind : LinearIndependent K ![q s, q w] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    have h0 : q (a • s + c • w) = 0 := by
      rw [map_add, map_smul, map_smul]
      exact hac
    have hmem : a • s + c • w ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      exact h0
    rw [hp, Submodule.mem_span_singleton] at hmem
    obtain ⟨d, hd⟩ := hmem
    have hrel : a • s + c • w + (-d) • b = 0 := by
      rw [← hd]
      simp
    exact hind a c (-d) hrel
  obtain ⟨f₀, hf₀⟩ := Module.exists_dual_forall_apply_eq_one (K := K)
    (v := ![q s, q w]) (s := Set.univ) hq_ind.linearIndepOn_univ
  set f : Module.Dual K (Fin m → K) := f₀.comp q with hf
  have hfb : f b = 0 := by
    have hqb : q b = 0 := by
      rw [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_singleton b)
    rw [hf, LinearMap.comp_apply, hqb, map_zero]
  have hfs : f s = 1 := by
    have := hf₀ 0 (Set.mem_univ _)
    simpa [hf] using this
  have hfw : f w = 1 := by
    have := hf₀ 1 (Set.mem_univ _)
    simpa [hf] using this
  have hfv : f (w - s) = 0 := by rw [map_sub, hfw, hfs, sub_self]
  obtain ⟨g, hg, hgz⟩ := exists_statedSL_mulVec_eq_transvection f hfv
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hgz, hfb, zero_smul, add_zero]
  · rw [hgz, hfs, one_smul]
    abel

private lemma notMem_span_pair_of_mem_span_pair {b s w u : Fin m → K}
    (hwspan : w ∈ Submodule.span K ({s, b} : Set (Fin m → K)))
    (hu : u ∉ Submodule.span K ({s, b} : Set (Fin m → K)))
    (hw : w ∉ Submodule.span K {b}) :
    w ∉ Submodule.span K ({u, b} : Set (Fin m → K)) := by
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨α, β, hαβ⟩ := hmem
  have hα : α = 0 := by
    by_contra hα
    apply hu
    have hmem' : α • u ∈ Submodule.span K ({s, b} : Set (Fin m → K)) := by
      have hαu : α • u = w - β • b := by rw [← hαβ]; abel
      rw [hαu]
      exact Submodule.sub_mem _ hwspan (Submodule.smul_mem _ β
        (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))))
    have := Submodule.smul_mem (Submodule.span K ({s, b} : Set (Fin m → K))) α⁻¹ hmem'
    rwa [smul_smul, inv_mul_cancel₀ hα, one_smul] at this
  subst hα
  apply hw
  rw [← hαβ]
  simpa using Submodule.smul_mem (Submodule.span K {b}) β
    (Submodule.subset_span (Set.mem_singleton b))

private lemma exists_statedSL_mulVec_eq_of_notMem_span_fixing {b s w : Fin m → K}
    (hm : 3 ≤ m) (hb : b ≠ 0) (hs : s ∉ Submodule.span K {b})
    (hw : w ∉ Submodule.span K {b}) :
    ∃ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ b = b ∧
      (g : Matrix (Fin m) (Fin m) K) *ᵥ s = w := by
  have hsb := independent_pair_of_notMem_span hb hs
  by_cases htriple : ∀ a c d : K, a • s + c • w + d • b = 0 → a = 0 ∧ c = 0
  · exact exists_statedSL_mulVec_eq_of_independent_fixing htriple
  · have hwspan := mem_span_pair_of_not_forall hsb htriple
    obtain ⟨u, hu⟩ := exists_notMem_span_pair hm hsb
    have hs_u_b := independent_of_notMem_span_pair hsb hu
    have hu_b_not : u ∉ Submodule.span K {b} := by
      intro hmem
      apply hu
      refine Submodule.span_mono ?_ hmem
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_insert_iff.mpr (Or.inr rfl)
    have hu_b := independent_pair_of_notMem_span hb hu_b_not
    have huw := notMem_span_pair_of_mem_span_pair hwspan hu hw
    have hu_w_b := independent_of_notMem_span_pair hu_b huw
    obtain ⟨g₁, hg₁, hb₁, hs₁⟩ :=
      exists_statedSL_mulVec_eq_of_independent_fixing hs_u_b
    obtain ⟨g₂, hg₂, hb₂, hu₂⟩ :=
      exists_statedSL_mulVec_eq_of_independent_fixing hu_w_b
    refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb₁, hb₂]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hs₁, hu₂]

private lemma exists_single_notMem_span {b : Fin m → K} (hm : 3 ≤ m) (hb : b ≠ 0) :
    ∃ j : Fin m, (Pi.single j (1 : K)) ∉ Submodule.span K {b} := by
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := Function.ne_iff.mp hb
  obtain ⟨j, hji⟩ : ∃ j : Fin m, j ≠ i := by
    have hcard : 1 < Fintype.card (Fin m) := by
      simp only [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard i
  refine ⟨j, ?_⟩
  intro hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hci : c * b i = 0 := by
    have := congrFun hc i
    simpa [Pi.single_apply, hji] using this
  have hc0 : c = 0 := (mul_eq_zero.mp hci).resolve_right hi
  have he0 : (Pi.single j (1 : K) : Fin m → K) = 0 := by rw [← hc, hc0, zero_smul]
  have := congrFun he0 j
  simp at this

private lemma eq_top_of_exists_notMem_span {b : Fin m → K} (hm : 3 ≤ m) (hb : b ≠ 0)
    (S : AddSubgroup (Fin m → K))
    (hS : ∀ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ b = b →
      ∀ s ∈ S, (g : Matrix (Fin m) (Fin m) K) *ᵥ s ∈ S)
    {s : Fin m → K} (hsS : s ∈ S) (hs : s ∉ Submodule.span K {b}) : S = ⊤ := by
  classical
  have hSall : ∀ w, w ∉ Submodule.span K {b} → w ∈ S := by
    intro w hw
    obtain ⟨g, hg, hgb, hgs⟩ :=
      exists_statedSL_mulVec_eq_of_notMem_span_fixing hm hb hs hw
    have := hS g hg hgb s hsS
    rwa [hgs] at this
  rw [AddSubgroup.eq_top_iff']
  intro x
  by_cases hx : x ∈ Submodule.span K {b}
  · obtain ⟨j, he⟩ := exists_single_notMem_span hm hb
    have hxe : x + Pi.single j (1 : K) ∉ Submodule.span K {b} := by
      intro hmem
      apply he
      have : Pi.single j (1 : K) = (x + Pi.single j (1 : K)) - x := by abel
      rw [this]
      exact Submodule.sub_mem _ hmem hx
    have h1 : x + Pi.single j (1 : K) ∈ S := hSall _ hxe
    have h2 : Pi.single j (1 : K) ∈ S := hSall _ he
    have : x = (x + Pi.single j (1 : K)) - Pi.single j (1 : K) := by abel
    rw [this]
    exact AddSubgroup.sub_mem S h1 h2
  · exact hSall x hx

end

theorem forall_eq_smul_or_eq_top_of_fixer_invariant {K : Type} [Field K] {m : ℕ} (hm : 3 ≤ m)
    {b : Fin m → K} (hb : b ≠ 0) (S : AddSubgroup (Fin m → K))
    (hS : ∀ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ b = b →
      ∀ s ∈ S, (g : Matrix (Fin m) (Fin m) K) *ᵥ s ∈ S) :
    (∀ s ∈ S, ∃ c : K, s = c • b) ∨ S = ⊤ := by
  classical
  by_cases hline : ∀ s ∈ S, ∃ c : K, s = c • b
  · exact Or.inl hline
  · push Not at hline
    obtain ⟨s, hsS, hs⟩ := hline
    refine Or.inr (eq_top_of_exists_notMem_span hm hb S hS hsS ?_)
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact hs c hc.symm

section

variable {m : ℕ} {K : Type} [Field K]

private lemma card_le_card_of_forall_eq_smul [Finite K] {b : Fin m → K} (hb : b ≠ 0)
    {S : AddSubgroup (Fin m → K)} (hline : ∀ s ∈ S, ∃ c : K, s = c • b) :
    Nat.card S ≤ Nat.card K := by
  classical
  let f : S → K := fun s => Classical.choose (hline s.1 s.2)
  have hf : Function.Injective f := by
    intro s t hst
    have hs := Classical.choose_spec (hline s.1 s.2)
    have ht := Classical.choose_spec (hline t.1 t.2)
    apply Subtype.ext
    calc (s : Fin m → K) = f s • b := hs
      _ = f t • b := by rw [hst]
      _ = (t : Fin m → K) := ht.symm
  exact Nat.card_le_card_of_injective f hf

private lemma card_eq_pow_of_eq_top {S : AddSubgroup (Fin m → K)} (hS : S = ⊤) :
    Nat.card S = Nat.card K ^ m := by
  rw [hS, Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_fin]

end

theorem card_ne_pow_of_fixer_invariant {K : Type} [Field K] [Finite K] {m k : ℕ} (hm : 3 ≤ m)
    (hk : 2 ≤ k) (hkm : k < m) {b : Fin m → K} (hb : b ≠ 0) (S : AddSubgroup (Fin m → K))
    (hS : ∀ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ b = b →
      ∀ s ∈ S, (g : Matrix (Fin m) (Fin m) K) *ᵥ s ∈ S) :
    Nat.card S ≠ Nat.card K ^ k := by
  rcases forall_eq_smul_or_eq_top_of_fixer_invariant hm hb S hS with hline | htop
  · intro heq
    have h1 := card_le_card_of_forall_eq_smul hb hline
    have h2 : Nat.card K < Nat.card K ^ k := by
      refine (pow_one (Nat.card K)).symm.trans_lt ?_
      exact pow_lt_pow_right₀ Finite.one_lt_card (by omega)
    omega
  · intro heq
    have h1 := card_eq_pow_of_eq_top htop
    have h2 : Nat.card K ^ k < Nat.card K ^ m :=
      pow_lt_pow_right₀ Finite.one_lt_card hkm
    omega

section

variable {m : ℕ} {K : Type} [Field K]

private lemma sub_one_mul_self_eq_zero_of_matrix_involution [CharP K 2]
    {t : Matrix (Fin m) (Fin m) K} (ht : t * t = 1) : (t - 1) * (t - 1) = 0 := by
  have hadd : ∀ M : Matrix (Fin m) (Fin m) K, M + M = 0 := by
    intro M
    ext a b
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h : (t - 1) * (t - 1) = t * t + 1 - (t + t) := by noncomm_ring
  rw [h, ht, hadd t, sub_zero, hadd 1]

private lemma rank_sub_one_le_one_of_matrix_involution [CharP K 2] (hm : m ≤ 3)
    {t : Matrix (Fin m) (Fin m) K} (ht : t * t = 1) : (t - 1).rank ≤ 1 := by
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero
    (A := t - 1) (B := t - 1) (sub_one_mul_self_eq_zero_of_matrix_involution ht)
  simp only [Fintype.card_fin] at h
  omega

private lemma exists_eq_one_add_vecMulVec_of_ne_zero [CharP K 2] (hm : m ≤ 3)
    {i : GL (Fin m) K} (hi : i * i = 1) (hN : (i : Matrix (Fin m) (Fin m) K) - 1 ≠ 0) :
    ∃ u μ : Fin m → K, μ ⬝ᵥ u = 0 ∧
      (i : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u μ := by
  have hi' : (i : Matrix (Fin m) (Fin m) K) * (i : Matrix (Fin m) (Fin m) K) = 1 := by
    simpa using congrArg (fun u : GL (Fin m) K => (u : Matrix (Fin m) (Fin m) K)) hi
  have hN2 : ((i : Matrix (Fin m) (Fin m) K) - 1) * ((i : Matrix (Fin m) (Fin m) K) - 1) =
      0 := sub_one_mul_self_eq_zero_of_matrix_involution hi'
  have hrank : ((i : Matrix (Fin m) (Fin m) K) - 1).rank ≤ 1 :=
    rank_sub_one_le_one_of_matrix_involution hm hi'
  obtain ⟨u, μ, hNvec⟩ :=
    CFSG.Quasithin.H13.L829NK.exists_vecMulVec_of_rank_le_one
      ((i : Matrix (Fin m) (Fin m) K) - 1) hrank
  have hvec0 : Matrix.vecMulVec u μ ≠ 0 := by
    rw [← hNvec]
    exact hN
  have hu : u ≠ 0 := fun hu0 => hvec0 (by rw [hu0]; simp)
  have hμ : μ ≠ 0 := fun hμ0 => hvec0 (by rw [hμ0]; simp)
  have hdot : μ ⬝ᵥ u = 0 := by
    have hzero : Matrix.vecMulVec u ((μ ⬝ᵥ u) • μ) = 0 := by
      have h := hN2
      rw [hNvec, Matrix.vecMulVec_mul_vecMulVec] at h
      exact h
    rcases Matrix.vecMulVec_eq_zero.mp hzero with hu0 | hμ0
    · exact absurd hu0 hu
    · rcases smul_eq_zero.mp hμ0 with h0 | h0
      · exact h0
      · exact absurd h0 hμ
  refine ⟨u, μ, hdot, ?_⟩
  rw [← hNvec]
  abel

end

theorem exists_eq_one_add_vecMulVec_of_mul_self_eq_one {K : Type} [Field K] [CharP K 2]
    {m : ℕ} (hm : m ≤ 3) {i : GL (Fin m) K} (hi : i * i = 1) :
    ∃ u μ : Fin m → K, μ ⬝ᵥ u = 0 ∧
      (i : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u μ := by
  by_cases hN0 : (i : Matrix (Fin m) (Fin m) K) - 1 = 0
  · have hi1 : (i : Matrix (Fin m) (Fin m) K) = 1 := sub_eq_zero.mp hN0
    refine ⟨0, 0, by simp, ?_⟩
    rw [hi1]
    simp
  · exact exists_eq_one_add_vecMulVec_of_ne_zero hm hi hN0

theorem exists_conj_eq_one_add_vecMulVec {K : Type} [Field K] [CharP K 2] {m : ℕ}
    (hm2 : 2 ≤ m) (hm3 : m ≤ 3) {b : Fin m → K} (hb : b ≠ 0) {i : GL (Fin m) K}
    (hi : i * i = 1) :
    ∃ g ∈ StatedSL m K, ∃ μ : Fin m → K, μ ⬝ᵥ b = 0 ∧
      ((g * i * g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec b μ := by
  obtain ⟨u, μ₀, hμ₀u, hivec⟩ :=
    exists_eq_one_add_vecMulVec_of_mul_self_eq_one (K := K) (m := m) hm3 hi
  by_cases hu : u = 0
  · have hi1 : (i : Matrix (Fin m) (Fin m) K) = 1 := by
      rw [hivec, hu]
      simp
    refine ⟨1, one_mem _, 0, by simp, ?_⟩
    simp [hi1]
  · obtain ⟨g, hg, hgu⟩ := exists_statedSL_mulVec_eq (K := K) (m := m) hm2 hu hb
    refine ⟨g, hg, μ₀ ᵥ* ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K), ?_, ?_⟩
    · rw [← hgu, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hμ₀u
    · rw [Units.val_mul, Units.val_mul, hivec,
      CFSG.CGT.T75N.conj_one_add_vecMulVec (g : Matrix (Fin m) (Fin m) K)
        ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) (Units.mul_inv g) u μ₀, hgu]

end CFSG.ClassicalGroups.SpecialLinear
