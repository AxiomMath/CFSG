module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSubspaceCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule

universe u

variable {p f : ℕ} {K : Type*} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

section Flags

variable {σ : K →+* K}

@[expose] def IsSelfDualFlag (B : V →ₛₗ[σ] V →ₗ[K] K) (n : ℕ) (F : ℕ → Submodule K V) :
    Prop :=
  (∀ i ≤ n, finrank K (F i) = i) ∧ (∀ i < n, F i ≤ F (i + 1)) ∧
    ∀ i ≤ n, (F i).orthogonalBilin B = F (n - i)

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {n : ℕ} {F : ℕ → Submodule K V}

theorem IsSelfDualFlag.le (hF : IsSelfDualFlag B n F) {i i' : ℕ} (hii' : i ≤ i')
    (hi' : i' ≤ n) : F i ≤ F i' := by
  induction i', hii' using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hii' ih => exact (ih (by omega)).trans (hF.2.1 i' (by omega))

theorem IsSelfDualFlag.zero [FiniteDimensional K V] (hF : IsSelfDualFlag B n F) : F 0 = ⊥ :=
  Submodule.finrank_eq_zero.mp (hF.1 0 (Nat.zero_le _))

theorem IsSelfDualFlag.top [FiniteDimensional K V] (hF : IsSelfDualFlag B n F)
    (hn : finrank K V = n) : F n = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [hF.1 n le_rfl, hn])

theorem IsSelfDualFlag.apply_eq_zero (hF : IsSelfDualFlag B n F) {i j : ℕ} (hij : i + j ≤ n)
    {x y : V} (hx : x ∈ F j) (hy : y ∈ F i) : B x y = 0 := by
  have hy' : y ∈ (F j).orthogonalBilin B := by
    rw [hF.2.2 j (by omega)]
    exact hF.le (show i ≤ n - j by omega) (Nat.sub_le n j) hy
  exact (mem_orthogonalBilin.mp hy') x hx

end Flags

theorem exists_dedupFlag {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {N : ℕ} (E : ℕ → Submodule K U) (hmono : ∀ i < N, E i ≤ E (i + 1))
    (h0 : finrank K (E 0) = 0)
    (hstep : ∀ i < N, finrank K (E (i + 1)) ≤ finrank K (E i) + 1) :
    ∃ E' : ℕ → Submodule K U, (∀ m ≤ finrank K (E N), finrank K (E' m) = m) ∧
      (∀ m < finrank K (E N), E' m ≤ E' (m + 1)) ∧
      (∀ i ≤ N, E i = E' (finrank K (E i))) ∧ ∀ m ≤ finrank K (E N), ∃ i ≤ N, E' m = E i := by
  classical
  have hle : ∀ i i', i ≤ i' → i' ≤ N → E i ≤ E i' := by
    intro i i' hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact le_rfl
    | succ i' hii' ih => exact (ih (by omega)).trans (hmono i' (by omega))
  have hex : ∀ m, ∃ i, i ≤ N ∧ min m (finrank K (E N)) ≤ finrank K (E i) :=
    fun m => ⟨N, le_rfl, min_le_right _ _⟩
  have hcN : ∀ m, Nat.find (hex m) ≤ N := fun m => (Nat.find_spec (hex m)).1
  have hcge : ∀ m, min m (finrank K (E N)) ≤ finrank K (E (Nat.find (hex m))) :=
    fun m => (Nat.find_spec (hex m)).2
  have hcdim : ∀ m, finrank K (E (Nat.find (hex m))) = min m (finrank K (E N)) := by
    intro m
    rcases Nat.eq_zero_or_pos (Nat.find (hex m)) with hc0 | hpos
    · have := hcge m
      rw [hc0, h0] at this ⊢
      omega
    · obtain ⟨i, hi⟩ : ∃ i, Nat.find (hex m) = i + 1 := ⟨Nat.find (hex m) - 1, by omega⟩
      have hiN : i < N := by have := hcN m; omega
      have h1 : ¬(i ≤ N ∧ min m (finrank K (E N)) ≤ finrank K (E i)) :=
        Nat.find_min (hex m) (by omega)
      push Not at h1
      have h2 := hstep i hiN
      rw [← hi] at h2
      have := hcge m
      have := h1 hiN.le
      omega
  refine ⟨fun m => E (Nat.find (hex m)), fun m hm => (hcdim m).trans (min_eq_left hm),
    fun m _ => hle _ _ (Nat.find_mono fun i hi =>
      ⟨hi.1, le_trans (min_le_min (Nat.le_succ m) le_rfl) hi.2⟩) (hcN _),
    fun i hi => ?_, fun m _ => ⟨_, hcN m, rfl⟩⟩
  have hm : finrank K (E i) ≤ finrank K (E N) := Submodule.finrank_mono (hle i N hi le_rfl)
  have hci : Nat.find (hex (finrank K (E i))) ≤ i :=
    Nat.find_min' _ ⟨hi, min_le_left _ _⟩
  exact (Submodule.eq_of_le_of_finrank_eq (hle _ _ hci hi) (by rw [hcdim, min_eq_left hm])).symm

@[expose] def dedupIdx (a b i : ℕ) : ℕ :=
  i - (if a ≤ i then 1 else 0) - (if b ≤ i then 1 else 0)

section Split

variable (h : UnitaryFieldData p f K) [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem pairProj_mem (hB : B.IsSymm) {v w : V} (hvv : B v v = 0) (hvw : B v w = 1)
    (hww : B w w = 0) (x : V) : x - B w x • v - B v x • w ∈ pairOrth B v w := by
  have hwv : B w v = 1 := by rw [← hB.eq v w, hvw, map_one]
  rw [mem_orthogonalBilin]
  intro y hy
  obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hy
  simp only [map_sub, map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hvv, hvw, hwv, hww]
  ring

omit [FiniteDimensional K V] in
theorem pairProj_eq_self {v w x : V} (hx : x ∈ pairOrth B v w) :
    x - B w x • v - B v x • w = x := by
  have h1 : B v x = 0 := (mem_orthogonalBilin.mp hx) v (subset_span (by simp))
  have h2 : B w x = 0 := (mem_orthogonalBilin.mp hx) w (subset_span (by simp))
  rw [h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

theorem selfDualFlag_split (hB : B.IsSymm) (hBl : B.SeparatingLeft) {n : ℕ}
    {G : ℕ → Submodule K V} (hG : IsSelfDualFlag B n G) {v w : V} {j k : ℕ} (hj1 : 1 ≤ j)
    (hk1 : 1 ≤ k) (hjk : j + k = n + 1) (hvj : v ∈ G j) (hwk : w ∈ G k)
    (hv0 : v ≠ 0) (hvv : B v v = 0) (hvw : B v w = 1) (hww : B w w = 0) :
    (∀ i ≤ n, ∀ x ∈ G i, x - B w x • v - B v x • w ∈ G i) ∧
    (∀ i ≤ n, G i = (G i ⊓ span K {v, w}) ⊔ (G i ⊓ pairOrth B v w)) ∧
    (∀ i ≤ n, G i ⊓ span K {v, w} =
      (if j ≤ i then K ∙ v else ⊥) ⊔ (if k ≤ i then K ∙ w else ⊥)) ∧
    ∃ G' : ℕ → Submodule K (pairOrth B v w),
      IsSelfDualFlag (B.domRestrict₁₂ (pairOrth B v w) (pairOrth B v w)) (n - 2) G' ∧
      ∀ i ≤ n, (G i).comap (pairOrth B v w).subtype = G' (dedupIdx j k i) := by
  have hwv : B w v = 1 := by rw [← hB.eq v w, hvw, map_one]
  have hw0 : w ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvw
    exact zero_ne_one hvw
  obtain ⟨hH2, -, hcompl, -, -⟩ := (hermitian_hyperbolic_splitting h hB hBl hv0 hvv).2 w hvw hww
  have hvH : v ∈ span K {v, w} := subset_span (by simp)
  have hwH : w ∈ span K {v, w} := subset_span (by simp)
  have hcv : ∀ i, i < k → ∀ x ∈ G i, B v x = 0 := fun i _ x hx =>
    hG.apply_eq_zero (show i + j ≤ n by omega) hvj hx
  have hcw : ∀ i, i < j → ∀ x ∈ G i, B w x = 0 := fun i _ x hx =>
    hG.apply_eq_zero (show i + k ≤ n by omega) hwk hx
  have hmv : ∀ i ≤ n, ∀ x ∈ G i, B w x • v ∈ G i := by
    intro i hi x hx
    by_cases hji : j ≤ i
    · exact smul_mem _ _ (hG.le hji hi hvj)
    · rw [hcw i (by omega) x hx, zero_smul]
      exact zero_mem _
  have hmw : ∀ i ≤ n, ∀ x ∈ G i, B v x • w ∈ G i := by
    intro i hi x hx
    by_cases hki : k ≤ i
    · exact smul_mem _ _ (hG.le hki hi hwk)
    · rw [hcv i (by omega) x hx, zero_smul]
      exact zero_mem _
  have hQG : ∀ i ≤ n, ∀ x ∈ G i, x - B w x • v - B v x • w ∈ G i := fun i hi x hx =>
    sub_mem (sub_mem hx (hmv i hi x hx)) (hmw i hi x hx)
  have hsplit : ∀ i ≤ n, G i = (G i ⊓ span K {v, w}) ⊔ (G i ⊓ pairOrth B v w) := by
    intro i hi
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
    have hx' : x = (B w x • v + B v x • w) + (x - B w x • v - B v x • w) := by abel
    rw [hx']
    exact add_mem_sup ⟨add_mem (hmv i hi x hx) (hmw i hi x hx),
      add_mem (smul_mem _ _ hvH) (smul_mem _ _ hwH)⟩
      ⟨hQG i hi x hx, pairProj_mem h hB hvv hvw hww x⟩
  have hHint : ∀ i ≤ n, G i ⊓ span K {v, w} =
      (if j ≤ i then K ∙ v else ⊥) ⊔ (if k ≤ i then K ∙ w else ⊥) := by
    intro i hi
    refine le_antisymm (fun y hy => ?_) (sup_le ?_ ?_)
    · obtain ⟨hyG, hyH⟩ := hy
      obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hyH
      refine mem_sup.mpr ⟨a • v, ?_, b • w, ?_, rfl⟩
      · split_ifs with hji
        · exact smul_mem _ _ (mem_span_singleton_self v)
        · have ha := hcw i (by omega) _ hyG
          simp only [map_add, map_smul, smul_eq_mul, hwv, hww, mul_one, mul_zero,
            add_zero] at ha
          rw [ha, zero_smul]
          exact zero_mem _
      · split_ifs with hki
        · exact smul_mem _ _ (mem_span_singleton_self w)
        · have hb := hcv i (by omega) _ hyG
          simp only [map_add, map_smul, smul_eq_mul, hvv, hvw, mul_one, mul_zero,
            zero_add] at hb
          rw [hb, zero_smul]
          exact zero_mem _
    · split_ifs with hji
      · exact (span_singleton_le_iff_mem _ _).mpr ⟨hG.le hji hi hvj, hvH⟩
      · exact bot_le
    · split_ifs with hki
      · exact (span_singleton_le_iff_mem _ _).mpr ⟨hG.le hki hi hwk, hwH⟩
      · exact bot_le
  have hdimP : ∀ i ≤ n, finrank K ↥(G i ⊓ pairOrth B v w) = dedupIdx j k i := by
    intro i hi
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (G i ⊓ span K {v, w})
      (G i ⊓ pairOrth B v w)
    have h0 : G i ⊓ span K {v, w} ⊓ (G i ⊓ pairOrth B v w) = ⊥ :=
      eq_bot_iff.mpr fun x hx => by
        rw [← hcompl.inf_eq_bot]
        exact ⟨hx.1.2, hx.2.2⟩
    rw [← hsplit i hi, hG.1 i hi, h0, finrank_bot, add_zero, hHint i hi] at h1
    have e : ∀ X : Submodule K V,
        (if j ≤ i then K ∙ v else ⊥) ⊔ (if k ≤ i then K ∙ w else ⊥) = X →
        finrank K ↥X + finrank K ↥(G i ⊓ pairOrth B v w) = i := fun X hX => by
      rw [← hX]
      exact h1.symm
    unfold dedupIdx
    by_cases hji : j ≤ i <;> by_cases hki : k ≤ i <;> simp only [hji, hki, ↓reduceIte]
    · have := e (span K {v, w}) (by
        simp only [hji, hki, ↓reduceIte]
        exact (span_insert v {w}).symm)
      rw [hH2] at this
      omega
    · have := e (K ∙ v) (by simp only [hji, hki, ↓reduceIte, sup_bot_eq])
      rw [finrank_span_singleton hv0] at this
      omega
    · have := e (K ∙ w) (by simp only [hji, hki, ↓reduceIte, bot_sup_eq])
      rw [finrank_span_singleton hw0] at this
      omega
    · have := e ⊥ (by simp only [hji, hki, ↓reduceIte, sup_bot_eq])
      rw [finrank_bot] at this
      omega
  have hdimE : ∀ i ≤ n,
      finrank K ↥((G i).comap (pairOrth B v w).subtype) = dedupIdx j k i := fun i hi => by
    rw [finrank_comap_subtype, hdimP i hi]
  have hperpE : ∀ i ≤ n, ((G i).comap (pairOrth B v w).subtype).orthogonalBilin
      (B.domRestrict₁₂ (pairOrth B v w) (pairOrth B v w)) =
      (G (n - i)).comap (pairOrth B v w).subtype := by
    intro i hi
    ext y
    rw [mem_orthogonalBilin, mem_comap, subtype_apply, ← hG.2.2 i hi, mem_orthogonalBilin]
    constructor
    · intro hy x hx
      rw [hsplit i hi] at hx
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := mem_sup.mp hx
      have h1 : B x₁ y = 0 := (mem_orthogonalBilin.mp y.2) x₁ hx₁.2
      have h2 : B x₂ y = 0 := hy ⟨x₂, hx₂.2⟩ hx₂.1
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    · intro hy x hx
      exact hy x hx
  obtain ⟨G', hdim', hmono', hEq, hsurj⟩ := exists_dedupFlag (N := n)
    (fun i => (G i).comap (pairOrth B v w).subtype)
    (fun i hi => comap_mono (hG.2.1 i hi))
    (by
      change finrank K ↥((G 0).comap (pairOrth B v w).subtype) = 0
      rw [hdimE 0 (Nat.zero_le _)]
      unfold dedupIdx
      split_ifs <;> omega)
    (fun i hi => by
      change finrank K ↥((G (i + 1)).comap (pairOrth B v w).subtype) ≤
        finrank K ↥((G i).comap (pairOrth B v w).subtype) + 1
      rw [hdimE (i + 1) hi, hdimE i hi.le]
      unfold dedupIdx
      split_ifs <;> omega)
  have hEn : finrank K ↥((G n).comap (pairOrth B v w).subtype) = n - 2 := by
    rw [hdimE n le_rfl]
    unfold dedupIdx
    split_ifs <;> omega
  have hdim'' : ∀ m ≤ n - 2, finrank K (G' m) = m := fun m hm => hdim' m (by
    change m ≤ finrank K ↥((G n).comap (pairOrth B v w).subtype)
    rw [hEn]
    exact hm)
  have hEq' : ∀ i ≤ n, (G i).comap (pairOrth B v w).subtype = G' (dedupIdx j k i) :=
    fun i hi => by
      rw [← hdimE i hi]
      exact hEq i hi
  refine ⟨hQG, hsplit, hHint, G', ⟨hdim'', fun m hm => hmono' m (by
    change m < finrank K ↥((G n).comap (pairOrth B v w).subtype)
    rw [hEn]
    exact hm), fun m hm => ?_⟩, hEq'⟩
  obtain ⟨i, hi, hG'i⟩ := hsurj m (by
    change m ≤ finrank K ↥((G n).comap (pairOrth B v w).subtype)
    rw [hEn]
    exact hm)
  have hG'i' : G' m = (G i).comap (pairOrth B v w).subtype := hG'i
  have hmi : dedupIdx j k i = m := by
    rw [← hdimE i hi, ← hG'i', hdim'' m hm]
  rw [hG'i', hperpE i hi, hEq' (n - i) (Nat.sub_le n i)]
  congr 1
  rw [← hmi]
  unfold dedupIdx
  split_ifs <;> omega

end Split

theorem unitary_two_selfdual_flag_splitting (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {n : ℕ}
    (hn : finrank K V = n) (hn2 : 2 ≤ n) {F G : ℕ → Submodule K V}
    (hF : IsSelfDualFlag B n F) (hG : IsSelfDualFlag B n G) {v : V} (hv : v ∈ F 1)
    (hv0 : v ≠ 0) {j : ℕ} (hj : v ∈ G j) (hjmin : ∀ i < j, v ∉ G i) :
    j ≠ n + 1 - j ∧ (∃ w ∈ G (n + 1 - j), B v w = 1 ∧ B w w = 0) ∧
    ∀ w ∈ G (n + 1 - j), B v w = 1 → B w w = 0 →
      (∀ x, x - B w x • v - B v x • w ∈ pairOrth B v w) ∧
      (∀ x ∈ pairOrth B v w, x - B w x • v - B v x • w = x) ∧
      (∀ i ≤ n, ∀ x ∈ F i, x - B w x • v - B v x • w ∈ F i) ∧
      (∀ i ≤ n, ∀ x ∈ G i, x - B w x • v - B v x • w ∈ G i) ∧
      (∀ i ≤ n, F i = (F i ⊓ span K {v, w}) ⊔ (F i ⊓ pairOrth B v w)) ∧
      (∀ i ≤ n, G i = (G i ⊓ span K {v, w}) ⊔ (G i ⊓ pairOrth B v w)) ∧
      (∀ i ≤ n, F i ⊓ span K {v, w} =
        (if 1 ≤ i then K ∙ v else ⊥) ⊔ (if n ≤ i then K ∙ w else ⊥)) ∧
      (∀ i ≤ n, G i ⊓ span K {v, w} =
        (if j ≤ i then K ∙ v else ⊥) ⊔ (if n + 1 - j ≤ i then K ∙ w else ⊥)) ∧
      (B.domRestrict₁₂ (pairOrth B v w) (pairOrth B v w)).SeparatingLeft ∧
      finrank K (pairOrth B v w) = n - 2 ∧
      ∃ F' G' : ℕ → Submodule K (pairOrth B v w),
        IsSelfDualFlag (B.domRestrict₁₂ (pairOrth B v w) (pairOrth B v w)) (n - 2) F' ∧
        IsSelfDualFlag (B.domRestrict₁₂ (pairOrth B v w) (pairOrth B v w)) (n - 2) G' ∧
        (∀ i ≤ n, (F i).comap (pairOrth B v w).subtype = F' (dedupIdx 1 n i)) ∧
        ∀ i ≤ n, (G i).comap (pairOrth B v w).subtype = G' (dedupIdx j (n + 1 - j) i) := by
  have hvv : B v v = 0 := hF.apply_eq_zero (show 1 + 1 ≤ n by omega) hv hv
  have hjn : j ≤ n := by
    by_contra hjn
    exact hjmin n (by omega) (by rw [hG.top hn]; exact mem_top)
  have hj1 : 1 ≤ j := by
    by_contra hj0
    obtain rfl : j = 0 := by omega
    rw [hG.zero, mem_bot] at hj
    exact hv0 hj
  have hvj' : v ∉ G (j - 1) := hjmin (j - 1) (by omega)
  have hGj : G (j - 1) ⊔ K ∙ v = G j := by
    have hle : G (j - 1) ⊔ K ∙ v ≤ G j :=
      sup_le (hG.le (by omega) hjn) ((span_singleton_le_iff_mem v _).mpr hj)
    have hlt : G (j - 1) < G (j - 1) ⊔ K ∙ v := lt_of_le_of_ne le_sup_left fun he =>
      hvj' (by rw [he]; exact mem_sup_right (mem_span_singleton_self v))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hG.1 (j - 1) (by omega)] at h1
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [hG.1 j hjn]; omega)
  have hjk' : j ≠ n + 1 - j := by
    intro hjk
    apply hvj'
    have hperp : (G j).orthogonalBilin B = G (j - 1) := by
      rw [hG.2.2 j hjn]
      congr 1
      omega
    rw [← hperp, mem_orthogonalBilin]
    intro y hy
    rw [← hGj] at hy
    obtain ⟨g, hg, c, hc, rfl⟩ := mem_sup.mp hy
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hc
    have hgv : B g v = 0 := hG.apply_eq_zero (show j + (j - 1) ≤ n by omega) hg hj
    simp [hgv, hvv]
  have hexw : ∃ w ∈ G (n + 1 - j), B v w = 1 ∧ B w w = 0 := by
    obtain ⟨w₀, hw₀, hvw₀⟩ : ∃ w₀ ∈ G (n + 1 - j), B v w₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hvj'
      have hperp : (G (n + 1 - j)).orthogonalBilin B = G (j - 1) := by
        rw [hG.2.2 (n + 1 - j) (by omega)]
        congr 1
        omega
      rw [← hperp, mem_orthogonalBilin]
      intro y hy
      rw [← hB.eq v y, hcon y hy, map_zero]
    have hw₁k : (B v w₀)⁻¹ • w₀ ∈ G (n + 1 - j) := smul_mem _ _ hw₀
    have hvw₁ : B v ((B v w₀)⁻¹ • w₀) = 1 := by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hvw₀]
    rcases lt_or_gt_of_ne hjk' with hlt | hgt
    ·
      have hvk : v ∈ G (n + 1 - j) := hG.le (by omega) (by omega) hj
      obtain ⟨w₁, hw₁k, hvw₁⟩ : ∃ w₁ ∈ G (n + 1 - j), B v w₁ = 1 := ⟨_, hw₁k, hvw₁⟩
      have hdF : h.bar (B w₁ w₁) = B w₁ w₁ := hB.eq w₁ w₁
      obtain ⟨c, hc⟩ := h.traceLin_surjective (-⟨B w₁ w₁, hdF⟩)
      have hc' : c + h.bar c = -B w₁ w₁ := by
        simpa [UnitaryFieldData.trace] using congrArg Subtype.val hc
      have hw₁v : B w₁ v = 1 := by rw [← hB.eq v w₁, hvw₁, map_one]
      refine ⟨w₁ + c • v, add_mem hw₁k (smul_mem _ _ hvk), ?_, ?_⟩
      · rw [map_add, hvw₁, map_smul, hvv, smul_zero, add_zero]
      · simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, hvv, hvw₁, hw₁v, mul_zero, add_zero, mul_one]
        linear_combination hc'
    ·
      exact ⟨_, hw₁k, hvw₁, hG.apply_eq_zero (by omega) hw₁k hw₁k⟩
  refine ⟨hjk', hexw, fun w hwk hvw hww => ?_⟩
  obtain ⟨-, -, -, hsep, hdim⟩ := (hermitian_hyperbolic_splitting h hB hBl hv0 hvv).2 w hvw hww
  have hwF : w ∈ F n := by
    rw [hF.top hn]
    exact mem_top
  obtain ⟨hQF, hsplitF, hHF, F', hF', hEF⟩ := selfDualFlag_split h hB hBl hF (j := 1) (k := n)
    le_rfl (by omega) (by omega) hv hwF hv0 hvv hvw hww
  obtain ⟨hQG, hsplitG, hHG, G', hG', hEG⟩ := selfDualFlag_split h hB hBl hG
    (k := n + 1 - j) hj1 (by omega) (by omega) hj hwk hv0 hvv hvw hww
  exact ⟨pairProj_mem h hB hvv hvw hww, fun x hx => pairProj_eq_self h hx, hQF, hQG, hsplitF,
    hsplitG, hHF, hHG, hsep, by rw [hdim, hn], F', G', hF', hG', hEF, hEG⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
