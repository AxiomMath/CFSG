module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteDiagonal

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

theorem CoreAt.unique {I : Type*} {i₀ i₁ i₂ i₃ i₄ : I} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ}
    (hδ₀ : δ₀ = 1 ∨ δ₀ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) {a b : Fin 3}
    {v : I → ℤ} (ha : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a v)
    (hb : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ b v) : a = b := by
  have h0 : caseZ0 a = caseZ0 b := by
    have h := ha.1.symm.trans hb.1
    rcases hδ₀ with hd | hd <;> rw [hd] at h <;> linarith
  have h2 : caseZ2 a = caseZ2 b := by
    have h := ha.2.2.1.symm.trans hb.2.2.1
    rcases hδ₂ with hd | hd <;> rw [hd] at h <;> linarith
  fin_cases a <;> fin_cases b <;> simp_all [caseZ0, caseZ2]

@[expose] def OffPairs {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (i₀ i₁ i₂ i₃ i₄ : I) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ) (p : H → I) (q : K → Fin 4 → I) (k : K)
    (v : I → ℤ) (a : Fin 3) (ξ : I) (x : ℤ) : Prop :=
  CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a v ∧ (∀ h, v (p h) = 0) ∧
    (∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i = if i = ξ then x else 0) ∧
    (x ≠ 0 → ξ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k) ∧ ∀ k' l, q k' l ≠ ξ)

theorem generic_caseA_scalar {s N u u' t σ σ' ϑ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hσ' : σ' = 1 ∨ σ' = -1) (hϑ : ϑ = 1 ∨ ϑ = -1) (hs : (s = 5 ∧ N = 2) ∨ (s = 4 ∧ N = 1))
    (h1 : s + 2 * σ * u + ϑ * t = 6) (h2 : s + 2 * σ' * u' + ϑ * t = 6)
    (hn : 2 * (u * u) + 2 * (u' * u') + t * t ≤ N) : s = 5 ∧ t = ϑ := by
  have hu := mul_self_nonneg u
  have hu' := mul_self_nonneg u'
  have ht := mul_self_nonneg t
  have bt : -1 ≤ t ∧ t ≤ 1 := by
    constructor <;> rcases hs with ⟨-, hN⟩ | ⟨-, hN⟩ <;> nlinarith
  have bu : -1 ≤ u ∧ u ≤ 1 := by
    constructor <;> rcases hs with ⟨-, hN⟩ | ⟨-, hN⟩ <;> nlinarith
  have bu' : -1 ≤ u' ∧ u' ≤ 1 := by
    constructor <;> rcases hs with ⟨-, hN⟩ | ⟨-, hN⟩ <;> nlinarith
  obtain ⟨btl, btu⟩ := bt
  obtain ⟨bul, buu⟩ := bu
  obtain ⟨bul', buu'⟩ := bu'
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> rcases hϑ with rfl | rfl <;>
    interval_cases t <;> interval_cases u <;> interval_cases u' <;> omega

theorem generic_caseB_scalar {s N u u' σ σ' : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hσ' : σ' = 1 ∨ σ' = -1) (hs : (s = 6 ∧ N = 1) ∨ (s = 4 ∧ N ≤ 2))
    (h1 : s + 2 * σ * u = 6) (h2 : s + 2 * σ' * u' = 6)
    (hn : 2 * (u * u) + 2 * (u' * u') ≤ N) : s = 6 ∧ u = 0 ∧ u' = 0 := by
  have hu := mul_self_nonneg u
  have hu' := mul_self_nonneg u'
  have bu : -1 ≤ u ∧ u ≤ 1 := by
    constructor <;> rcases hs with ⟨-, hN⟩ | ⟨-, hN⟩ <;> nlinarith
  have bu' : -1 ≤ u' ∧ u' ≤ 1 := by
    constructor <;> rcases hs with ⟨-, hN⟩ | ⟨-, hN⟩ <;> nlinarith
  obtain ⟨bul, buu⟩ := bu
  obtain ⟨bul', buu'⟩ := bu'
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;>
    interval_cases u <;> interval_cases u' <;> omega

theorem case_prod' (a b : Fin 3) : (if a = b then caseNorm a else 4) = 5 ∨
    (if a = b then caseNorm a else 4) = 6 ∨ (if a = b then caseNorm a else 4) = 4 := by
  fin_cases a <;> fin_cases b <;> simp [caseNorm]

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype K]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

section Cross

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype K] in
theorem q_mem_outK {k k' : K} (hkk : k ≠ k') (l : Fin 4) :
    q k' l ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k) :=
  mem_outK.mpr ⟨F.q_notMem_core k' l, fun h he => F.q_ne_p k' l h he.symm,
    fun _ he => hkk (F.q_inj he).1⟩

omit [Fintype K] in
theorem eq_of_agree (k : K) {v w : I → ℤ} (h₀ : v i₀ = w i₀) (h₁ : v i₁ = w i₁)
    (h₂ : v i₂ = w i₂) (h₃ : v i₃ = w i₃) (h₄ : v i₄ = w i₄) (hp : ∀ h, v (p h) = w (p h))
    (hq : ∀ l, v (q k l) = w (q k l))
    (hout : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i = w i) : v = w := by
  funext i
  by_cases hc : i ∈ ({i₀, i₁, i₂, i₃, i₄} : Finset I)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
  by_cases hph : ∃ h, p h = i
  · obtain ⟨h, rfl⟩ := hph
    exact hp h
  by_cases hql : ∃ l, q k l = i
  · obtain ⟨l, rfl⟩ := hql
    exact hq l
  push Not at hph hql
  exact hout i (mem_outK.mpr ⟨hc, hph, hql⟩)

omit [Fintype K] in
theorem offPairs_of_shape {k : K} {v : I → ℤ} {a : Fin 3}
    (hcore : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a v) (hp : ∀ h, v (p h) = 0)
    (hR : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i * v i = 6 - caseNorm a)
    (hY : ∀ k', v ⬝ᵥ Y k' = 0) :
    ∃ ξ x, x * x = 6 - caseNorm a ∧ OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v a ξ x := by
  have hnorm : caseNorm a = 5 ∨ caseNorm a = 6 := by
    fin_cases a <;> simp [caseNorm]
  rcases hnorm with h5 | h6
  · rw [h5] at hR ⊢
    obtain ⟨ξ, hξ, hξv, hrest⟩ := exists_unit_of_sum_mul_self_eq_one (by rw [hR]; norm_num)
    have hval : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i = if i = ξ then v ξ else 0 := by
      intro i hi
      by_cases hiξ : i = ξ
      · rw [ite_eq_left hiξ, hiξ]
      · rw [ite_eq_right hiξ, hrest i hi hiξ]
    refine ⟨ξ, v ξ, by rcases hξv with h | h <;> rw [h] <;> norm_num, hcore, hp, hval,
      fun hx => ⟨hξ, fun k' l hql => ?_⟩⟩
    by_cases hkk : k' = k
    · subst hkk
      exact (mem_outK.mp hξ).2.2 l hql
    ·
      have hq : ∀ l', v (q k' l') = if l' = l then v ξ else 0 := by
        intro l'
        rw [hval _ (F.q_mem_outK (Ne.symm hkk) l')]
        by_cases hl : l' = l
        · rw [ite_eq_left (by rw [hl, hql]), ite_eq_left hl]
        · rw [ite_eq_right (fun he => hl (F.q_inj (he.trans hql.symm)).2), ite_eq_right hl]
      have h := (F.dot_Y v k').symm.trans (hY k')
      rw [hq 0, hq 1, hq 2, hq 3] at h
      have hv0 : v ξ ≠ 0 := by rcases hξv with h' | h' <;> rw [h'] <;> norm_num
      have hη0 : ∀ l', η k' l' ≠ 0 := fun l' => by
        rcases F.sη k' l' with h' | h' <;> rw [h'] <;> norm_num
      rcases (by decide : ∀ l : Fin 4, l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) l with
        rfl | rfl | rfl | rfl <;> simp [Fin.ext_iff] at h <;> rcases h with h | h
      all_goals first | exact hη0 _ h | exact hv0 h
  · rw [h6] at hR ⊢
    have hval : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i = if i = i₀ then 0 else 0 := by
      intro i hi
      rw [ite_self]
      exact eq_zero_of_sum_mul_self_eq_zero' (by rw [hR]; norm_num) hi
    exact ⟨i₀, 0, by norm_num, hcore, hp, hval, fun hx => absurd rfl hx⟩

omit [Fintype K] F in
theorem offPairs_congr {k : K} {v w : I → ℤ} {a : Fin 3} {ξ : I} {x : ℤ}
    (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v a ξ x)
    (hcore : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a w) (hp : ∀ h, w (p h) = 0)
    (hout : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i = v i) :
    OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k w a ξ x :=
  ⟨hcore, hp, fun i hi => (hout i hi).trans (hv.2.2.1 i hi), hv.2.2.2⟩

omit [Fintype K] in
theorem dot_offPairs {k k' : K} (hkk : k ≠ k') {v w : I → ℤ} {a b : Fin 3} {ξ ξ' : I}
    {x x' : ℤ} (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v a ξ x)
    (hw : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k' w b ξ' x') :
    v ⬝ᵥ w = (if a = b then caseNorm a else 4) + x * (if ξ = ξ' then x' else 0) := by
  obtain ⟨⟨v0, v1, v2, v3, v4⟩, vp, vout, vξ⟩ := hv
  obtain ⟨⟨w0, w1, w2, w3, w4⟩, wp, wout, wξ⟩ := hw
  have hsplit := F.sum_split k fun i => v i * w i
  have hvw : v ⬝ᵥ w = ∑ i, v i * w i := rfl
  have hodd : ∑ h, v (p h) * w (p h) = 0 := Finset.sum_eq_zero fun h _ => by rw [vp h, zero_mul]
  have hq : ∑ l, v (q k l) * w (q k l) = 0 := Finset.sum_eq_zero fun l _ => by
    rw [wout _ (F.q_mem_outK (Ne.symm hkk) l)]
    by_cases hx' : x' = 0
    · simp [hx']
    · rw [ite_eq_right ((wξ hx').2 k l), mul_zero]
  have hrest : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), v i * w i =
      x * (if ξ = ξ' then x' else 0) := by
    by_cases hx : x = 0
    · rw [hx, zero_mul]
      exact Finset.sum_eq_zero fun i hi => by rw [vout i hi, hx, ite_self, zero_mul]
    · obtain ⟨hξ, hξq⟩ := vξ hx
      rw [Finset.sum_eq_single ξ (fun i hi hiξ => by rw [vout i hi, ite_eq_right hiξ, zero_mul])
        (fun h => absurd hξ h), vout ξ hξ, ite_eq_left rfl]
      congr 1
      have hξ' : ξ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k') :=
        mem_outK.mpr ⟨(mem_outK.mp hξ).1, (mem_outK.mp hξ).2.1, fun l => hξq k' l⟩
      exact wout ξ hξ'
  have hcore : v i₀ * w i₀ + v i₁ * w i₁ + v i₂ * w i₂ + v i₃ * w i₃ + v i₄ * w i₄ =
      if a = b then caseNorm a else 4 := by
    rw [v0, v1, v2, v3, v4, w0, w1, w2, w3, w4, ← case_prod a b]
    have s₀ := sign_mul_self F.sδ₀
    have s₁ := sign_mul_self F.sδ₁
    have s₂ := sign_mul_self F.sδ₂
    have s₃ := sign_mul_self F.sδ₃
    have s₄ := sign_mul_self F.sδ₄
    linear_combination (caseZ0 a * caseZ0 b) * s₀ + (caseZ0 a * caseZ0 b) * s₁ +
      (caseZ2 a * caseZ2 b) * s₂ + (caseZ2 a * caseZ2 b) * s₃ + (caseW a * caseW b) * s₄
  rw [hvw, hsplit, hodd, hq, hrest, ← hcore]
  ring

omit [Fintype K] in
theorem dot_pair_column {k : K} {v w : I → ℤ} {a b : Fin 3} {ξ : I} {x σ : ℤ} {e : Fin 2}
    (hv : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k v a ξ x)
    (hpair : PairAt (q k) (η k) v e σ) (hw : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ b w)
    (hwe : η k (pairA e) * w (q k (pairA e)) + η k (pairB e) * w (q k (pairB e)) = 0) :
    w ⬝ᵥ v = (if b = a then caseNorm b else 4) +
      2 * σ * (η k (pairA e) * w (q k (pairA e))) + x * w ξ := by
  obtain ⟨⟨v0, v1, v2, v3, v4⟩, vp, vout, vξ⟩ := hv
  obtain ⟨w0, w1, w2, w3, w4⟩ := hw
  obtain ⟨pa, pb, pa', pb'⟩ := hpair
  have hsplit := F.sum_split k fun i => w i * v i
  have hwv : w ⬝ᵥ v = ∑ i, w i * v i := rfl
  have hodd : ∑ h, w (p h) * v (p h) = 0 := Finset.sum_eq_zero fun h _ => by rw [vp h, mul_zero]
  have hq : ∑ l, w (q k l) * v (q k l) = 2 * σ * (η k (pairA e) * w (q k (pairA e))) := by
    rw [Fin.sum_univ_four]
    fin_cases e
    · simp only [pairA, pairB, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sub_zero,
        Matrix.cons_val_one] at pa pb pa' pb' hwe ⊢
      rw [pa, pb, pa', pb']
      linear_combination (-σ) * hwe
    · simp only [pairA, pairB, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, sub_self,
        Matrix.cons_val_zero] at pa pb pa' pb' hwe ⊢
      rw [pa, pb, pa', pb']
      linear_combination (-σ) * hwe
  have hrest : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * v i = x * w ξ := by
    by_cases hx : x = 0
    · rw [hx, zero_mul]
      exact Finset.sum_eq_zero fun i hi => by rw [vout i hi, hx, ite_self, mul_zero]
    · obtain ⟨hξ, -⟩ := vξ hx
      rw [Finset.sum_eq_single ξ (fun i hi hiξ => by rw [vout i hi, ite_eq_right hiξ, mul_zero])
        (fun h => absurd hξ h), vout ξ hξ, ite_eq_left rfl, mul_comm]
  have hcore : w i₀ * v i₀ + w i₁ * v i₁ + w i₂ * v i₂ + w i₃ * v i₃ + w i₄ * v i₄ =
      if b = a then caseNorm b else 4 := by
    rw [v0, v1, v2, v3, v4, w0, w1, w2, w3, w4, ← case_prod b a]
    have s₀ := sign_mul_self F.sδ₀
    have s₁ := sign_mul_self F.sδ₁
    have s₂ := sign_mul_self F.sδ₂
    have s₃ := sign_mul_self F.sδ₃
    have s₄ := sign_mul_self F.sδ₄
    linear_combination (caseZ0 b * caseZ0 a) * s₀ + (caseZ0 b * caseZ0 a) * s₁ +
      (caseZ2 b * caseZ2 a) * s₂ + (caseZ2 b * caseZ2 a) * s₃ + (caseW b * caseW a) * s₄
  rw [hwv, hsplit, hodd, hq, hrest, ← hcore]
  ring

end Cross

end Frame

end CFSG.Wreathed.FlatComplete
