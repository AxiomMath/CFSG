module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4OrthLin
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.LieType.Universal.SpinOmega.Reflections

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter CFSG.LieType.Universal.Spin

@[expose] def frameSel (c : Fin 8 → Bool) : (Fin 4 → Fin 8) × (Fin 4 → Fin 8) × Fin 8 :=
  let T := (List.finRange 8).filter (fun k => c k)
  let F := (List.finRange 8).filter (fun k => !c k)
  if 6 ≤ T.length then
    (fun k => T.getD (k.val + 1) 0, fun _ => T.getD 0 0, T.getD 5 0)
  else if 6 ≤ F.length then
    (fun k => F.getD (k.val + 1) 0, fun _ => F.getD 0 0, F.getD 5 0)
  else
    let A := if F.length ≤ T.length then T else F
    let B := if F.length ≤ T.length then F else T
    (![A.getD 1 0, A.getD 2 0, A.getD 3 0, B.getD 1 0],
      ![A.getD 0 0, A.getD 0 0, A.getD 0 0, B.getD 0 0],
      if 5 ≤ A.length then A.getD 4 0 else B.getD 2 0)

@[expose] def FrameGood (c : Fin 8 → Bool) (d : (Fin 4 → Fin 8) × (Fin 4 → Fin 8) × Fin 8) :
    Prop :=
  (∀ k, c (d.1 k) = c (d.2.1 k)) ∧ (∀ k l, d.1 k = d.1 l → k = l) ∧
    (∀ k l, d.2.1 k ≠ d.1 l) ∧ (∀ k, d.2.2 ≠ d.1 k ∧ d.2.2 ≠ d.2.1 k)

instance (c : Fin 8 → Bool) (d : (Fin 4 → Fin 8) × (Fin 4 → Fin 8) × Fin 8) :
    Decidable (FrameGood c d) := by
  unfold FrameGood; infer_instance

theorem frameSel_good (c : Fin 8 → Bool) : FrameGood c (frameSel c) := by
  have hc : c = ![c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7] := by
    funext i; fin_cases i <;> rfl
  rw [hc]
  generalize c 0 = b0
  generalize c 1 = b1
  generalize c 2 = b2
  generalize c 3 = b3
  generalize c 4 = b4
  generalize c 5 = b5
  generalize c 6 = b6
  generalize c 7 = b7
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;>
    cases b7 <;> decide

theorem isSquare_div_of_iff {K : Type*} [Field K] [Fintype K] [DecidableEq K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : IsSquare a ↔ IsSquare b) : IsSquare (a / b) := by
  by_cases hA : IsSquare a
  · exact hA.div (h.mp hA)
  · have hB : ¬ IsSquare b := fun hB => hA (h.mpr hB)
    rw [← quadraticChar_one_iff_isSquare (div_ne_zero ha hb)]
    have hχa := quadraticChar_neg_one_iff_not_isSquare.mpr hA
    have hχb := quadraticChar_neg_one_iff_not_isSquare.mpr hB
    have hinv : quadraticChar K b * quadraticChar K b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hb, map_one]
    rw [hχb] at hinv
    have hχbinv : quadraticChar K b⁻¹ = -1 := by linarith
    rw [div_eq_mul_inv, map_mul, hχa, hχbinv]
    norm_num

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_commute_of_eigen {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x : V} (hx : g x = x ∨ g x = -x) :
    g * reflect Q x = reflect Q x * g := by
  have h := reflect_conj hg x
  have hr : reflect Q (g x) = reflect Q x := by
    rcases hx with h' | h'
    · rw [h']
    · rw [h', show -x = (-1 : K) • x by rw [neg_one_smul], reflect_smul_of_ne_zero
        (neg_ne_zero.mpr one_ne_zero)]
  rw [hr] at h
  calc g * reflect Q x = g * reflect Q x * g⁻¹ * g := by group
    _ = reflect Q x * g := by rw [h]

theorem reflect_apply_frame {ι : Type*} [DecidableEq ι] {x : ι → V} (hx : IsOrthFamily Q x)
    (m l : ι) : reflect Q (x m) (x l) = (if m = l then -1 else 1 : K) • x l := by
  by_cases h : m = l
  · subst h
    simp [reflect_apply_self (hx.1 m)]
  · simp [h, reflect_apply_of_polar_eq_zero (hx.2 m l h)]

theorem reflect_comm_frame {ι : Type*} {x : ι → V} (hx : IsOrthFamily Q x) (m l : ι) :
    reflect Q (x m) * reflect Q (x l) = reflect Q (x l) * reflect Q (x m) := by
  by_cases h : m = l
  · rw [h]
  · exact reflect_comm (hx.2 m l h)

@[expose] def FourCommuting (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) : Prop :=
  ∃ u : Fin 4 → (V ≃ₗ[K] V),
    (∀ k, u k ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
    (∀ k, u k * u k ∈ scalars K V) ∧ (∀ i j, u i * u j = u j * u i) ∧
    (∀ k, u k * g = g * u k) ∧
    ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun k => u k ^ (a k : ℕ)).prod ∉ scalars K V

theorem eq_of_smul_eq_smul {c e : K} {v : V} (hv : v ≠ 0) (h : e • v = c • v) : e = c := by
  have h' : (e - c) • v = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hv)

theorem fourCommuting_of_sq_one [Fintype K] [DecidableEq K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hdim : 8 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) : FourCommuting Q g := by
  classical
  obtain ⟨x, hx, hxe⟩ := exists_eigen_frame h2 hnd hg hg2 8 hdim
  set c : Fin 8 → Bool := fun k => decide (IsSquare (Q (x k))) with hc
  obtain ⟨hcls, hinj, hpi, hspare⟩ := frameSel_good c
  set i := (frameSel c).1 with hi
  set p := (frameSel c).2.1 with hp
  set j := (frameSel c).2.2 with hj
  have hx0 : ∀ l, x l ≠ 0 := fun l h => hx.1 l (by rw [h, QuadraticMap.map_zero])
  have hscale : ∀ k, ∃ t : K, t ≠ 0 ∧ Q (t • x (i k)) = Q (x (p k)) := by
    intro k
    have hiff : IsSquare (Q (x (p k))) ↔ IsSquare (Q (x (i k))) := by
      have := hcls k
      simp only [hc, decide_eq_decide] at this
      exact this.symm
    obtain ⟨t, ht⟩ := isSquare_div_of_iff (hx.1 (p k)) (hx.1 (i k)) hiff
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at ht
      exact ht.elim (hx.1 _) (hx.1 _)
    refine ⟨t, ht0, ?_⟩
    rw [map_smul_eq_sq, pow_two, ← ht, div_mul_cancel₀ _ (hx.1 _)]
  set u : Fin 4 → (V ≃ₗ[K] V) := fun k => reflect Q (x (p k)) * reflect Q (x (i k)) with hu
  have hcomm : ∀ m l, reflect Q (x m) * reflect Q (x l) = reflect Q (x l) * reflect Q (x m) :=
    reflect_comm_frame hx
  have hact : ∀ k l, u k (x l) =
      ((if p k = l then -1 else 1) * (if i k = l then -1 else 1) : K) • x l := by
    intro k l
    rw [hu, LinearEquiv.mul_apply, reflect_apply_frame hx, map_smul, reflect_apply_frame hx,
      smul_smul, mul_comm]
  refine ⟨u, fun k => ?_, fun k => ?_, fun k l => ?_, fun k => ?_, fun a ha hsc => ?_⟩
  · obtain ⟨t, ht0, htQ⟩ := hscale k
    have h := reflect_mul_reflect_mem_commutator h2 (p := x (p k)) (q := t • x (i k))
      (by rw [polar_smul_right, hx.2 _ _ (hpi k k), smul_zero]) htQ.symm
      (by rw [htQ]; exact hx.1 _)
    rwa [reflect_smul_of_ne_zero ht0] at h
  · have h1 : u k * u k = 1 := by
      calc u k * u k = reflect Q (x (p k)) * (reflect Q (x (i k)) * reflect Q (x (p k))) *
            reflect Q (x (i k)) := by simp only [hu, mul_assoc]
        _ = reflect Q (x (p k)) * (reflect Q (x (p k)) * reflect Q (x (i k))) *
            reflect Q (x (i k)) := by rw [hcomm (i k) (p k)]
        _ = (reflect Q (x (p k)) * reflect Q (x (p k))) *
            (reflect Q (x (i k)) * reflect Q (x (i k))) := by simp only [mul_assoc]
        _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]
    rw [h1]
    exact one_mem _
  · have hc' : ∀ a b : Fin 8, Commute (reflect Q (x a)) (reflect Q (x b)) := fun a b => hcomm a b
    exact ((hc' (p k) (p l)).mul_right (hc' (p k) (i l))).mul_left
      ((hc' (i k) (p l)).mul_right (hc' (i k) (i l)))
  · rw [hu, mul_assoc, ← reflect_commute_of_eigen hg (hxe (i k)), ← mul_assoc,
      ← reflect_commute_of_eigen hg (hxe (p k)), mul_assoc]
  · obtain ⟨c0, hc0⟩ := mem_scalars.mp hsc
    have hprod : ∀ l, (List.ofFn fun k => u k ^ (a k : ℕ)).prod (x l) =
        (∏ k, ((if p k = l then -1 else 1) * (if i k = l then -1 else 1) : K) ^ (a k : ℕ)) •
          x l := fun l => prod_ofFn_pow_apply (fun k => hact k l) (fun k => (a k : ℕ))
    have hj1 : c0 = 1 := by
      have h := hprod j
      rw [hc0] at h
      have he : (∏ k, ((if p k = j then -1 else 1) * (if i k = j then -1 else 1) : K) ^
          (a k : ℕ)) = 1 := Finset.prod_eq_one fun k _ => by
        rw [ite_eq_right (hspare k).2.symm, ite_eq_right (hspare k).1.symm, one_mul, one_pow]
      rw [he, one_smul] at h
      exact eq_of_smul_eq_smul (hx0 j) (by rw [one_smul]; exact h)
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, a k₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    have ha1 : (a k₀ : ℕ) = 1 := by
      have := (a k₀).isLt
      have h0 : (a k₀ : ℕ) ≠ 0 := fun h => hk₀ (Fin.ext h)
      omega
    have h := hprod (i k₀)
    rw [hc0] at h
    have he : (∏ k, ((if p k = i k₀ then -1 else 1) * (if i k = i k₀ then -1 else 1) : K) ^
        (a k : ℕ)) = -1 := by
      rw [Finset.prod_eq_single k₀]
      · rw [ite_eq_right (hpi k₀ k₀), ite_eq_left rfl, one_mul, ha1, pow_one]
      · intro k _ hk
        rw [ite_eq_right (hpi k k₀), ite_eq_right (fun h => hk (hinj k k₀ h)), one_mul, one_pow]
      · intro h
        exact absurd (Finset.mem_univ k₀) h
    rw [he, hj1, one_smul] at h
    have h' : (2 : K) • x (i k₀) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h]
      rw [neg_smul, one_smul, add_neg_cancel]
    exact hx0 _ ((smul_eq_zero.mp h').resolve_left h2)

theorem fourCommuting_of_sq_neg_one [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) (hdim : 8 ≤ Module.finrank K V)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgΩ : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hg2 : ∀ v, g (g v) = -v) : FourCommuting Q g := by
  classical
  obtain ⟨w, hw⟩ := exists_plane_frame h2 hnd hg hg2 3 (by omega)
  obtain ⟨⟨y, hy0, hyw⟩, -⟩ := exists_orth_of_lt_finrank h2 hnd hw
    (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
  set F := planeFamily g w with hF
  have hF0 : ∀ m, F m ≠ 0 := fun m h => hw.1 m (by rw [h, QuadraticMap.map_zero])
  have hcomm : ∀ m l, reflect Q (F m) * reflect Q (F l) = reflect Q (F l) * reflect Q (F m) :=
    reflect_comm_frame hw
  set h : Fin 3 → (V ≃ₗ[K] V) := fun k => reflect Q (F (.inl k)) * reflect Q (F (.inr k))
    with hh
  have hact : ∀ k m, h k (F m) =
      ((if (Sum.inl k : Fin 3 ⊕ Fin 3) = m then -1 else 1) *
        (if (Sum.inr k : Fin 3 ⊕ Fin 3) = m then -1 else 1) : K) • F m := by
    intro k m
    rw [hh, LinearEquiv.mul_apply, reflect_apply_frame hw, map_smul, reflect_apply_frame hw,
      smul_smul, mul_comm]
  have hhy : ∀ k, h k y = y := fun k => by
    have hr : polar Q (F (.inr k)) y = 0 := by rw [polar_comm]; exact hyw (.inr k)
    have hl : polar Q (F (.inl k)) y = 0 := by rw [polar_comm]; exact hyw (.inl k)
    rw [hh]
    change reflect Q (F (.inl k)) (reflect Q (F (.inr k)) y) = y
    rw [reflect_apply_of_polar_eq_zero hr, reflect_apply_of_polar_eq_zero hl]
  have hh2 : ∀ k, h k * h k = 1 := fun k => by
    calc h k * h k = reflect Q (F (.inl k)) * (reflect Q (F (.inr k)) *
          reflect Q (F (.inl k))) * reflect Q (F (.inr k)) := by simp only [hh, mul_assoc]
      _ = reflect Q (F (.inl k)) * (reflect Q (F (.inl k)) * reflect Q (F (.inr k))) *
          reflect Q (F (.inr k)) := by rw [hcomm (.inr k) (.inl k)]
      _ = (reflect Q (F (.inl k)) * reflect Q (F (.inl k))) *
          (reflect Q (F (.inr k)) * reflect Q (F (.inr k))) := by simp only [mul_assoc]
      _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]
  have hhcomm : ∀ k l, h k * h l = h l * h k := fun k l => by
    have hc' : ∀ a b, Commute (reflect Q (F a)) (reflect Q (F b)) := fun a b => hcomm a b
    exact ((hc' (.inl k) (.inl l)).mul_right (hc' (.inl k) (.inr l))).mul_left
      ((hc' (.inr k) (.inl l)).mul_right (hc' (.inr k) (.inr l)))
  have hhg : ∀ k, h k * g = g * h k := fun k => by
    have e1 := reflect_conj hg (F (.inl k))
    have e2 := reflect_conj hg (F (.inr k))
    have hgF1 : g (F (.inl k)) = F (.inr k) := rfl
    have hgF2 : g (F (.inr k)) = (-1 : K) • F (.inl k) := by
      change g (g (w k)) = (-1 : K) • w k
      rw [hg2, neg_one_smul]
    rw [hgF1] at e1
    rw [hgF2, reflect_smul_of_ne_zero (neg_ne_zero.mpr one_ne_zero)] at e2
    have hconj : g * h k * g⁻¹ = h k := by
      calc g * h k * g⁻¹ = (g * reflect Q (F (.inl k)) * g⁻¹) *
            (g * reflect Q (F (.inr k)) * g⁻¹) := by
              simp only [hh, mul_assoc, inv_mul_cancel_left]
        _ = h k := by rw [e1, e2, hcomm]
    calc h k * g = g * h k * g⁻¹ * g := by rw [hconj]
      _ = g * h k := by group
  have hhΩ : ∀ k, h k ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    fun k => reflect_mul_reflect_mem_commutator h2 (hw.2 (.inl k) (.inr k) Sum.inl_ne_inr)
      (by change Q (w k) = Q (g (w k)); rw [map_of_mem hg]) (hw.1 (.inr k))
  have hgsc : g * g ∈ scalars K V := mem_scalars.mpr ⟨-1, fun v => by
    rw [LinearEquiv.mul_apply, hg2, neg_one_smul]⟩
  refine ⟨Fin.snoc h g, fun k => ?_, fun k => ?_, fun k l => ?_, fun k => ?_, fun a ha hsc => ?_⟩
  · induction k using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hgΩ
    | cast k => rw [Fin.snoc_castSucc]; exact hhΩ k
  · induction k using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hgsc
    | cast k => rw [Fin.snoc_castSucc, hh2]; exact one_mem _
  · induction k using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last => rfl
      | cast l => rw [Fin.snoc_last, Fin.snoc_castSucc, hhg]
    | cast k =>
      induction l using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc, hhg]
      | cast l => rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hhcomm]
  · induction k using Fin.lastCases with
    | last => rw [Fin.snoc_last]
    | cast k => rw [Fin.snoc_castSucc, hhg]
  · obtain ⟨c0, hc0⟩ := mem_scalars.mp hsc
    rw [List.ofFn_succ', List.prod_concat] at hc0
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hc0
    set H := (List.ofFn fun k : Fin 3 => h k ^ (a (Fin.castSucc k) : ℕ)).prod with hH
    have hHF : ∀ m, H (F m) = (∏ k : Fin 3, ((if (Sum.inl k : Fin 3 ⊕ Fin 3) = m then -1 else 1) *
        (if (Sum.inr k : Fin 3 ⊕ Fin 3) = m then -1 else 1) : K) ^ (a (Fin.castSucc k) : ℕ)) •
          F m := fun m => prod_ofFn_pow_apply (fun k => hact k m) _
    have hHy : H y = y := by
      have := prod_ofFn_pow_apply (g := h) (t := y) (c := fun _ => (1 : K))
        (fun k => by rw [one_smul]; exact hhy k) (fun k => (a (Fin.castSucc k) : ℕ))
      rw [this, Finset.prod_eq_one (fun k _ => one_pow _), one_smul]
    have hval : ∀ b : Fin 2, (b : ℕ) = 0 ∨ (b : ℕ) = 1 := fun b => by
      have := b.isLt; omega
    rcases hval (a (Fin.last 3)) with h3 | h3
    ·
      rw [h3, pow_zero, mul_one] at hc0
      have hc1 : c0 = 1 := by
        have h' := hc0 y
        rw [hHy] at h'
        exact eq_of_smul_eq_smul hy0 (by rw [one_smul]; exact h'.symm)
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin 3, a (Fin.castSucc k₀) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply ha
        funext k
        induction k using Fin.lastCases with
        | last => exact Fin.ext h3
        | cast k => exact hcon k
      have ha1 : (a (Fin.castSucc k₀) : ℕ) = 1 :=
        (hval _).resolve_left (fun h => hk₀ (Fin.ext h))
      have h' := hc0 (F (.inl k₀))
      rw [hHF, hc1, one_smul] at h'
      have he : (∏ k : Fin 3, ((if (Sum.inl k : Fin 3 ⊕ Fin 3) = Sum.inl k₀ then -1 else 1) *
          (if (Sum.inr k : Fin 3 ⊕ Fin 3) = Sum.inl k₀ then -1 else 1) : K) ^
            (a (Fin.castSucc k) : ℕ)) = -1 := by
        rw [Finset.prod_eq_single k₀]
        · rw [ite_eq_left rfl, ite_eq_right Sum.inr_ne_inl, mul_one, ha1, pow_one]
        · intro k _ hk
          rw [ite_eq_right (fun e => hk (Sum.inl_injective e)), ite_eq_right Sum.inr_ne_inl,
            one_mul, one_pow]
        · intro e
          exact absurd (Finset.mem_univ k₀) e
      rw [he, neg_one_smul] at h'
      have h'' : (2 : K) • F (.inl k₀) = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h']
        exact neg_add_cancel _
      exact hF0 _ ((smul_eq_zero.mp h'').resolve_left h2)
    ·
      rw [h3, pow_one] at hc0
      have h' := hc0 (w 0)
      rw [LinearEquiv.mul_apply] at h'
      change H (F (.inr 0)) = c0 • F (.inl 0) at h'
      rw [hHF] at h'
      set e := (∏ k : Fin 3, ((if (Sum.inl k : Fin 3 ⊕ Fin 3) = Sum.inr 0 then -1 else 1) *
        (if (Sum.inr k : Fin 3 ⊕ Fin 3) = Sum.inr 0 then -1 else 1) : K) ^
          (a (Fin.castSucc k) : ℕ)) with he
      have he0 : e ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by
        split_ifs <;> norm_num)
      have hpol := hw.2 (.inl 0) (.inr 0) Sum.inl_ne_inr
      have hpol' : polar Q (F (.inl 0)) (e • F (.inr 0)) = 0 := by
        rw [polar_smul_right, hpol, smul_zero]
      rw [h', polar_smul_right, polar_self_eq_two_mul', smul_eq_mul] at hpol'
      have hc00 : c0 = 0 := by
        rcases mul_eq_zero.mp hpol' with h0 | h0
        · exact h0
        · exact absurd ((mul_eq_zero.mp h0).resolve_left h2) (hw.1 _)
      rw [hc00, zero_smul] at h'
      exact hF0 _ ((smul_eq_zero.mp h').resolve_left he0)

end CFSG.ComponentClassification.Sol76T13.Hq4
