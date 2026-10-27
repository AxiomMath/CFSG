module

public import CFSG.LieType.Universal.Unitary.Roots.Elements

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Universal.SpecialLinear

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (σ) in
private def hf (x y : Fin n → F) : F := ∑ i, σ (x i) * y (Fin.rev i)

private def act (g : SU σ n) (v : Fin n → F) : Fin n → F :=
  ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v

private theorem act_mul (g h : SU σ n) (v : Fin n → F) : act (g * h) v = act g (act h v) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

private theorem act_one (v : Fin n → F) : act (1 : SU σ n) v = v := by
  simp only [act, OneMemClass.coe_one, Units.val_one, one_mulVec]

private theorem act_smul (g : SU σ n) (c : F) (v : Fin n → F) : act g (c • v) = c • act g v :=
  mulVec_smul _ _ _

private theorem act_inv_act (g : SU σ n) (v : Fin n → F) : act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

private theorem act_injective (g : SU σ n) : Function.Injective (act g) := fun v w h => by
  rw [← act_inv_act g v, h, act_inv_act]

private theorem hf_eq_dotProduct (x y : Fin n → F) :
    hf σ x y = (fun i => σ (x i)) ⬝ᵥ (antidiag n *ᵥ y) := by
  simp only [hf, dotProduct, mulVec, antidiag, of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single (Fin.rev i) (fun j _ hj => by simp [hj]) (by simp)]
  simp

private theorem hf_act (g : SU σ n) (x y : Fin n → F) : hf σ (act g x) (act g y) = hf σ x y := by
  obtain ⟨-, hiso⟩ := g.2
  set A := ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hσx : (fun i => σ ((A *ᵥ x) i)) = A.map σ *ᵥ fun i => σ (x i) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  have hJ : (A.map σ)ᵀ * antidiag n * A = antidiag n := hiso
  rw [hf_eq_dotProduct, hf_eq_dotProduct, act, act, hσx, ← vecMul_transpose,
    ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hJ]

private theorem hf_single_left (s : Fin n) (c : F) (y : Fin n → F) :
    hf σ (Pi.single s c) y = σ c * y (Fin.rev s) := by
  rw [hf, Finset.sum_eq_single s (fun i _ hi => by simp [hi]) (by simp)]
  simp

private theorem hf_add_left (x x' y : Fin n → F) : hf σ (x + x') y = hf σ x y + hf σ x' y := by
  simp only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem act_single_ne_zero (g : SU σ n) (s : Fin n) :
    act g (Pi.single s (1 : F)) ≠ 0 := by
  intro h
  have := act_injective g (h.trans (mulVec_zero _).symm)
  have h1 := congrFun this s
  simp at h1

private theorem act_single (g : SU σ n) (s : Fin n) (c : F) :
    act g (Pi.single s c) = c • act g (Pi.single s 1) := by
  rw [← act_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

variable (hσ : ∀ c, σ (σ c) = c)

private theorem act_rootHom {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
    (c : F) (v : Fin n → F) :
    act (rootHom σ hσ hij hi hj (Multiplicative.ofAdd c)) v =
      v + Pi.single i (c * v j) - Pi.single (Fin.rev j) (σ c * v (Fin.rev i)) := by
  rw [act, coe_rootHom, toAdd_ofAdd, rootMatrix_mulVec]

omit hσ in
private theorem act_longRootHom {i : Fin n} (hi : i ≠ Fin.rev i) (c : traceZero σ)
    (v : Fin n → F) :
    act (longRootHom σ hi (Multiplicative.ofAdd c)) v = v + Pi.single i (c * v (Fin.rev i)) := by
  rw [act, coe_longRootHom, toAdd_ofAdd, longRootMatrix_mulVec]

private noncomputable def heisElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a),
    by
      rw [heisenbergMatrix_mul σ hi hik hk, map_neg, add_neg_cancel,
        show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero],
    by
      rw [heisenbergMatrix_mul σ hi hik hk, neg_add_cancel,
        show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

private theorem heisElt_mem {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) :
    heisElt hσ hi hik hk a b hab ∈ heisenbergSubgroup σ hσ hi hik hk :=
  ⟨a, b, hab, rfl⟩

private theorem act_heisElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) (v : Fin n → F) :
    act (heisElt hσ hi hik hk a b hab) v =
      v + Pi.single i (a * v k) - Pi.single k (σ a * v (Fin.rev i)) +
        Pi.single i (b * v (Fin.rev i)) :=
  heisenbergMatrix_mulVec σ i k a b v

private def Out (k : ℕ) (s : Fin n) : Prop := s.val < k ∨ (Fin.rev s).val < k

omit hσ in
private theorem not_out {k : ℕ} {t : Fin n} (h1 : k ≤ t.val) (h2 : t.val + k < n) : ¬Out k t := by
  simp only [Out, Fin.val_rev, not_or, not_lt]
  omega

omit hσ in
private theorem ne_of_out {k : ℕ} {s t : Fin n} (hs : Out k s) (ht : ¬Out k t) : s ≠ t :=
  fun h => ht (h ▸ hs)

omit hσ in
private theorem single_one_apply_of_ne {s t : Fin n} (h : t ≠ s) :
    (Pi.single s (1 : F) : Fin n → F) t = 0 :=
  Pi.single_eq_of_ne h 1

section Clear

variable {R : Subgroup (SU σ n)}
  (hR₁ : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
    j ≠ Fin.rev i → ∀ c, rootHom σ hσ hij hi hj c ∈ R)
  (hR₂ : ∀ (i : Fin n) (hi : i ≠ Fin.rev i) c, longRootHom σ hi c ∈ R)
  (hR₃ : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
    heisenbergSubgroup σ hσ hi hik hk ≤ R)

include hR₂ in
private theorem clear_base {kk : Fin n} (hkk : 2 * kk.val + 1 < n) {v : Fin n → F}
    (hv : ∀ s, Out kk.val s → v s = 0) (hv' : v (Fin.rev kk) ≠ 0) (hvv : hf σ v v = 0)
    (hz : ∀ l : Fin n, kk.val < l.val → l.val < (Fin.rev kk).val → v l = 0) :
    ∃ r ∈ R, (∀ s, Out kk.val s → act r (Pi.single s 1) = Pi.single s 1) ∧
      act r (Pi.single kk 1) = Pi.single kk 1 ∧
      act r v = Pi.single (Fin.rev kk) (v (Fin.rev kk)) := by
  have hne : kk ≠ Fin.rev kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
  have hk1 : ¬Out kk.val kk := not_out le_rfl (by omega)
  have hk2 : ¬Out kk.val (Fin.rev kk) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  set x := v kk
  set y := v (Fin.rev kk)
  have hdecomp : v = Pi.single kk x + Pi.single (Fin.rev kk) y := by
    funext l
    by_cases hl1 : l = kk
    · subst hl1
      simp [hne, x]
    by_cases hl2 : l = Fin.rev kk
    · subst hl2
      simp [Ne.symm hne, y]
    rw [Pi.add_apply, Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2, add_zero]
    have hl1' : l.val ≠ kk.val := fun h => hl1 (Fin.ext h)
    have hl2' : l.val ≠ (Fin.rev kk).val := fun h => hl2 (Fin.ext h)
    rw [Fin.val_rev] at hl2'
    by_cases hout : Out kk.val l
    · exact hv l hout
    · simp only [Out, Fin.val_rev, not_or, not_lt] at hout
      exact hz l (by omega) (by rw [Fin.val_rev]; omega)
  have hxy : σ x * y + σ y * x = 0 := by
    have h := hvv
    rw [hdecomp, hf_add_left, hf_single_left, hf_single_left, Fin.rev_rev, Pi.add_apply,
      Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, zero_add, add_zero] at h
    exact h
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hv'
  have hc : -x / y + σ (-x / y) = 0 := by
    rw [map_div₀, map_neg, div_add_div _ _ hv' hσy, div_eq_zero_iff]
    left
    linear_combination (-1 : F) * hxy
  refine ⟨longRootHom σ hne (Multiplicative.ofAdd ⟨-x / y, (mem_traceZero σ).mpr hc⟩),
    hR₂ _ _ _, fun s hs => ?_, ?_, ?_⟩
  · rw [act_longRootHom, single_one_apply_of_ne (Ne.symm (ne_of_out hs hk2)), mul_zero,
      Pi.single_zero, add_zero]
  · rw [act_longRootHom, single_one_apply_of_ne (Ne.symm hne), mul_zero, Pi.single_zero,
      add_zero]
  · rw [act_longRootHom]
    funext l
    simp only [Pi.add_apply]
    by_cases hl1 : l = kk
    · subst hl1
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne]
      field_simp
      ring
    · rw [Pi.single_eq_of_ne hl1, add_zero]
      nth_rewrite 1 [hdecomp]
      simp [Pi.single_eq_of_ne hl1]

include hR₁ hR₃ in
private theorem clear_step (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) {kk : Fin n}
    (hkk : 2 * kk.val + 1 < n) {jj : Fin n} (hj1 : kk.val < jj.val)
    (hj2 : jj.val < (Fin.rev kk).val) (v : Fin n → F) (hv' : v (Fin.rev kk) ≠ 0) :
    ∃ r ∈ R, (∀ s, Out kk.val s → act r (Pi.single s 1) = Pi.single s 1) ∧
      act r (Pi.single kk 1) = Pi.single kk 1 ∧ act r v jj = 0 ∧
      ∀ l, l ≠ jj → l ≠ kk → act r v l = v l := by
  rw [Fin.val_rev] at hj2
  have hne : kk ≠ Fin.rev kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
  have hkj : kk ≠ jj := Fin.ne_of_val_ne (by omega)
  have hjk' : jj ≠ Fin.rev kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
  have hk2 : ¬Out kk.val (Fin.rev kk) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  have hj3 : ¬Out kk.val jj := not_out (by omega) (by omega)
  have hj4 : ¬Out kk.val (Fin.rev jj) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  by_cases hmid : Fin.rev jj = jj
  · set a₀ := σ (v jj / v (Fin.rev kk))
    have hσa : σ a₀ = v jj / v (Fin.rev kk) := hσ _
    obtain ⟨b₀, hb₀⟩ := htr (-(σ a₀ * a₀)) (by rw [map_neg, map_mul, hσ, mul_comm])
    have hab : b₀ + σ b₀ + σ a₀ * a₀ = 0 := by rw [hb₀]; ring
    refine ⟨heisElt hσ hne hkj hmid a₀ b₀ hab, hR₃ _ _ _ _ _ (heisElt_mem hσ _ _ _ _ _ _),
      fun s hs => ?_, ?_, ?_, fun l hl1 hl2 => ?_⟩
    · rw [act_heisElt, single_one_apply_of_ne (Ne.symm (ne_of_out hs hj3)),
        single_one_apply_of_ne (Ne.symm (ne_of_out hs hk2))]
      simp
    · rw [act_heisElt, single_one_apply_of_ne (Ne.symm hkj),
        single_one_apply_of_ne (Ne.symm hne)]
      simp
    · rw [act_heisElt]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hkj), Pi.single_eq_same,
        hσa]
      field_simp
      ring
    · rw [act_heisElt]
      simp [Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2]
  · have hk3 : Fin.rev kk ≠ Fin.rev (Fin.rev kk) := rev_ne_rev_rev hne
    have hkj' : Fin.rev kk ≠ Fin.rev jj := fun h => hkj (Fin.rev_injective h)
    have hjj : jj ≠ Fin.rev jj := fun h => hmid h.symm
    refine ⟨rootHom σ hσ hjk' hjj hk3 (Multiplicative.ofAdd (-(v jj) / v (Fin.rev kk))),
      hR₁ _ _ _ _ _ hkj' _, fun s hs => ?_, ?_, ?_, fun l hl1 hl2 => ?_⟩
    · rw [act_rootHom, single_one_apply_of_ne (Ne.symm (ne_of_out hs hk2)),
        single_one_apply_of_ne (Ne.symm (ne_of_out hs hj4))]
      simp
    · rw [act_rootHom, single_one_apply_of_ne (Ne.symm hne),
        single_one_apply_of_ne (fun h => hjk' (by rw [← h, Fin.rev_rev]))]
      simp
    · rw [act_rootHom, Fin.rev_rev]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hkj)]
      field_simp
      ring
    · rw [act_rootHom, Fin.rev_rev]
      simp [Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2]

include hR₁ hR₂ hR₃ in
private theorem exists_clear (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) {kk : Fin n}
    (hkk : 2 * kk.val + 1 < n) :
    ∀ t : ℕ, ∀ v : Fin n → F, (∀ s, Out kk.val s → v s = 0) → v (Fin.rev kk) ≠ 0 →
      hf σ v v = 0 → (∀ l : Fin n, kk.val < l.val → l.val + t < (Fin.rev kk).val → v l = 0) →
      ∃ r ∈ R, (∀ s, Out kk.val s → act r (Pi.single s 1) = Pi.single s 1) ∧
        act r (Pi.single kk 1) = Pi.single kk 1 ∧
        act r v = Pi.single (Fin.rev kk) (v (Fin.rev kk)) := by
  have hk1 : ¬Out kk.val kk := not_out le_rfl (by omega)
  have hk2 : ¬Out kk.val (Fin.rev kk) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  intro t
  induction t with
  | zero =>
    intro v hv hv' hvv hz
    exact clear_base hR₂ hkk hv hv' hvv fun l h1 h2 => hz l h1 (by omega)
  | succ t ih =>
    intro v hv hv' hvv hz
    by_cases hj : kk.val + (t + 1) < (Fin.rev kk).val
    · obtain ⟨r₀, hr₀, hfix, hfixk, h0, hsame⟩ := clear_step hσ hR₁ hR₃ htr hkk
        (jj := ⟨(Fin.rev kk).val - (t + 1), by omega⟩) (by simp only; omega) (by simp only; omega)
        v hv'
      have hjk2 : Fin.rev kk ≠ ⟨(Fin.rev kk).val - (t + 1), by omega⟩ :=
        Fin.ne_of_val_ne (by simp only; omega)
      have hkk2 : Fin.rev kk ≠ kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
      have hv'' : act r₀ v (Fin.rev kk) = v (Fin.rev kk) := hsame _ hjk2 hkk2
      obtain ⟨r, hr, hfix', hfixk', hrv⟩ := ih (act r₀ v)
        (fun s hs => by
          rw [hsame s (fun h => ?_) (ne_of_out hs hk1), hv s hs]
          subst h
          exact not_out (k := kk.val) (by simp only; omega) (by simp only [Fin.val_rev] at *; omega)
            hs)
        (by rw [hv'']; exact hv') (by rw [hf_act]; exact hvv)
        (fun l h1 h2 => by
          by_cases hl : l = ⟨(Fin.rev kk).val - (t + 1), by omega⟩
          · rw [hl]
            exact h0
          · rw [hsame l hl (fun h => by rw [h] at h1; omega)]
            exact hz l h1 (by
              have : l.val ≠ (Fin.rev kk).val - (t + 1) := fun h => hl (Fin.ext h)
              omega))
      refine ⟨r * r₀, mul_mem hr hr₀, fun s hs => ?_, ?_, ?_⟩
      · rw [act_mul, hfix s hs, hfix' s hs]
      · rw [act_mul, hfixk, hfixk']
      · rw [act_mul, hrv, hv'']
    · exact ih v hv hv' hvv fun l h1 h2 => hz l h1 (by omega)

include hR₂ in
private theorem longWeyl_mem {b : Fin n} (hb : b ≠ Fin.rev b) (z : traceZero σ) :
    longWeyl σ hb z ∈ R := by
  rw [longWeyl_def]
  exact mul_mem (mul_mem (hR₂ _ _ _) (hR₂ _ _ _)) (hR₂ _ _ _)

omit hσ in
private theorem act_longWeyl_single {b : Fin n} (hb : b ≠ Fin.rev b) {z : traceZero σ}
    (hz : (z : F) ≠ 0) (s : Fin n) (c : F) :
    act (longWeyl σ hb z) (Pi.single s c) =
      Pi.single (Equiv.swap b (Fin.rev b) s) (longSign b (z : F) s * c) := by
  rw [act, coe_longWeyl σ hb hz, signedPerm_mulVec_single]

include hR₁ hR₂ hR₃ in
private theorem exists_smul_single_of_ne (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {kk : Fin n} (hkk : 2 * kk.val + 1 < n) {v : Fin n → F}
    (hv : ∀ s, Out kk.val s → v s = 0) (hv' : v (Fin.rev kk) ≠ 0) (hvv : hf σ v v = 0) :
    ∃ r ∈ R, (∀ s, Out kk.val s → act r (Pi.single s 1) = Pi.single s 1) ∧
      ∃ μ, act r v = Pi.single kk μ := by
  have hne : kk ≠ Fin.rev kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
  have hk1 : ¬Out kk.val kk := not_out le_rfl (by omega)
  have hk2 : ¬Out kk.val (Fin.rev kk) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  obtain ⟨r₁, hr₁, hfix, -, hrv⟩ := exists_clear hσ hR₁ hR₂ hR₃ htr hkk n v hv hv' hvv
    fun l _ h2 => by simp only [Fin.val_rev] at h2; omega
  refine ⟨longWeyl σ hne ζ * r₁, mul_mem (longWeyl_mem hR₂ hne ζ) hr₁, fun s hs => ?_,
    (ζ : F) * v (Fin.rev kk), ?_⟩
  · rw [act_mul, hfix s hs, act_longWeyl_single hne hζ,
      Equiv.swap_apply_of_ne_of_ne (ne_of_out hs hk1) (ne_of_out hs hk2)]
    simp [longSign, ne_of_out hs hk1, ne_of_out hs hk2]
  · rw [act_mul, hrv, act_longWeyl_single hne hζ, Equiv.swap_apply_right]
    simp [longSign, Ne.symm hne]

include hR₁ hR₂ hR₃ in
private theorem exists_smul_single (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {kk : Fin n} (hkk : 2 * kk.val + 1 < n) {v : Fin n → F}
    (hv : ∀ s, Out kk.val s → v s = 0) (hvv : hf σ v v = 0) :
    ∃ r ∈ R, (∀ s, Out kk.val s → act r (Pi.single s 1) = Pi.single s 1) ∧
      ∃ μ, act r v = Pi.single kk μ := by
  have hne : kk ≠ Fin.rev kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev]; omega)
  have hk1 : ¬Out kk.val kk := not_out le_rfl (by omega)
  have hk2 : ¬Out kk.val (Fin.rev kk) := not_out (by simp only [Fin.val_rev]; omega)
    (by simp only [Fin.val_rev]; omega)
  by_cases hv' : v (Fin.rev kk) ≠ 0
  · exact exists_smul_single_of_ne hσ hR₁ hR₂ hR₃ htr hζ hkk hv hv' hvv
  push Not at hv'
  by_cases hl : ∃ l : Fin n, kk.val < l.val ∧ l.val < (Fin.rev kk).val ∧ l ≠ Fin.rev l ∧ v l ≠ 0
  · obtain ⟨l, hl1, hl2, hl3, hl4⟩ := hl
    have hkl : Fin.rev kk ≠ l := Fin.ne_of_val_ne (by omega)
    have hk3 : Fin.rev kk ≠ Fin.rev (Fin.rev kk) := rev_ne_rev_rev hne
    have hlk : l ≠ Fin.rev (Fin.rev kk) := by
      rw [Fin.rev_rev]
      exact Fin.ne_of_val_ne (by omega)
    have hl5 : ¬Out kk.val l := not_out (by omega) (by simp only [Fin.val_rev] at hl2; omega)
    have hl6 : ¬Out kk.val (Fin.rev l) := not_out (by simp only [Fin.val_rev] at *; omega)
      (by simp only [Fin.val_rev] at *; omega)
    have hlk' : Fin.rev kk ≠ Fin.rev l := fun h => hl3 (by
      have := Fin.rev_injective h
      exact absurd (this ▸ hl1) (lt_irrefl _))
    set r₀ := rootHom σ hσ hkl hk3 hl3 (Multiplicative.ofAdd 1)
    have hr₀ : r₀ ∈ R := hR₁ _ _ _ _ _ hlk _
    have hv'1 : act r₀ v (Fin.rev kk) = v l := by
      rw [act_rootHom]
      simp [hv', Pi.single_eq_of_ne hlk']
    obtain ⟨r, hr, hfix, μ, hμ⟩ := exists_smul_single_of_ne hσ hR₁ hR₂ hR₃ htr hζ hkk
      (v := act r₀ v) (fun s hs => by
        rw [act_rootHom]
        simp [hv s hs, Pi.single_eq_of_ne (ne_of_out hs hk2),
          Pi.single_eq_of_ne (ne_of_out hs hl6)])
      (by rw [hv'1]; exact hl4) (by rw [hf_act]; exact hvv)
    refine ⟨r * r₀, mul_mem hr hr₀, fun s hs => ?_, μ, by rw [act_mul, hμ]⟩
    rw [act_mul, act_rootHom, Fin.rev_rev, single_one_apply_of_ne (Ne.symm (ne_of_out hs hl5)),
      single_one_apply_of_ne (Ne.symm (ne_of_out hs hk1)), mul_zero, mul_zero, Pi.single_zero,
      Pi.single_zero, add_zero, sub_zero, hfix s hs]
  · push Not at hl
    refine ⟨1, one_mem R, fun s _ => act_one _, v kk, ?_⟩
    rw [act_one]
    have hmid : ∀ p : Fin n, Fin.rev p = p → v p = 0 := by
      intro p hp
      have hp' : p.val = n - 1 - p.val := by
        have := congrArg Fin.val hp
        simp only [Fin.val_rev] at this
        omega
      have hsum : hf σ v v = σ (v p) * v p := by
        rw [hf, Finset.sum_eq_single p (fun i _ hip => ?_) (by simp), hp]
        by_cases hi : Fin.rev i = i
        · exact absurd (Fin.ext (by
            have := congrArg Fin.val hi
            simp only [Fin.val_rev] at this
            omega)) hip
        by_cases hik : i = kk
        · subst hik
          rw [hv', mul_zero]
        by_cases hout : Out kk.val i
        · rw [hv i hout, map_zero, zero_mul]
        by_cases hik' : i = Fin.rev kk
        · subst hik'
          rw [hv', map_zero, zero_mul]
        simp only [Out, Fin.val_rev, not_or, not_lt] at hout
        have hik1 : i.val ≠ kk.val := fun h => hik (Fin.ext h)
        have hik2 : i.val ≠ n - (kk.val + 1) := fun h => hik' (Fin.ext (by
          simp only [Fin.val_rev]; omega))
        rw [hl i (by omega) (by simp only [Fin.val_rev]; omega) (fun h => hi h.symm), map_zero,
          zero_mul]
      rw [hsum] at hvv
      rcases mul_eq_zero.mp hvv with h | h
      · exact (map_eq_zero_iff σ σ.injective).mp h
      · exact h
    funext l
    by_cases hlk : l = kk
    · subst hlk
      simp
    rw [Pi.single_eq_of_ne hlk]
    by_cases hout : Out kk.val l
    · exact hv l hout
    by_cases hlk' : l = Fin.rev kk
    · rw [hlk']
      exact hv'
    by_cases hlm : Fin.rev l = l
    · exact hmid l hlm
    simp only [Out, Fin.val_rev, not_or, not_lt] at hout
    have h1 : l.val ≠ kk.val := fun h => hlk (Fin.ext h)
    have h2 : l.val ≠ n - (kk.val + 1) := fun h => hlk' (Fin.ext (by
      simp only [Fin.val_rev]; omega))
    exact hl l (by omega) (by simp only [Fin.val_rev]; omega) (fun h => hlm h.symm)

end Clear

omit hσ in
private theorem out_rev {k : ℕ} {s : Fin n} : Out k (Fin.rev s) ↔ Out k s := by
  simp only [Out, Fin.rev_rev]
  exact Or.comm

omit hσ in
private theorem act_apply_eq_zero {k : ℕ} {g : SU σ n}
    (hg : ∀ s, Out k s → ∃ μ, act g (Pi.single s 1) = Pi.single s μ) {t : Fin n}
    (ht : ¬Out k t) {s : Fin n} (hs : Out k s) : act g (Pi.single t 1) s = 0 := by
  obtain ⟨μ, hμ⟩ := hg (Fin.rev s) (out_rev.mpr hs)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [Pi.single_zero] at hμ
    exact act_single_ne_zero g _ hμ
  have h := hf_act g (Pi.single (Fin.rev s) 1) (Pi.single t 1)
  rw [hμ, hf_single_left, hf_single_left, Fin.rev_rev, map_one, one_mul,
    Pi.single_eq_of_ne (ne_of_out hs ht)] at h
  exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hμ0)

section Step

variable {R : Subgroup (SU σ n)}
  (hR₁ : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
    j ≠ Fin.rev i → ∀ c, rootHom σ hσ hij hi hj c ∈ R)
  (hR₂ : ∀ (i : Fin n) (hi : i ≠ Fin.rev i) c, longRootHom σ hi c ∈ R)
  (hR₃ : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
    heisenbergSubgroup σ hσ hi hik hk ≤ R)

include hR₁ hR₂ hR₃ in
private theorem exists_step (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {k : ℕ} (hk : 2 * k + 1 < n) (g : SU σ n)
    (hg : ∀ s, Out k s → ∃ μ, act g (Pi.single s 1) = Pi.single s μ) :
    ∃ r ∈ R, ∀ s, Out (k + 1) s → ∃ μ, act (r * g) (Pi.single s 1) = Pi.single s μ := by
  set kk : Fin n := ⟨k, by omega⟩ with hkkdef
  have hkk : 2 * kk.val + 1 < n := hk
  have hk1 : ¬Out k kk := not_out le_rfl (by simp only [kk]; omega)
  have hk2 : ¬Out k (Fin.rev kk) := not_out (by simp only [Fin.val_rev, kk]; omega)
    (by simp only [Fin.val_rev, kk]; omega)
  have hne : Fin.rev kk ≠ kk := Fin.ne_of_val_ne (by simp only [Fin.val_rev, kk]; omega)
  obtain ⟨r₁, hr₁, hfix₁, μ, hμ⟩ := exists_smul_single hσ hR₁ hR₂ hR₃ htr hζ hkk
    (v := act g (Pi.single kk 1)) (fun s hs => act_apply_eq_zero hg hk1 hs)
    (by rw [hf_act, hf_single_left, map_one, one_mul, Pi.single_eq_of_ne hne])
  have hg₁ : ∀ s, Out k s → ∃ μ, act (r₁ * g) (Pi.single s 1) = Pi.single s μ := by
    intro s hs
    obtain ⟨μ', hμ'⟩ := hg s hs
    refine ⟨μ', ?_⟩
    rw [act_mul, hμ', act_single, hfix₁ s hs, ← Pi.single_smul, smul_eq_mul, mul_one]
  set u := act (r₁ * g) (Pi.single (Fin.rev kk) 1)
  have hu : ∀ s, Out k s → u s = 0 := fun s hs => act_apply_eq_zero hg₁ hk2 hs
  have hμk : act (r₁ * g) (Pi.single kk 1) = Pi.single kk μ := by rw [act_mul, hμ]
  have hpair : σ μ * u (Fin.rev kk) = 1 := by
    have h := hf_act (r₁ * g) (Pi.single kk 1) (Pi.single (Fin.rev kk) 1)
    rw [hμk, hf_single_left, hf_single_left, map_one, one_mul, Pi.single_eq_same] at h
    exact h
  have hu' : u (Fin.rev kk) ≠ 0 := fun h => by rw [h, mul_zero] at hpair; exact zero_ne_one hpair
  have huu : hf σ u u = 0 := by
    rw [hf_act, hf_single_left, map_one, one_mul, Fin.rev_rev, Pi.single_eq_of_ne (Ne.symm hne)]
  obtain ⟨r₂, hr₂, hfix₂, hfixk₂, hr₂u⟩ := exists_clear hσ hR₁ hR₂ hR₃ htr hkk n u hu hu' huu
    fun l _ h2 => by simp only [Fin.val_rev] at h2; omega
  refine ⟨r₂ * r₁, mul_mem hr₂ hr₁, fun s hs => ?_⟩
  rw [mul_assoc, act_mul]
  by_cases hsk : Out k s
  · obtain ⟨μ', hμ'⟩ := hg₁ s hsk
    exact ⟨μ', by rw [hμ', act_single, hfix₂ s hsk, ← Pi.single_smul, smul_eq_mul, mul_one]⟩
  · simp only [Out, Fin.val_rev, not_or, not_lt] at hs hsk
    by_cases hs1 : s.val = k
    · have : s = kk := Fin.ext hs1
      subst this
      exact ⟨μ, by rw [hμk, act_single, hfixk₂, ← Pi.single_smul, smul_eq_mul, mul_one]⟩
    · have : s = Fin.rev kk := Fin.ext (by simp only [Fin.val_rev, kk]; omega)
      subst this
      exact ⟨u (Fin.rev kk), hr₂u⟩

include hR₁ hR₂ hR₃ in
private theorem mem_of_out (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) (hdiag : ∀ g : SU σ n,
      (∃ t, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) → g ∈ R) :
    ∀ d k, k + d = n / 2 → ∀ g : SU σ n,
      (∀ s, Out k s → ∃ μ, act g (Pi.single s 1) = Pi.single s μ) → g ∈ R := by
  intro d
  induction d with
  | zero =>
    intro k hk g hg
    simp only [add_zero] at hk
    subst hk
    have hall : ∀ s, ∃ μ, act g (Pi.single s 1) = Pi.single s μ := by
      intro s
      by_cases hs : Out (n / 2) s
      · exact hg s hs
      · refine ⟨act g (Pi.single s 1) s, funext fun r => ?_⟩
        by_cases hrs : r = s
        · subst hrs
          simp
        · rw [Pi.single_eq_of_ne hrs]
          refine act_apply_eq_zero hg hs ?_
          simp only [Out, Fin.val_rev, not_or, not_lt] at hs ⊢
          have : r.val ≠ s.val := fun h => hrs (Fin.ext h)
          omega
    refine hdiag g ⟨fun s => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s s, ?_⟩
    ext r s
    obtain ⟨μ, hμ⟩ := hall s
    have h1 := congrFun hμ r
    have h2 := congrFun hμ s
    simp only [act, mulVec_single_one, col_apply] at h1 h2
    rw [h1, diagonal_apply]
    by_cases hrs : r = s
    · subst hrs
      simp [h2]
    · simp [hrs]
  | succ d ih =>
    intro k hk g hg
    obtain ⟨r, hr, hrg⟩ := exists_step hσ hR₁ hR₂ hR₃ htr hζ (k := k) (by omega) g hg
    have := ih (k + 1) (by omega) (r * g) hrg
    have hg' : g = r⁻¹ * (r * g) := by group
    rw [hg']
    exact mul_mem (inv_mem hr) this

end Step

omit hσ in
theorem unitary_of_coe_eq_diagonal {g : SU σ n} {t : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) (s : Fin n) :
    σ (t s) * t (Fin.rev s) = 1 := by
  obtain ⟨-, hiso⟩ := g.2
  have h := congrFun (congrFun hiso s) (Fin.rev s)
  have h1 : conjTr σ (diagonal t) = diagonal fun s => σ (t s) := by
    rw [conjTr, diagonal_map (map_zero σ), diagonal_transpose]
  rw [hg, h1, mul_diagonal, diagonal_mul] at h
  simpa [antidiag] using h

omit hσ in
private theorem prod_of_diagonal {g : SU σ n} {t : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) : ∏ s, t s = 1 := by
  obtain ⟨hdet, -⟩ := g.2
  rwa [hg, det_diagonal] at hdet

omit hσ in
private theorem coe_mul_of_diagonal {g h : SU σ n} {a b : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal a)
    (hh : ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal b) :
    (((g * h : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (a * b) := by
  rw [Subgroup.coe_mul, Units.val_mul, hg, hh, diagonal_mul_diagonal]
  rfl

omit hσ in
private theorem eq_one_of_diagonal {g : SU σ n} {t : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) (ht : ∀ s, t s = 1) :
    g = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [hg, show t = fun _ => 1 from funext ht, diagonal_one]
  rfl

section Diag

variable {R : Subgroup (SU σ n)}
  (hR₁ : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
    j ≠ Fin.rev i → ∀ c, rootHom σ hσ hij hi hj c ∈ R)
  (hR₂ : ∀ (i : Fin n) (hi : i ≠ Fin.rev i) c, longRootHom σ hi c ∈ R)
  (hR₃ : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
    heisenbergSubgroup σ hσ hi hik hk ≤ R)

include hR₁ in
private theorem shortTorus_mem {a b : Fin n} (hab : a ≠ b) (ha : a ≠ Fin.rev a)
    (hb : b ≠ Fin.rev b) (hba : b ≠ Fin.rev a) (c : F) : shortTorus σ hσ hab ha hb c ∈ R := by
  have hab' : a ≠ Fin.rev b := fun h => hba (by rw [h, Fin.rev_rev])
  have h1 : ∀ c, shortWeyl σ hσ hab ha hb c ∈ R := fun c => by
    rw [shortWeyl_def]
    exact mul_mem (mul_mem (hR₁ _ _ _ _ _ hba _) (hR₁ _ _ _ _ _ hab' _)) (hR₁ _ _ _ _ _ hba _)
  rw [shortTorus_def]
  exact mul_mem (h1 c) (h1 (-1))

include hR₂ in
private theorem longTorus_mem {b : Fin n} (hb : b ≠ Fin.rev b) (ζ : traceZero σ) {e : F}
    (he : σ e = e) : longTorus σ hb ζ he ∈ R := by
  rw [longTorus_def]
  exact mul_mem (longWeyl_mem hR₂ hb _) (longWeyl_mem hR₂ hb _)

include hR₃ in
private theorem exists_heisWeyl {b p : Fin n} (hb : b ≠ Fin.rev b) (hbp : b ≠ p)
    (hp : Fin.rev p = p) {a β : F} (hab : β + σ β + σ a * a = 0) (hβ : β ≠ 0) :
    ∃ N ∈ R, ((N : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      signedPerm (Equiv.swap b (Fin.rev b)) (heisSign σ b p β) := by
  have hb' : Fin.rev b ≠ Fin.rev (Fin.rev b) := rev_ne_rev_rev hb
  have hbp' : Fin.rev b ≠ p := fun h => hbp (by rw [← Fin.rev_rev b, h, hp])
  have hσβ : σ β ≠ 0 := (map_ne_zero σ).mpr hβ
  have h₁ : (σ β)⁻¹ + σ (σ β)⁻¹ + σ (-a * (σ β)⁻¹) * (-a * (σ β)⁻¹) = 0 := by
    simp only [map_mul, map_neg, map_inv₀, hσ]
    field_simp
    linear_combination hab
  have h₂ : (σ β)⁻¹ + σ (σ β)⁻¹ + σ (-a * β⁻¹) * (-a * β⁻¹) = 0 := by
    simp only [map_mul, map_neg, map_inv₀, hσ]
    field_simp
    linear_combination hab
  refine ⟨heisElt hσ hb' hbp' hp _ _ h₁ * heisElt hσ hb hbp hp a β hab *
      heisElt hσ hb' hbp' hp _ _ h₂,
    mul_mem (mul_mem (hR₃ _ _ _ _ _ (heisElt_mem hσ _ _ _ _ _ _))
      (hR₃ _ _ _ _ _ (heisElt_mem hσ _ _ _ _ _ _))) (hR₃ _ _ _ _ _ (heisElt_mem hσ _ _ _ _ _ _)),
    ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact heisenbergMatrix_weyl hσ hb hbp hp hab hβ

include hR₂ hR₃ in
private theorem exists_oddTorus (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) {b p : Fin n} (hb : b ≠ Fin.rev b) (hbp : b ≠ p) (hp : Fin.rev p = p)
    {e : F} (he : e ≠ 0) :
    ∃ x ∈ R, ∃ d : Fin n → F, ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d ∧
      d b = e ∧ d (Fin.rev b) = (σ e)⁻¹ ∧ ∀ s, s ≠ b → s ≠ Fin.rev b → s ≠ p → d s = 1 := by
  have hσζ : σ (ζ : F) = -ζ := by
    have := (mem_traceZero σ).mp ζ.2
    linear_combination this
  have hbp' : Fin.rev b ≠ p := fun h => hbp (by rw [← Fin.rev_rev b, h, hp])
  set β := e * (ζ : F)
  have hβ : β ≠ 0 := mul_ne_zero he hζ
  obtain ⟨a, ha⟩ := hnorm (-(β + σ β)) (by rw [map_neg, map_add, hσ, add_comm])
  have hab : β + σ β + σ a * a = 0 := by rw [ha]; ring
  obtain ⟨N, hN, hNm⟩ := exists_heisWeyl hσ hR₃ hb hbp hp hab hβ
  refine ⟨N * longWeyl σ hb (-ζ), mul_mem hN (longWeyl_mem hR₂ hb _),
    fun s => heisSign σ b p β (Equiv.swap b (Fin.rev b) s) * longSign b (-(ζ : F)) s, ?_, ?_, ?_,
    fun s h1 h2 h3 => ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, hNm, coe_longWeyl σ hb (by simpa using hζ),
      signedPerm_mul_signedPerm, Equiv.swap_mul_self, signedPerm_one]
    rfl
  · simp only [Equiv.swap_apply_left, heisSign, longSign, Ne.symm hb, hbp', ite_true, ite_false,
      β]
    field_simp
  · simp only [Equiv.swap_apply_right, heisSign, longSign, Ne.symm hb, ite_true, ite_false,
      map_mul, hσζ, β]
    field_simp
  · simp only [Equiv.swap_apply_of_ne_of_ne h1 h2, heisSign, longSign, h1, h2, h3, ite_false,
      mul_one]

include hR₁ hR₂ hR₃ in
private theorem diag_mem (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) :
    ∀ d k, k + d + 1 = n / 2 → ∀ (g : SU σ n) (t : Fin n → F),
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t →
      (∀ s : Fin n, s.val < k → t s = 1) → g ∈ R := by
  intro d
  induction d with
  | zero =>
    intro k hk g t hg ht
    have hu := unitary_of_coe_eq_diagonal hg
    have h0 : ∀ s, t s ≠ 0 := ne_zero_of_unitary hu
    set b : Fin n := ⟨k, by omega⟩
    have hb : b ≠ Fin.rev b := Fin.ne_of_val_ne (by simp only [Fin.val_rev, b]; omega)
    have hrest : ∀ s, s ≠ b → s ≠ Fin.rev b → Fin.rev s ≠ s → t s = 1 := by
      intro s h1 h2 h3
      have h1' : s.val ≠ k := fun h => h1 (Fin.ext h)
      have h2' : s.val ≠ n - 1 - k := fun h => h2 (Fin.ext (by simp only [Fin.val_rev, b]; omega))
      have h3' : s.val ≠ n - 1 - s.val := fun h => h3 (Fin.ext (by simp only [Fin.val_rev]; omega))
      by_cases hs : s.val < k
      · exact ht s hs
      · have := hu (Fin.rev s)
        rw [Fin.rev_rev, ht (Fin.rev s) (by simp only [Fin.val_rev]; omega), map_one,
          one_mul] at this
        exact this
    by_cases hev : Even n
    ·
      have hmid : ∀ s : Fin n, Fin.rev s ≠ s := fun s h => by
        have := congrArg Fin.val h
        simp only [Fin.val_rev] at this
        obtain ⟨r, hr⟩ := hev
        omega
      have hprod := prod_of_diagonal hg
      rw [Finset.prod_eq_mul b (Fin.rev b) hb (fun s _ hs => hrest s hs.1 hs.2 (hmid s))
        (by simp) (by simp)] at hprod
      have hσe : σ (t b) = t b := by
        have h1 := hu b
        exact mul_right_cancel₀ (h0 (Fin.rev b)) (h1.trans hprod.symm)
      have hg' : g = longTorus σ hb ζ hσe := by
        refine Subtype.ext (Units.ext ?_)
        rw [hg, coe_longTorus σ hb hζ hσe (h0 b)]
        congr 1
        funext s
        by_cases h1 : s = b
        · subst h1
          simp [longTorusFun]
        by_cases h2 : s = Fin.rev b
        · subst h2
          simp only [longTorusFun, Ne.symm hb, ite_true, ite_false]
          exact eq_inv_of_mul_eq_one_right hprod
        · simp only [longTorusFun, h1, h2, ite_false]
          exact hrest s h1 h2 (hmid s)
      rw [hg']
      exact longTorus_mem hR₂ hb ζ hσe
    ·
      set p : Fin n := ⟨n / 2, by omega⟩
      have hp : Fin.rev p = p := Fin.ext (by
        simp only [Fin.val_rev, p]
        rw [Nat.not_even_iff_odd] at hev
        obtain ⟨r, hr⟩ := hev
        omega)
      have hbp : b ≠ p := Fin.ne_of_val_ne (by simp only [b, p]; omega)
      obtain ⟨x, hx, dx, hxm, hdb, hdb', hd1⟩ := exists_oddTorus hσ hR₂ hR₃ hnorm hζ hb hbp hp
        (inv_ne_zero (h0 b))
      have htb' : t (Fin.rev b) = (σ (t b))⁻¹ := eq_inv_of_mul_eq_one_right (hu b)
      have hg₂ := coe_mul_of_diagonal hxm hg
      have hval : ∀ s, s ≠ p → (dx * t) s = 1 := by
        intro s hs
        by_cases h1 : s = b
        · subst h1
          simp only [Pi.mul_apply, hdb]
          exact inv_mul_cancel₀ (h0 _)
        by_cases h2 : s = Fin.rev b
        · subst h2
          simp only [Pi.mul_apply, hdb', htb', map_inv₀, inv_inv]
          exact mul_inv_cancel₀ ((map_ne_zero σ).mpr (h0 b))
        · rw [Pi.mul_apply, hd1 s h1 h2 hs,
            hrest s h1 h2 (fun h => hs (Fin.ext (by
              have := congrArg Fin.val h
              simp only [Fin.val_rev, p] at this ⊢
              omega))), mul_one]
      have hprod := prod_of_diagonal hg₂
      rw [Finset.prod_eq_single p (fun s _ hs => hval s hs) (by simp)] at hprod
      have hone : x * g = 1 := eq_one_of_diagonal hg₂ fun s => by
        by_cases hs : s = p
        · rw [hs]
          exact hprod
        · exact hval s hs
      have : g = x⁻¹ := eq_inv_of_mul_eq_one_right hone
      rw [this]
      exact inv_mem hx
  | succ d ih =>
    intro k hk g t hg ht
    have hu := unitary_of_coe_eq_diagonal hg
    have h0 : ∀ s, t s ≠ 0 := ne_zero_of_unitary hu
    set a : Fin n := ⟨k, by omega⟩
    set a' : Fin n := ⟨k + 1, by omega⟩
    have haa : a ≠ a' := Fin.ne_of_val_ne (by simp [a, a'])
    have ha : a ≠ Fin.rev a := Fin.ne_of_val_ne (by simp only [Fin.val_rev, a]; omega)
    have ha' : a' ≠ Fin.rev a' := Fin.ne_of_val_ne (by simp only [Fin.val_rev, a']; omega)
    have hba : a' ≠ Fin.rev a := Fin.ne_of_val_ne (by simp only [Fin.val_rev, a, a']; omega)
    set h := shortTorus σ hσ haa ha ha' (t a)⁻¹
    have hhm := coe_shortTorus σ hσ haa ha ha' hba (inv_ne_zero (h0 a))
    have hg₁ := coe_mul_of_diagonal hhm hg
    have hmem := ih (k + 1) (by omega) (h * g) _ hg₁ fun s hs => by
      by_cases hsk : s.val = k
      · have : s = a := Fin.ext hsk
        subst this
        simp [shortTorusFun, inv_mul_cancel₀ (h0 a)]
      · have hs' : s.val < k := by omega
        have e1 : s ≠ a := Fin.ne_of_val_ne (by simp [a]; omega)
        have e2 : s ≠ a' := Fin.ne_of_val_ne (by simp [a']; omega)
        have e3 : s ≠ Fin.rev a := Fin.ne_of_val_ne (by simp only [Fin.val_rev, a]; omega)
        have e4 : s ≠ Fin.rev a' := Fin.ne_of_val_ne (by simp only [Fin.val_rev, a']; omega)
        simp [shortTorusFun, e1, e2, e3, e4, ht s hs']
    have hg' : g = h⁻¹ * (h * g) := by group
    rw [hg']
    exact mul_mem (inv_mem (shortTorus_mem hσ hR₁ haa ha ha' hba _)) hmem

end Diag

theorem eq_top_of_rootElements_le (hσ : ∀ c, σ (σ c) = c)
    (hζ : ∃ ζ : F, ζ ≠ 0 ∧ ζ + σ ζ = 0) (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) (hn : 2 ≤ n) (R : Subgroup (SU σ n))
    (hR₁ : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
      j ≠ Fin.rev i → ∀ c, rootHom σ hσ hij hi hj c ∈ R)
    (hR₂ : ∀ (i : Fin n) (hi : i ≠ Fin.rev i) c, longRootHom σ hi c ∈ R)
    (hR₃ : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
      heisenbergSubgroup σ hσ hi hik hk ≤ R) : R = ⊤ := by
  obtain ⟨z, hz0, hz⟩ := hζ
  refine eq_top_iff.mpr fun g _ => ?_
  refine mem_of_out hσ hR₁ hR₂ hR₃ htr (ζ := ⟨z, hz⟩) hz0 (fun g ⟨t, ht⟩ => ?_) (n / 2) 0
    (by omega) g fun s hs => ?_
  · exact diag_mem hσ hR₁ hR₂ hR₃ hnorm (ζ := ⟨z, hz⟩) hz0 (n / 2 - 1) 0 (by omega) g t ht
      fun s hs => absurd hs (Nat.not_lt_zero _)
  · simp [Out] at hs

end CFSG.LieType.Universal.Unitary
