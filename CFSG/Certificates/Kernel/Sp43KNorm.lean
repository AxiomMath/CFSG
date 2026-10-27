module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Classes
public import CFSG.Certificates.Kernel.Sp43KGrp
public import Certificates.Data.Kernel.Sp43KOrb

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 CFSG.Sp43.Native Subgroup

private theorem shl_lt {y s : ℕ} (hy : y < 2 ^ (16 - s)) (hs : s ≤ 16) : y <<< s < 2 ^ 16 := by
  rw [Nat.shiftLeft_eq]
  calc y * 2 ^ s < 2 ^ (16 - s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hy (by positivity)
    _ = 2 ^ 16 := by rw [← pow_add, Nat.sub_add_cancel hs]

theorem colT_lt (x k : ℕ) : colT x k < 2 ^ 16 := by
  have hy : (x >>> k) &&& 4369 < 2 ^ 13 := Nat.and_lt_two_pow _ (by norm_num)
  unfold colT
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (by omega)
    (shl_lt (by omega) (by norm_num))) (shl_lt (by omega) (by norm_num)))
    (shl_lt (by omega) (by norm_num))

private theorem and_lt_l {x y : ℕ} (hx : x < 2 ^ 16) : x &&& y < 2 ^ 16 := by
  rw [Nat.and_comm]
  exact Nat.and_lt_two_pow _ hx

theorem mul3_lt {ap am bp bm : ℕ} (ha : ap < 2 ^ 16) (hm : am < 2 ^ 16) :
    mul3P ap am bp bm < 2 ^ 16 ∧ mul3M ap am bp bm < 2 ^ 16 :=
  ⟨Nat.or_lt_two_pow (and_lt_l ha) (and_lt_l hm), Nat.or_lt_two_pow (and_lt_l ha) (and_lt_l hm)⟩

theorem add3_lt {ap am bp bm : ℕ} (ha : ap < 2 ^ 16) (hm : am < 2 ^ 16) (hb : bp < 2 ^ 16)
    (hbm : bm < 2 ^ 16) : add3P ap am bp bm < 2 ^ 16 ∧ add3M ap am bp bm < 2 ^ 16 :=
  ⟨Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ hb) (and_lt_l ha)) (and_lt_l hm),
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ hbm) (and_lt_l hm))
      (and_lt_l ha)⟩

theorem term_lt (a b k : ℕ) : termP a b k < 2 ^ 16 ∧ termM a b k < 2 ^ 16 :=
  mul3_lt (colT_lt _ _) (colT_lt _ _)

theorem mulT_lt (a b : ℕ) : mulT a b < 2 ^ 32 := by
  obtain ⟨p0, m0⟩ := term_lt a b 0
  obtain ⟨p1, m1⟩ := term_lt a b 1
  obtain ⟨p2, m2⟩ := term_lt a b 2
  obtain ⟨p3, m3⟩ := term_lt a b 3
  obtain ⟨q1, n1⟩ := add3_lt p0 m0 p1 m1
  obtain ⟨q2, n2⟩ := add3_lt q1 n1 p2 m2
  obtain ⟨-, n3⟩ := add3_lt q2 n2 p3 m3
  have h3 : s3M a b < 2 ^ 16 := n3
  unfold mulT
  refine Nat.or_lt_two_pow (lt_of_lt_of_le (Nat.and_lt_two_pow _ (by decide : laneT < 2 ^ 16))
    (by norm_num)) ?_
  rw [Nat.shiftLeft_eq]
  calc s3M a b * 2 ^ 16 < 2 ^ 16 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
    _ = 2 ^ 32 := by norm_num

theorem okT_of {c : ℕ} (he : ExT c) (hc : c < 2 ^ 32) : okT c = true := by
  simp only [okT, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro n
    simp only [Nat.testBit_and, Nat.zero_testBit, testBit_high]
    rcases lt_or_ge n 16 with h | h
    · have := he n h
      revert this
      cases c.testBit n <;> cases c.testBit (n + 16) <;> simp
    · have : laneT.testBit n = false := by
        have e : laneT = 2 ^ 16 - 1 := rfl
        rw [e, Nat.testBit_two_pow_sub_one]
        simpa using h
      rw [this, Bool.and_false]
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hc

theorem okT_mulT {a b : ℕ} (ha : ExT a) (hb : ExT b) : okT (mulT a b) = true :=
  okT_of (exT_mulT ha hb) (mulT_lt a b)

theorem okT_conjT {n n' c : ℕ} (hn : InG n) (hn' : InG n') (hc : InG c) :
    okT (conjT n n' c) = true :=
  okT_mulT (exT_mulT hn.1 hc.1) hn'.1

theorem ofT_eq_ofCode {c : ℕ} (hc : InG c) : ofT c = ofCode (toCT c) := by
  have hs : Symp (toCT c) := by
    unfold Symp
    rw [← toMT_eq_toM]
    exact hc.2
  apply Subtype.ext
  rw [coe_ofT hc, coe_ofCode hs, toMT_eq_toM]

theorem act_ofT {c : ℕ} (hc : InG c) (v : ℕ) : act (ofT c) (toV v) = toV (vecC (toCT c) v) := by
  have hs : Symp (toCT c) := by
    unfold Symp
    rw [← toMT_eq_toM]
    exact hc.2
  rw [ofT_eq_ofCode hc, act_ofCode hs]

theorem noEig_spec {c : ℕ} (hc : InG c) (h : noEigOK (toCT c) = true)
    {w : Fin 2 ⊕ Fin 2 → ZMod 3} (hw : w ≠ 0) : act (ofT c) w ≠ w ∧ act (ofT c) w ≠ -w := by
  have hk : toV (encV w) = w := toV_encV w
  have hk0 : encV w ≠ 0 := fun h0 => hw (by rw [← hk, h0, toV_zero])
  have hk81 : encV w < 81 := encV_lt w
  unfold noEigOK at h
  rw [List.all_eq_true] at h
  have := h (encV w - 1) (List.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel (by omega)] at this
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨h1, h2⟩ := this
  have hv : toV (vecC (toCT c) (encV w)) = act (ofT c) w := by rw [← act_ofT hc, hk]
  refine ⟨fun e => h1 (eq_of_toV_eq (vecC_lt _ _) hk81 (by rw [hv, e, hk])), fun e => h2
    (eq_of_toV_eq (vecC_lt _ _) (negV_lt _) (by rw [hv, e, toV_negV, hk]))⟩

theorem mem_inf_of {D₀ : Sylow 5 G} {P₀ : Sylow 3 G} {e : Fin 2 ⊕ Fin 2 → ZMod 3} {m : G}
    (he : e ≠ 0) (hm : m ∈ center G) (hP : ∀ y ∈ (P₀ : Subgroup G), act y e = e)
    (hfix : ∀ w, (∀ y ∈ (P₀ : Subgroup G), act y w = w) → w = 0 ∨ w = e ∨ w = -e)
    (hN : ∀ x ∈ normalizer ((D₀ : Subgroup G) : Set G),
      x = 1 ∨ x = m ∨ ∀ w ≠ 0, act x w ≠ w ∧ act x w ≠ -w)
    (D : Sylow 5 G) (P : Sylow 3 G) {x : G}
    (hxD : x ∈ normalizer (D : Set G)) (hxP : x ∈ normalizer (P : Set G)) : x = 1 ∨ x = m := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G D₀ D
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G P₀ P
  have hxP' : ∀ y, y ∈ ((h • P₀ : Sylow 3 G) : Subgroup G) ↔
      x * y * x⁻¹ ∈ ((h • P₀ : Sylow 3 G) : Subgroup G) :=
    Subgroup.mem_normalizer_iff.1 hxP
  have hxD' : ∀ y, y ∈ ((g • D₀ : Sylow 5 G) : Subgroup G) ↔
      x * y * x⁻¹ ∈ ((g • D₀ : Sylow 5 G) : Subgroup G) :=
    Subgroup.mem_normalizer_iff.1 hxD
  have hu : ∀ y ∈ (P₀ : Subgroup G), act y (act h⁻¹ (act x (act h e))) = act h⁻¹ (act x (act h e)) := by
    intro y hy
    have hy' : h * y * h⁻¹ ∈ ((h • P₀ : Sylow 3 G) : Subgroup G) := by
      rw [mem_smul_sylow_iff]
      have e' : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e']
      exact hy
    have hy'' : x⁻¹ * (h * y * h⁻¹) * x ∈ ((h • P₀ : Sylow 3 G) : Subgroup G) := by
      rw [hxP']
      have e' : x * (x⁻¹ * (h * y * h⁻¹) * x) * x⁻¹ = h * y * h⁻¹ := by group
      rw [e']
      exact hy'
    have hz := (mem_smul_sylow_iff h P₀ _).1 hy''
    have e' : y * h⁻¹ * x * h = h⁻¹ * x * h * (h⁻¹ * (x⁻¹ * (h * y * h⁻¹) * x) * h) := by group
    rw [← act_mul y h⁻¹, ← act_mul (y * h⁻¹) x, ← act_mul (y * h⁻¹ * x) h, e',
      act_mul (h⁻¹ * x * h), hP _ hz, act_mul (h⁻¹ * x) h, act_mul h⁻¹ x]
  have hxv : act x (act h e) = act h e ∨ act x (act h e) = -act h e := by
    have hback : act x (act h e) = act h (act h⁻¹ (act x (act h e))) := (act_act_inv h _).symm
    rcases hfix _ hu with h0 | hpos | hneg
    · exact absurd (eq_zero_of_act_eq_zero (eq_zero_of_act_eq_zero (eq_zero_of_act_eq_zero h0)))
        he
    · left
      rw [hback, hpos]
    · right
      rw [hback, hneg, act_neg]
  have hcN : g⁻¹ * x * g ∈ normalizer ((D₀ : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro y hy
    have h1 : g * y * g⁻¹ ∈ ((g • D₀ : Sylow 5 G) : Subgroup G) := by
      rw [mem_smul_sylow_iff]
      have e' : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e']
      exact hy
    have h2 := (mem_smul_sylow_iff g D₀ _).1 ((hxD' (g * y * g⁻¹)).1 h1)
    have e' : g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g := by
      group
    rw [e']
    exact h2
  have hw0 : act g⁻¹ (act h e) ≠ 0 := fun h0 =>
    he (eq_zero_of_act_eq_zero (eq_zero_of_act_eq_zero h0))
  have ee : act (g⁻¹ * x * g) (act g⁻¹ (act h e)) = act g⁻¹ (act x (act h e)) := by
    rw [act_mul (g⁻¹ * x) g, act_mul g⁻¹ x, act_act_inv]
  have hx : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rcases hN _ hcN with h1 | h1 | h1
  · left
    rw [hx, h1, mul_one, mul_inv_cancel]
  · right
    rw [hx, h1, (Subgroup.mem_center_iff.1 hm) g, mul_assoc, mul_inv_cancel, mul_one]
  · obtain ⟨n1, n2⟩ := h1 _ hw0
    rcases hxv with h2 | h2
    · exact absurd (by rw [ee, h2]) n1
    · exact absurd (by rw [ee, h2, act_neg]) n2

theorem card_inf_le_of {m : G} (h : ∀ (D : Sylow 5 G) (P : Sylow 3 G) (x : G),
    x ∈ normalizer (D : Set G) → x ∈ normalizer (P : Set G) → x = 1 ∨ x = m)
    (D : Sylow 5 G) (P : Sylow 3 G) :
    Nat.card ↥(normalizer (D : Set G) ⊓ normalizer (P : Set G)) ≤ 2 := by
  have hsub : ((normalizer (D : Set G) ⊓ normalizer (P : Set G) : Subgroup G) : Set G) ⊆
      {1, m} := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hx
    rcases h D P x hx.1 hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc Nat.card ↥(normalizer (D : Set G) ⊓ normalizer (P : Set G))
      = ((normalizer (D : Set G) ⊓ normalizer (P : Set G) : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, m} : Set G).ncard := Set.ncard_le_ncard hsub
    _ ≤ ({m} : Set G).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

end CFSG.KC.Sp43K

end
