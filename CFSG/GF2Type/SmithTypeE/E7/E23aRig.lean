module

public import CFSG.GF2Type.SmithTypeE.DMod.TD6
public import Certificates.Certificate38801

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.GF2Type.SmithTypeE.DMod CFSG.SmithD6

theorem xor_two_pow_lt_of_le {c k : ℕ} (hc : c < 2 ^ (k + 1)) (hk : 2 ^ k ≤ c) :
    c ^^^ 2 ^ k < 2 ^ k := by
  have hbit : c.testBit k = true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hk hc
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Nat.testBit_xor]
  by_cases hkj : k = j
  · subst hkj
    simp [hbit]
  · have hlt : k < j := by omega
    have hcj : c.testBit j = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hc (Nat.pow_le_pow_right Nat.two_pos (by omega : k + 1 ≤ j)))
    simp [hcj, Nat.testBit_two_pow_of_ne hkj]

theorem apply_dec12_aux_lt (x : V12 →ₗ[ZMod 2] V12)
    (h : ∀ i < 12, x (dec12 (2 ^ i)) = dec12 (2 ^ i)) (n : ℕ) :
    n ≤ 12 → ∀ c, c < 2 ^ n → x (dec12 c) = dec12 c := by
  induction n with
  | zero =>
    intro _ c hc
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    rw [dec12_zero, map_zero]
  | succ k ih =>
    intro hk c hc
    by_cases hlt : c < 2 ^ k
    · exact ih (by omega) c hlt
    · have hk' : 2 ^ k ≤ c := by omega
      have hd : c ^^^ 2 ^ k < 2 ^ k := xor_two_pow_lt_of_le hc hk'
      have hcd : c = (c ^^^ 2 ^ k) ^^^ 2 ^ k := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have key : dec12 c = dec12 (c ^^^ 2 ^ k) + dec12 (2 ^ k) := by
        rw [← dec12_xor]
        exact congrArg dec12 hcd
      have h1 : x (dec12 (c ^^^ 2 ^ k)) = dec12 (c ^^^ 2 ^ k) := ih (by omega) _ hd
      have h2 : x (dec12 (2 ^ k)) = dec12 (2 ^ k) := h k (by omega)
      rw [key, map_add, h1, h2]

theorem apply_dec12_of_fix_basis (x : V12 →ₗ[ZMod 2] V12)
    (h : ∀ i < 12, x (dec12 (2 ^ i)) = dec12 (2 ^ i)) (c : ℕ) (hc : c < 4096) :
    x (dec12 c) = dec12 c := by
  exact apply_dec12_aux_lt x h 12 le_rfl c (lt_of_lt_of_eq hc (by norm_num))

theorem eq_one_of_fix_basis (x : V12 ≃ₗ[ZMod 2] V12)
    (h : ∀ i < 12, x (dec12 (2 ^ i)) = dec12 (2 ^ i)) : x = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨c, hc, rfl⟩ := dec12_surj v
  exact apply_dec12_of_fix_basis (x : V12 →ₗ[ZMod 2] V12) h c hc


theorem ea7RigCheck_holds : ea7ChkRig = true := Certificates.certificate38801

theorem ea7_inF0_lt {p : ℕ} (h : ea7InF0 p = true) : p < 365211 := by
  unfold ea7InF0 ea7InX at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem ea7_triple_lt {k y : ℕ} (hk : k < 365211) (hy : y ∈ ea7Triple k) : y < 4096 := by
  obtain ⟨-, h1, h2, h3, -⟩ := lineFacts.entry k hk
  simp only [ea7Triple, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
  omega

theorem ea7_mem_lineSet {k c : ℕ} (h : c ∈ ea7Triple k) : dec12 c ∈ lineSet k := by
  rw [lineSet_eq]
  simp only [ea7Triple, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem ea7_exists_of_mem_lineSet {k : ℕ} {v : V12} (h : v ∈ lineSet k) :
    ∃ y, y ∈ ea7Triple k ∧ dec12 y = v := by
  rw [lineSet_eq] at h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact ⟨(linePair k).1, by simp [ea7Triple], rfl⟩
  rcases Finset.mem_insert.mp h with rfl | h
  · exact ⟨(linePair k).2, by simp [ea7Triple], rfl⟩
  rcases Finset.mem_singleton.mp h with rfl
  exact ⟨(linePair k).1 ^^^ (linePair k).2, by simp [ea7Triple], rfl⟩

theorem ea7_fix_triple (x : V12 ≃ₗ[ZMod 2] V12) {a b c : ℕ} (ha : a < 365211) (hb : b < 365211)
    (hxa : ∀ v : V12, v ∈ lineSet a → x v ∈ lineSet a)
    (hxb : ∀ v : V12, v ∈ lineSet b → x v ∈ lineSet b)
    (hca : c ∈ ea7Triple a) (hcb : c ∈ ea7Triple b)
    (hint : ∀ y ∈ ea7Triple a, y ∈ ea7Triple b → y = c) :
    x (dec12 c) = dec12 c := by
  obtain ⟨y, hy, hxy⟩ := ea7_exists_of_mem_lineSet (hxa (dec12 c) (ea7_mem_lineSet hca))
  obtain ⟨z, hz, hxz⟩ := ea7_exists_of_mem_lineSet (hxb (dec12 c) (ea7_mem_lineSet hcb))
  have hyz : y = z :=
    eq_of_dec12_eq (ea7_triple_lt ha hy) (ea7_triple_lt hb hz) (hxy.trans hxz.symm)
  have hyb : y ∈ ea7Triple b := by
    rw [hyz]
    exact hz
  rw [← hxy, hint y hy hyb]

theorem ea7_fixed_line_mem (x : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) {k : ℕ} (hk : k < 365211)
    (hp : omegaToPerm x ⟨k, hk⟩ = ⟨k, hk⟩) :
    ∀ v : V12, v ∈ lineSet k → (x : V12 ≃ₗ[ZMod 2] V12) v ∈ lineSet k := by
  intro v hv
  have h1 : actPerm ⟨(x : V12 ≃ₗ[ZMod 2] V12), omegaPlus_le_iso x.2⟩ ⟨k, hk⟩ = ⟨k, hk⟩ := by
    rw [← omegaToPerm_apply x]
    exact hp
  have h2 : lineSet k = Finset.map (x : V12 ≃ₗ[ZMod 2] V12).toEquiv.toEmbedding (lineSet k) := by
    have h := lineSet_actPerm ⟨(x : V12 ≃ₗ[ZMod 2] V12), omegaPlus_le_iso x.2⟩ ⟨k, hk⟩
    rw [h1] at h
    exact h
  have h3 : (x : V12 ≃ₗ[ZMod 2] V12) v ∈
      Finset.map (x : V12 ≃ₗ[ZMod 2] V12).toEquiv.toEmbedding (lineSet k) :=
    Finset.mem_map.mpr ⟨v, hv, rfl⟩
  rw [← h2] at h3
  exact h3

theorem ea7_basis_fix (x : ↥(CFSG.Open.timmesfeldOmegaPlus 6))
    (hF : ∀ p : Fin 365211, ea7InF0 p.val = true → omegaToPerm x p = p) (i : ℕ) (hi : i < 12) :
    (x : V12 ≃ₗ[ZMod 2] V12) (dec12 (2 ^ i)) = dec12 (2 ^ i) := by
  have hr := ea7RigCheck_holds
  rw [ea7ChkRig, Bool.and_eq_true] at hr
  obtain ⟨h12, hall⟩ := hr
  obtain ⟨t, ht, hti⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp h12 i (List.mem_range.mpr hi))
  have hc : t.1 = 2 ^ i := beq_iff_eq.mp hti
  have hta := List.all_eq_true.mp hall t ht
  simp only [Bool.and_eq_true] at hta
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := hta
  have ha : t.2.1 < 365211 := ea7_inF0_lt hA
  have hb : t.2.2 < 365211 := ea7_inF0_lt hB
  have hint : ∀ y ∈ ea7Triple t.2.1, y ∈ ea7Triple t.2.2 → y = t.1 := by
    intro y hy hyb
    have h1 := List.all_eq_true.mp hE y hy
    have h2 : (ea7Triple t.2.2).contains y = true := List.elem_eq_true_of_mem hyb
    rw [h2] at h1
    simpa using h1
  rw [← hc]
  exact ea7_fix_triple (x : V12 ≃ₗ[ZMod 2] V12) ha hb
    (ea7_fixed_line_mem x ha (hF ⟨t.2.1, ha⟩ hA))
    (ea7_fixed_line_mem x hb (hF ⟨t.2.2, hb⟩ hB))
    (List.contains_iff_mem.mp hC) (List.contains_iff_mem.mp hD) hint

theorem eq_one_of_fixes_F0 {g : Equiv.Perm (Fin 365211)} (hg : g ∈ TD6)
    (hF : ∀ p : Fin 365211, ea7InF0 p.val = true → g p = p) : g = 1 := by
  obtain ⟨x, rfl⟩ := exists_omega_of_mem_TD6 hg
  have hx : (x : V12 ≃ₗ[ZMod 2] V12) = 1 :=
    eq_one_of_fix_basis (x : V12 ≃ₗ[ZMod 2] V12) fun i hi => ea7_basis_fix x hF i hi
  have hx' : x = 1 := Subtype.ext hx
  rw [hx', map_one]

end CFSG.GF2Type.SmithTypeE.E7
