module

public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram

public section

namespace CFSG.Semidihedral.Principal

namespace SevenIrreducibles

variable {L : Type*} [DecidableEq L]

theorem sum_ind_mul (S : Finset L) (v : L → ℤ) {A : L} (hA : A ∈ S) :
    ∑ x ∈ S, (if x = A then (1 : ℤ) else 0) * v x = v A := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hA, ite_true]

theorem sum_diff_mul (S : Finset L) (a v : L → ℤ) {A B : L} (hA : A ∈ S) (hB : B ∈ S)
    (s : ℤ) (ha : ∀ x ∈ S, a x = s * ((if x = A then 1 else 0) - (if x = B then 1 else 0))) :
    ∑ x ∈ S, a x * v x = s * (v A - v B) := by
  rw [Finset.sum_congr rfl fun x hx => by rw [ha x hx]]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
    sum_ind_mul S v hA, sum_ind_mul S v hB]

theorem sum_principal_diff_mul (S : Finset L) (a v : L → ℤ) {p A B : L} (hp : p ∈ S)
    (hA : A ∈ S) (hB : B ∈ S) (s : ℤ)
    (ha : ∀ x ∈ S, a x = (if x = p then 1 else 0) +
      s * ((if x = A then 1 else 0) - (if x = B then 1 else 0))) :
    ∑ x ∈ S, a x * v x = v p + s * (v A - v B) := by
  rw [Finset.sum_congr rfl fun x hx => by rw [ha x hx]]
  simp only [add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum, sum_ind_mul S v hp, sum_ind_mul S v hA, sum_ind_mul S v hB]

theorem sum_three_mul (S : Finset L) (a v : L → ℤ) {A B C : L} (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) (s t u : ℤ)
    (ha : ∀ x ∈ S, a x = s * (if x = A then 1 else 0) + t * (if x = B then 1 else 0) +
      u * (if x = C then 1 else 0)) :
    ∑ x ∈ S, a x * v x = s * v A + t * v B + u * v C := by
  rw [Finset.sum_congr rfl fun x hx => by rw [ha x hx]]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, sum_ind_mul S v hA,
    sum_ind_mul S v hB, sum_ind_mul S v hC]

theorem diff_normalize (S : Finset L) (a : L → ℤ) {E F : L} (hEF : E ≠ F) (hE : E ∈ S)
    (hF : F ∈ S) (ha : ∀ x ∈ S, a x = (if x = E then 1 else 0) - (if x = F then 1 else 0))
    {c : L} (hc : c ∈ S) {s : ℤ} (hs : s = 1 ∨ s = -1) (hac : a c = s) :
    ∃ D ∈ S, D ≠ c ∧ a D = -s ∧
      ∀ x ∈ S, a x = s * ((if x = c then 1 else 0) - (if x = D then 1 else 0)) := by
  by_cases hcE : c = E
  · subst hcE
    have hs1 : s = 1 := by
      rw [← hac, ha c hc]
      simp [hEF]
    refine ⟨F, hF, Ne.symm hEF, ?_, fun x hx => by rw [ha x hx, hs1]; ring⟩
    rw [ha F hF, hs1]
    simp [Ne.symm hEF]
  · by_cases hcF : c = F
    · subst hcF
      have hs1 : s = -1 := by
        rw [← hac, ha c hc]
        simp [hcE]
      refine ⟨E, hE, hEF, ?_, fun x hx => by rw [ha x hx, hs1]; ring⟩
      rw [ha E hE, hs1]
      simp [hEF]
    · exfalso
      rw [ha c hc] at hac
      simp only [hcE, hcF, ite_false, sub_self] at hac
      rcases hs with h | h <;> omega

theorem principal_norm_three_shape (S : Finset L) {p : L} (hp : p ∈ S) (deg : L → ℤ)
    (hdeg : ∀ x ∈ S, 0 < deg x) (hdegp : deg p = 1) (b : L → ℤ) (hbp : b p = 1)
    (hnorm : ∑ x ∈ S, b x * b x = 3) (hdegree : ∑ x ∈ S, b x * deg x = 0) :
    ∃ A ∈ S, ∃ B ∈ S, A ≠ p ∧ B ≠ p ∧ A ≠ B ∧ deg B = deg A + 1 ∧
      ∀ x ∈ S, b x = (if x = p then 1 else 0) +
        1 * ((if x = A then 1 else 0) - (if x = B then 1 else 0)) := by
  obtain ⟨N, hNS, hNcard, hNsign, hNout⟩ :=
    principal_small_norm_support S hp b hbp (n := 2) (by norm_num) (by rw [hnorm]; norm_num)
  obtain ⟨m₁, m₂, hm, rfl⟩ := Finset.card_eq_two.mp hNcard
  have hm₁ : m₁ ∈ S.erase p := hNS (by simp)
  have hm₂ : m₂ ∈ S.erase p := hNS (by simp)
  have hm₁S := Finset.mem_of_mem_erase hm₁
  have hm₂S := Finset.mem_of_mem_erase hm₂
  have hm₁p := Finset.ne_of_mem_erase hm₁
  have hm₂p := Finset.ne_of_mem_erase hm₂
  have hform : ∀ x ∈ S, b x = 1 * (if x = p then 1 else 0) + b m₁ * (if x = m₁ then 1 else 0) +
      b m₂ * (if x = m₂ then 1 else 0) := by
    intro x hx
    by_cases hxp : x = p
    · subst hxp
      simp [hbp, Ne.symm hm₁p, Ne.symm hm₂p]
    by_cases hx₁ : x = m₁
    · subst hx₁
      simp [hxp, hm]
    by_cases hx₂ : x = m₂
    · subst hx₂
      simp [hxp, hx₁]
    · rw [hNout x hx hxp (by simp [hx₁, hx₂])]
      simp [hxp, hx₁, hx₂]
  have hdeg₂ := sum_three_mul S b deg hp hm₁S hm₂S 1 (b m₁) (b m₂) hform
  rw [hdegree, hdegp] at hdeg₂
  have hd₁ := hdeg m₁ hm₁S
  have hd₂ := hdeg m₂ hm₂S
  rcases hNsign m₁ (by simp) with h₁ | h₁ <;> rcases hNsign m₂ (by simp) with h₂ | h₂
  · rw [h₁, h₂] at hdeg₂
    linarith
  · refine ⟨m₁, hm₁S, m₂, hm₂S, hm₁p, hm₂p, hm, by rw [h₁, h₂] at hdeg₂; linarith,
      fun x hx => ?_⟩
    rw [hform x hx, h₁, h₂]
    ring
  · refine ⟨m₂, hm₂S, m₁, hm₁S, hm₂p, hm₁p, Ne.symm hm, by rw [h₁, h₂] at hdeg₂; linarith,
      fun x hx => ?_⟩
    rw [hform x hx, h₁, h₂]
    ring
  · rw [h₁, h₂] at hdeg₂
    linarith

theorem norm_two_shape (S : Finset L) {p : L} (deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x)
    (b : L → ℤ) (hbp : b p = 0) (hnorm : ∑ x ∈ S, b x * b x = 2)
    (hdegree : ∑ x ∈ S, b x * deg x = 0) :
    ∃ E ∈ S, ∃ F ∈ S, E ≠ p ∧ F ≠ p ∧ E ≠ F ∧ deg E = deg F ∧
      ∀ x ∈ S, b x = (if x = E then 1 else 0) - (if x = F then 1 else 0) := by
  obtain ⟨E, hE, F, hF, hEF, hdEF, hform⟩ :=
    degree_zero_norm_two_coordinates S deg hdeg b hnorm hdegree
  refine ⟨E, hE, F, hF, fun h => ?_, fun h => ?_, hEF, hdEF, hform⟩
  · have hpF : p ≠ F := h ▸ hEF
    have := hform E hE
    rw [h, hbp] at this
    simp [hpF] at this
  · have hpE : p ≠ E := fun h' => hEF (h'.symm.trans h.symm)
    have := hform F hF
    rw [h, hbp] at this
    simp [hpE] at this

theorem eq_of_card_three {N : Finset L} (hN : N.card = 3) {a b c : L} (ha : a ∈ N) (hb : b ∈ N)
    (hc : c ∈ N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : N = {a, b, c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [hN, Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_pair hbc]

theorem exists_third_of_card_three {N : Finset L} (hN : N.card = 3) {a b : L} (ha : a ∈ N)
    (hb : b ∈ N) (hab : a ≠ b) : ∃ c ∈ N, c ≠ a ∧ c ≠ b ∧ N = {a, b, c} := by
  have hcard : ((N.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
      Finset.card_erase_of_mem ha, hN]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have hcmem : c ∈ (N.erase a).erase b := hc ▸ Finset.mem_singleton_self c
  have hcb : c ≠ b := Finset.ne_of_mem_erase hcmem
  have hca : c ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcmem)
  have hcN : c ∈ N := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcmem)
  exact ⟨c, hcN, hca, hcb, eq_of_card_three hN ha hb hcN hab (Ne.symm hca) (Ne.symm hcb)⟩

theorem form_of_support_three (S : Finset L) (f : L → ℤ) {a b c : L} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hout : ∀ x ∈ S, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    ∀ x ∈ S, f x = f a * (if x = a then 1 else 0) + f b * (if x = b then 1 else 0) +
      f c * (if x = c then 1 else 0) := by
  intro x hx
  by_cases hxa : x = a
  · subst hxa
    simp [hab, hac]
  by_cases hxb : x = b
  · subst hxb
    simp [hxa, hbc]
  by_cases hxc : x = c
  · subst hxc
    simp [hxa, hxb]
  · simp [hxa, hxb, hxc, hout x hx hxa hxb hxc]

theorem sign_of_ne_zero {z : ℤ} (h : z = -1 ∨ z = 0 ∨ z = 1) (hz : z ≠ 0) : z = 1 ∨ z = -1 := by
  omega

theorem three_label_degree_ne_zero (S : Finset L) (f deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x)
    {N : Finset L} (hNS : N ⊆ S) (hout : ∀ x ∈ S, x ∉ N → f x = 0) {a b c : L} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hNeq : N = {a, b, c}) (hfb : f b = f a) (hfc : f c = f a)
    (hfa : f a ≠ 0) : ∑ x ∈ S, f x * deg x ≠ 0 := by
  have ha : a ∈ S := hNS (by simp [hNeq])
  have hb : b ∈ S := hNS (by simp [hNeq])
  have hc : c ∈ S := hNS (by simp [hNeq])
  have hsum : ∑ x ∈ S, f x * deg x = ∑ x ∈ N, f x * deg x :=
    (Finset.sum_subset hNS fun x hx hxN => by rw [hout x hx hxN, zero_mul]).symm
  rw [hsum, hNeq, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, hfb, hfc]
  have hpos : 0 < deg a + deg b + deg c := by
    have := hdeg a ha
    have := hdeg b hb
    have := hdeg c hc
    omega
  intro h
  have h' : f a * (deg a + deg b + deg c) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact hfa h''
  · omega

theorem third_support_point (S : Finset L) (f : L → ℤ) {N : Finset L} (hNS : N ⊆ S)
    (hNcard : N.card = 3) (hNsign : ∀ x ∈ N, f x = 1 ∨ f x = -1)
    (hNout : ∀ x ∈ S, x ∉ N → f x = 0) {c y : L} (hcN : c ∈ N) (hyN : y ∈ N) (hyc : y ≠ c) :
    ∃ z ∈ S, z ≠ c ∧ z ≠ y ∧ (f z = 1 ∨ f z = -1) ∧
      ∀ x ∈ S, f x = f c * (if x = c then 1 else 0) + f y * (if x = y then 1 else 0) +
        f z * (if x = z then 1 else 0) := by
  obtain ⟨z, hzN, hzc, hzy, hNeq⟩ := exists_third_of_card_three hNcard hcN hyN (Ne.symm hyc)
  refine ⟨z, hNS hzN, hzc, hzy, hNsign z hzN, form_of_support_three S f (Ne.symm hyc)
    (Ne.symm hzc) (Ne.symm hzy) fun x hx h₁ h₂ h₃ => hNout x hx ?_⟩
  rw [hNeq]
  simp [h₁, h₂, h₃]

theorem shapes_of_first_two (S : Finset L) {p : L} (hp : p ∈ S) (deg : L → ℤ)
    (hdeg : ∀ x ∈ S, 0 < deg x) (b₁ b₂ b₃ b₄ b₅ : L → ℤ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {c₁ c₂ c₃ : L} (hc₁ : c₁ ∈ S) (hc₂ : c₂ ∈ S) (hc₃ : c₃ ∈ S) (h12 : c₁ ≠ c₂) (h13 : c₁ ≠ c₃)
    (h23 : c₂ ≠ c₃)
    (hb₁ : ∀ x ∈ S, b₁ x = (if x = p then 1 else 0) +
      ε * ((if x = c₁ then 1 else 0) - (if x = c₂ then 1 else 0)))
    (hb₂ : ∀ x ∈ S, b₂ x = ε * ((if x = c₁ then 1 else 0) - (if x = c₃ then 1 else 0)))
    (hp₃ : b₃ p = 0) (hp₄ : b₄ p = 0) (hp₅ : b₅ p = 0)
    (hd₃ : ∑ x ∈ S, b₃ x * deg x = 0) (hd₄ : ∑ x ∈ S, b₄ x * deg x = 0)
    (hd₅ : ∑ x ∈ S, b₅ x * deg x = 0)
    (g13 : ∑ x ∈ S, b₁ x * b₃ x = 0) (g14 : ∑ x ∈ S, b₁ x * b₄ x = -1)
    (g15 : ∑ x ∈ S, b₁ x * b₅ x = 1) (g23 : ∑ x ∈ S, b₂ x * b₃ x = -1)
    (g24 : ∑ x ∈ S, b₂ x * b₄ x = 0) (g25 : ∑ x ∈ S, b₂ x * b₅ x = 1)
    (g33 : ∑ x ∈ S, b₃ x * b₃ x = 2) (g34 : ∑ x ∈ S, b₃ x * b₄ x = 0)
    (g35 : ∑ x ∈ S, b₃ x * b₅ x = 0) (g44 : ∑ x ∈ S, b₄ x * b₄ x = 3)
    (g45 : ∑ x ∈ S, b₄ x * b₅ x = 1) (g55 : ∑ x ∈ S, b₅ x * b₅ x = 3) :
    ∃ c₄ c₅ c₆ c₇ : L, ∃ ε₁ ε₂ ε₃ : ℤ, c₄ ∈ S ∧ c₅ ∈ S ∧ c₆ ∈ S ∧ c₇ ∈ S ∧
      c₄ ≠ p ∧ c₅ ≠ p ∧ c₆ ≠ p ∧ c₇ ≠ p ∧
      c₄ ≠ c₁ ∧ c₄ ≠ c₂ ∧ c₄ ≠ c₃ ∧ c₅ ≠ c₁ ∧ c₅ ≠ c₂ ∧ c₅ ≠ c₃ ∧ c₅ ≠ c₄ ∧
      c₆ ≠ c₁ ∧ c₆ ≠ c₂ ∧ c₆ ≠ c₃ ∧ c₆ ≠ c₄ ∧ c₆ ≠ c₅ ∧
      c₇ ≠ c₁ ∧ c₇ ≠ c₂ ∧ c₇ ≠ c₃ ∧ c₇ ≠ c₄ ∧ c₇ ≠ c₅ ∧ c₇ ≠ c₆ ∧
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      (∀ x ∈ S, b₃ x = ε * ((if x = c₃ then 1 else 0) - (if x = c₄ then 1 else 0))) ∧
      (∀ x ∈ S, b₄ x = ε * (if x = c₂ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₂ * (if x = c₆ then 1 else 0)) ∧
      (∀ x ∈ S, b₅ x = ε * (if x = c₁ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₃ * (if x = c₇ then 1 else 0)) := by
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨E, hE, F, hF, -, -, hEF, -, hb₃EF⟩ := norm_two_shape S deg hdeg b₃ hp₃ g33 hd₃
  have hval₃ : ∀ x ∈ S, b₃ x = -1 ∨ b₃ x = 0 ∨ b₃ x = 1 := by
    intro x hx
    rw [hb₃EF x hx]
    split_ifs <;> simp
  have h13' := sum_principal_diff_mul S b₁ b₃ hp hc₁ hc₂ ε hb₁
  rw [g13, hp₃] at h13'
  have h23' := sum_diff_mul S b₂ b₃ hc₁ hc₃ ε hb₂
  rw [g23] at h23'
  have h3eq : b₃ c₁ = b₃ c₂ := by
    have h : ε * (b₃ c₁ - b₃ c₂) = 0 := by linarith
    have := (mul_eq_zero.mp h).resolve_left hεne
    linarith
  have h3c₁ : b₃ c₁ = 0 := by
    by_contra hne
    obtain ⟨D, -, hDc, -, hform⟩ := diff_normalize S b₃ hEF hE hF hb₃EF hc₁
      (sign_of_ne_zero (hval₃ c₁ hc₁) hne) rfl
    have h := hform c₂ hc₂
    rw [← h3eq] at h
    by_cases hc₂D : c₂ = D
    · subst hc₂D
      simp only [Ne.symm h12, ite_true, ite_false, zero_sub, mul_neg, mul_one] at h
      exact hne (by linarith)
    · simp only [Ne.symm h12, hc₂D, ite_false, sub_zero, mul_zero] at h
      exact hne h
  have h3c₃ : b₃ c₃ = ε := by
    rw [h3c₁] at h23'
    rcases hε with rfl | rfl <;> linarith
  obtain ⟨c₄, hc₄, hc₄c₃, hc₄val, hb₃⟩ := diff_normalize S b₃ hEF hE hF hb₃EF hc₃ hε h3c₃
  have hc₄p : c₄ ≠ p := fun h => by
    rw [h, hp₃] at hc₄val
    exact hεne (by linarith)
  have hc₄c₁ : c₄ ≠ c₁ := fun h => by
    rw [h, h3c₁] at hc₄val
    exact hεne (by linarith)
  have hc₄c₂ : c₄ ≠ c₂ := fun h => by
    rw [h, ← h3eq, h3c₁] at hc₄val
    exact hεne (by linarith)
  obtain ⟨N₄, hN₄S, hN₄card, hN₄sign, hN₄out⟩ :=
    small_norm_support S b₄ (n := 3) (by norm_num) (by rw [g44]; norm_num)
  have hmem₄ : ∀ x ∈ S, b₄ x ≠ 0 → x ∈ N₄ := fun x hx h => by
    by_contra hxN
    exact h (hN₄out x hx hxN)
  have hne₄ : ∀ x ∈ N₄, b₄ x ≠ 0 := fun x hx => by
    rcases hN₄sign x hx with h | h <;> omega
  have h14' := sum_principal_diff_mul S b₁ b₄ hp hc₁ hc₂ ε hb₁
  rw [g14, hp₄] at h14'
  have h24' := sum_diff_mul S b₂ b₄ hc₁ hc₃ ε hb₂
  rw [g24] at h24'
  have h34' := sum_diff_mul S b₃ b₄ hc₃ hc₄ ε hb₃
  rw [g34] at h34'
  have h4₁₃ : b₄ c₃ = b₄ c₁ := by
    have := (mul_eq_zero.mp h24'.symm).resolve_left hεne
    linarith
  have h4₃₄ : b₄ c₄ = b₄ c₁ := by
    have := (mul_eq_zero.mp h34'.symm).resolve_left hεne
    linarith
  have h4c₁ : b₄ c₁ = 0 := by
    by_contra hne
    have hN₄eq := eq_of_card_three hN₄card (hmem₄ c₁ hc₁ hne)
      (hmem₄ c₃ hc₃ (h4₁₃ ▸ hne)) (hmem₄ c₄ hc₄ (h4₃₄ ▸ hne)) h13 (Ne.symm hc₄c₁)
      (Ne.symm hc₄c₃)
    exact three_label_degree_ne_zero S b₄ deg hdeg hN₄S hN₄out h13 (Ne.symm hc₄c₁)
      (Ne.symm hc₄c₃) hN₄eq h4₁₃ h4₃₄ hne hd₄
  have h4c₂ : b₄ c₂ = ε := by
    rw [h4c₁] at h14'
    rcases hε with rfl | rfl <;> linarith
  have hc₂N₄ : c₂ ∈ N₄ := hmem₄ c₂ hc₂ (by rw [h4c₂]; exact hεne)
  have herase₄ : (N₄.erase c₂).card = 2 := by
    rw [Finset.card_erase_of_mem hc₂N₄, hN₄card]
  obtain ⟨c₅, c₆, hc₅₆, hpair₄⟩ := Finset.card_eq_two.mp herase₄
  have hc₅mem : c₅ ∈ N₄.erase c₂ := hpair₄ ▸ by simp
  have hc₆mem : c₆ ∈ N₄.erase c₂ := hpair₄ ▸ by simp
  have hc₅N₄ := Finset.mem_of_mem_erase hc₅mem
  have hc₆N₄ := Finset.mem_of_mem_erase hc₆mem
  have hc₅ : c₅ ∈ S := hN₄S hc₅N₄
  have hc₆ : c₆ ∈ S := hN₄S hc₆N₄
  have hc₅c₂ := Finset.ne_of_mem_erase hc₅mem
  have hc₆c₂ := Finset.ne_of_mem_erase hc₆mem
  have hN₄eq : N₄ = {c₂, c₅, c₆} := by
    rw [← Finset.insert_erase hc₂N₄, hpair₄]
  have hzero₄ : ∀ y, b₄ y = 0 → ∀ x ∈ N₄, x ≠ y := fun y hy x hx h => hne₄ x hx (h ▸ hy)
  have hc₅c₁ := hzero₄ c₁ h4c₁ c₅ hc₅N₄
  have hc₆c₁ := hzero₄ c₁ h4c₁ c₆ hc₆N₄
  have hc₅c₃ := hzero₄ c₃ (by rw [h4₁₃, h4c₁]) c₅ hc₅N₄
  have hc₆c₃ := hzero₄ c₃ (by rw [h4₁₃, h4c₁]) c₆ hc₆N₄
  have hc₅c₄ := hzero₄ c₄ (by rw [h4₃₄, h4c₁]) c₅ hc₅N₄
  have hc₆c₄ := hzero₄ c₄ (by rw [h4₃₄, h4c₁]) c₆ hc₆N₄
  have hc₅p := hzero₄ p hp₄ c₅ hc₅N₄
  have hc₆p := hzero₄ p hp₄ c₆ hc₆N₄
  have hb₄ : ∀ x ∈ S, b₄ x = ε * (if x = c₂ then 1 else 0) + b₄ c₅ * (if x = c₅ then 1 else 0) +
      b₄ c₆ * (if x = c₆ then 1 else 0) := by
    intro x hx
    rw [form_of_support_three S b₄ (Ne.symm hc₅c₂) (Ne.symm hc₆c₂) hc₅₆ (fun y hy h₁ h₂ h₃ =>
      hN₄out y hy (by rw [hN₄eq]; simp [h₁, h₂, h₃])) x hx, h4c₂]
  obtain ⟨N₅, hN₅S, hN₅card, hN₅sign, hN₅out⟩ :=
    small_norm_support S b₅ (n := 3) (by norm_num) (by rw [g55]; norm_num)
  have hmem₅ : ∀ x ∈ S, b₅ x ≠ 0 → x ∈ N₅ := fun x hx h => by
    by_contra hxN
    exact h (hN₅out x hx hxN)
  have hne₅ : ∀ x ∈ N₅, b₅ x ≠ 0 := fun x hx => by
    rcases hN₅sign x hx with h | h <;> omega
  have h15' := sum_principal_diff_mul S b₁ b₅ hp hc₁ hc₂ ε hb₁
  rw [g15, hp₅] at h15'
  have h25' := sum_diff_mul S b₂ b₅ hc₁ hc₃ ε hb₂
  rw [g25] at h25'
  have h35' := sum_diff_mul S b₃ b₅ hc₃ hc₄ ε hb₃
  rw [g35] at h35'
  have h5₂₃ : b₅ c₃ = b₅ c₂ := by
    have h : ε * (b₅ c₂ - b₅ c₃) = 0 := by linarith
    have := (mul_eq_zero.mp h).resolve_left hεne
    linarith
  have h5₃₄ : b₅ c₄ = b₅ c₂ := by
    have := (mul_eq_zero.mp h35'.symm).resolve_left hεne
    linarith
  have h5c₂ : b₅ c₂ = 0 := by
    by_contra hne
    have hN₅eq := eq_of_card_three hN₅card (hmem₅ c₂ hc₂ hne)
      (hmem₅ c₃ hc₃ (h5₂₃ ▸ hne)) (hmem₅ c₄ hc₄ (h5₃₄ ▸ hne)) h23 (Ne.symm hc₄c₂)
      (Ne.symm hc₄c₃)
    exact three_label_degree_ne_zero S b₅ deg hdeg hN₅S hN₅out h23 (Ne.symm hc₄c₂)
      (Ne.symm hc₄c₃) hN₅eq h5₂₃ h5₃₄ hne hd₅
  have h5c₁ : b₅ c₁ = ε := by
    rw [h5c₂] at h15'
    rcases hε with rfl | rfl <;> linarith
  have hc₁N₅ : c₁ ∈ N₅ := hmem₅ c₁ hc₁ (by rw [h5c₁]; exact hεne)
  have hzero₅ : ∀ y, b₅ y = 0 → ∀ x ∈ N₅, x ≠ y := fun y hy x hx h => hne₅ x hx (h ▸ hy)
  have h45' := sum_three_mul S b₄ b₅ hc₂ hc₅ hc₆ ε (b₄ c₅) (b₄ c₆) hb₄
  rw [g45, h5c₂, mul_zero, zero_add] at h45'
  have hε₁ : b₄ c₅ = 1 ∨ b₄ c₅ = -1 := hN₄sign c₅ hc₅N₄
  have hε₂ : b₄ c₆ = 1 ∨ b₄ c₆ = -1 := hN₄sign c₆ hc₆N₄
  have hval₅ : ∀ x ∈ S, b₅ x = -1 ∨ b₅ x = 0 ∨ b₅ x = 1 := fun x hx => by
    by_cases hxN : x ∈ N₅
    · rcases hN₅sign x hxN with h | h <;> simp [h]
    · simp [hN₅out x hx hxN]
  have hcase : (b₅ c₅ = b₄ c₅ ∧ b₅ c₆ = 0) ∨ (b₅ c₅ = 0 ∧ b₅ c₆ = b₄ c₆) := by
    have h5 := hval₅ c₅ hc₅
    have h6 := hval₅ c₆ hc₆
    rcases hε₁ with h₁ | h₁ <;> rcases hε₂ with h₂ | h₂ <;> rw [h₁, h₂] at h45' ⊢ <;> omega
  have hc₂N₅ := hzero₅ c₂ h5c₂
  have hc₃N₅ := hzero₅ c₃ (by rw [h5₂₃, h5c₂])
  have hc₄N₅ := hzero₅ c₄ (by rw [h5₃₄, h5c₂])
  have hpN₅ := hzero₅ p hp₅
  rcases hcase with ⟨hA₅, hA₆⟩ | ⟨hB₅, hB₆⟩
  · have hc₅N₅ : c₅ ∈ N₅ := hmem₅ c₅ hc₅ (by rw [hA₅]; rcases hε₁ with h | h <;> omega)
    obtain ⟨c₇, hc₇, hc₇c₁, hc₇c₅, hsign₇, hform₅⟩ :=
      third_support_point S b₅ hN₅S hN₅card hN₅sign hN₅out hc₁N₅ hc₅N₅ hc₅c₁
    have hc₇N₅ : c₇ ∈ N₅ := hmem₅ c₇ hc₇ (by rcases hsign₇ with h | h <;> omega)
    refine ⟨c₄, c₅, c₆, c₇, b₄ c₅, b₄ c₆, b₅ c₇, hc₄, hc₅, hc₆, hc₇, hc₄p, hc₅p, hc₆p,
      hpN₅ c₇ hc₇N₅, hc₄c₁, hc₄c₂, hc₄c₃, hc₅c₁, hc₅c₂, hc₅c₃, hc₅c₄, hc₆c₁, hc₆c₂,
      hc₆c₃, hc₆c₄, Ne.symm hc₅₆, hc₇c₁, hc₂N₅ c₇ hc₇N₅, hc₃N₅ c₇ hc₇N₅, hc₄N₅ c₇ hc₇N₅,
      hc₇c₅, hzero₅ c₆ hA₆ c₇ hc₇N₅, hε₁, hε₂, hsign₇, hb₃, hb₄, fun x hx => ?_⟩
    rw [hform₅ x hx, h5c₁, hA₅]
  · have hc₆N₅ : c₆ ∈ N₅ := hmem₅ c₆ hc₆ (by rw [hB₆]; rcases hε₂ with h | h <;> omega)
    obtain ⟨c₇, hc₇, hc₇c₁, hc₇c₆, hsign₇, hform₅⟩ :=
      third_support_point S b₅ hN₅S hN₅card hN₅sign hN₅out hc₁N₅ hc₆N₅ hc₆c₁
    have hc₇N₅ : c₇ ∈ N₅ := hmem₅ c₇ hc₇ (by rcases hsign₇ with h | h <;> omega)
    refine ⟨c₄, c₆, c₅, c₇, b₄ c₆, b₄ c₅, b₅ c₇, hc₄, hc₆, hc₅, hc₇, hc₄p, hc₆p, hc₅p,
      hpN₅ c₇ hc₇N₅, hc₄c₁, hc₄c₂, hc₄c₃, hc₆c₁, hc₆c₂, hc₆c₃, hc₆c₄, hc₅c₁, hc₅c₂,
      hc₅c₃, hc₅c₄, hc₅₆, hc₇c₁, hc₂N₅ c₇ hc₇N₅, hc₃N₅ c₇ hc₇N₅, hc₄N₅ c₇ hc₇N₅,
      hc₇c₆, hzero₅ c₅ hB₅ c₇ hc₇N₅, hε₂, hε₁, hsign₇, hb₃, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hb₄ x hx]
      ring
    · rw [hform₅ x hx, h5c₁, hB₆]

theorem seven_labels_of_first_two (S : Finset L) {p : L} (hp : p ∈ S) (deg : L → ℤ)
    (hdeg : ∀ x ∈ S, 0 < deg x) (hdegp : deg p = 1) (b₁ b₂ b₃ b₄ b₅ : L → ℤ) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {c₁ c₂ c₃ : L} (hc₁ : c₁ ∈ S) (hc₂ : c₂ ∈ S) (hc₃ : c₃ ∈ S)
    (h1p : c₁ ≠ p) (h2p : c₂ ≠ p) (h3p : c₃ ≠ p) (h12 : c₁ ≠ c₂) (h13 : c₁ ≠ c₃)
    (h23 : c₂ ≠ c₃)
    (hb₁ : ∀ x ∈ S, b₁ x = (if x = p then 1 else 0) +
      ε * ((if x = c₁ then 1 else 0) - (if x = c₂ then 1 else 0)))
    (hb₂ : ∀ x ∈ S, b₂ x = ε * ((if x = c₁ then 1 else 0) - (if x = c₃ then 1 else 0)))
    (hp₃ : b₃ p = 0) (hp₄ : b₄ p = 0) (hp₅ : b₅ p = 0)
    (hd₁ : ∑ x ∈ S, b₁ x * deg x = 0) (hd₂ : ∑ x ∈ S, b₂ x * deg x = 0)
    (hd₃ : ∑ x ∈ S, b₃ x * deg x = 0) (hd₄ : ∑ x ∈ S, b₄ x * deg x = 0)
    (hd₅ : ∑ x ∈ S, b₅ x * deg x = 0)
    (g13 : ∑ x ∈ S, b₁ x * b₃ x = 0) (g14 : ∑ x ∈ S, b₁ x * b₄ x = -1)
    (g15 : ∑ x ∈ S, b₁ x * b₅ x = 1) (g23 : ∑ x ∈ S, b₂ x * b₃ x = -1)
    (g24 : ∑ x ∈ S, b₂ x * b₄ x = 0) (g25 : ∑ x ∈ S, b₂ x * b₅ x = 1)
    (g33 : ∑ x ∈ S, b₃ x * b₃ x = 2) (g34 : ∑ x ∈ S, b₃ x * b₄ x = 0)
    (g35 : ∑ x ∈ S, b₃ x * b₅ x = 0) (g44 : ∑ x ∈ S, b₄ x * b₄ x = 3)
    (g45 : ∑ x ∈ S, b₄ x * b₅ x = 1) (g55 : ∑ x ∈ S, b₅ x * b₅ x = 3) :
    ∃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : L, ∃ ε ε₁ ε₂ ε₃ : ℤ,
      (c₁ ∈ S ∧ c₂ ∈ S ∧ c₃ ∈ S ∧ c₄ ∈ S ∧ c₅ ∈ S ∧ c₆ ∈ S ∧ c₇ ∈ S) ∧
      (c₁ ≠ p ∧ c₂ ≠ p ∧ c₃ ≠ p ∧ c₄ ≠ p ∧ c₅ ≠ p ∧ c₆ ≠ p ∧ c₇ ≠ p) ∧
      [c₁, c₂, c₃, c₄, c₅, c₆, c₇].Nodup ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      (∀ x ∈ S, b₁ x = (if x = p then 1 else 0) +
        ε * ((if x = c₁ then 1 else 0) - (if x = c₂ then 1 else 0))) ∧
      (∀ x ∈ S, b₂ x = ε * ((if x = c₁ then 1 else 0) - (if x = c₃ then 1 else 0))) ∧
      (∀ x ∈ S, b₃ x = ε * ((if x = c₃ then 1 else 0) - (if x = c₄ then 1 else 0))) ∧
      (∀ x ∈ S, b₄ x = ε * (if x = c₂ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₂ * (if x = c₆ then 1 else 0)) ∧
      (∀ x ∈ S, b₅ x = ε * (if x = c₁ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₃ * (if x = c₇ then 1 else 0)) ∧
      deg c₂ = deg c₁ + ε ∧ deg c₃ = deg c₁ ∧ deg c₄ = deg c₁ ∧
      ε * deg c₂ + ε₁ * deg c₅ + ε₂ * deg c₆ = 0 ∧
      ε * deg c₁ + ε₁ * deg c₅ + ε₃ * deg c₇ = 0 := by
  obtain ⟨c₄, c₅, c₆, c₇, ε₁, ε₂, ε₃, hc₄, hc₅, hc₆, hc₇, h4p, h5p, h6p, h7p, h41, h42, h43,
      h51, h52, h53, h54, h61, h62, h63, h64, h65, h71, h72, h73, h74, h75, h76, hε₁, hε₂, hε₃,
      hb₃, hb₄, hb₅⟩ :=
    shapes_of_first_two S hp deg hdeg b₁ b₂ b₃ b₄ b₅ hε hc₁ hc₂ hc₃ h12 h13 h23 hb₁ hb₂ hp₃
      hp₄ hp₅ hd₃ hd₄ hd₅ g13 g14 g15 g23 g24 g25 g33 g34 g35 g44 g45 g55
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have e₁ := sum_principal_diff_mul S b₁ deg hp hc₁ hc₂ ε hb₁
  have e₂ := sum_diff_mul S b₂ deg hc₁ hc₃ ε hb₂
  have e₃ := sum_diff_mul S b₃ deg hc₃ hc₄ ε hb₃
  have e₄ := sum_three_mul S b₄ deg hc₂ hc₅ hc₆ ε ε₁ ε₂ hb₄
  have e₅ := sum_three_mul S b₅ deg hc₁ hc₅ hc₇ ε ε₁ ε₃ hb₅
  rw [hd₁, hdegp] at e₁
  rw [hd₂] at e₂
  rw [hd₃] at e₃
  rw [hd₄] at e₄
  rw [hd₅] at e₅
  have hd₃₁ : deg c₃ = deg c₁ := by
    have := (mul_eq_zero.mp e₂.symm).resolve_left hεne
    linarith
  have hd₄₃ : deg c₄ = deg c₃ := by
    have := (mul_eq_zero.mp e₃.symm).resolve_left hεne
    linarith
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, ε, ε₁, ε₂, ε₃, ⟨hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇⟩,
    ⟨h1p, h2p, h3p, h4p, h5p, h6p, h7p⟩, ?_, hε, hε₁, hε₂, hε₃, hb₁, hb₂, hb₃, hb₄, hb₅, ?_,
    hd₃₁, hd₄₃.trans hd₃₁, e₄.symm, e₅.symm⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_or, and_true]
    exact ⟨⟨h12, h13, Ne.symm h41, Ne.symm h51, Ne.symm h61, Ne.symm h71⟩,
      ⟨h23, Ne.symm h42, Ne.symm h52, Ne.symm h62, Ne.symm h72⟩,
      ⟨Ne.symm h43, Ne.symm h53, Ne.symm h63, Ne.symm h73⟩,
      ⟨Ne.symm h54, Ne.symm h64, Ne.symm h74⟩, ⟨Ne.symm h65, Ne.symm h75⟩, Ne.symm h76, fun h => h⟩
  · rcases hε with rfl | rfl <;> linarith

theorem seven_labels_coordinates (S : Finset L) {p : L} (hp : p ∈ S) (deg : L → ℤ)
    (hdeg : ∀ x ∈ S, 0 < deg x) (hdegp : deg p = 1) (b₁ b₂ b₃ b₄ b₅ : L → ℤ)
    (hp₁ : b₁ p = 1) (hp₂ : b₂ p = 0) (hp₃ : b₃ p = 0) (hp₄ : b₄ p = 0) (hp₅ : b₅ p = 0)
    (hd₁ : ∑ x ∈ S, b₁ x * deg x = 0) (hd₂ : ∑ x ∈ S, b₂ x * deg x = 0)
    (hd₃ : ∑ x ∈ S, b₃ x * deg x = 0) (hd₄ : ∑ x ∈ S, b₄ x * deg x = 0)
    (hd₅ : ∑ x ∈ S, b₅ x * deg x = 0)
    (g11 : ∑ x ∈ S, b₁ x * b₁ x = 3) (g12 : ∑ x ∈ S, b₁ x * b₂ x = 1)
    (g13 : ∑ x ∈ S, b₁ x * b₃ x = 0) (g14 : ∑ x ∈ S, b₁ x * b₄ x = -1)
    (g15 : ∑ x ∈ S, b₁ x * b₅ x = 1) (g22 : ∑ x ∈ S, b₂ x * b₂ x = 2)
    (g23 : ∑ x ∈ S, b₂ x * b₃ x = -1) (g24 : ∑ x ∈ S, b₂ x * b₄ x = 0)
    (g25 : ∑ x ∈ S, b₂ x * b₅ x = 1) (g33 : ∑ x ∈ S, b₃ x * b₃ x = 2)
    (g34 : ∑ x ∈ S, b₃ x * b₄ x = 0) (g35 : ∑ x ∈ S, b₃ x * b₅ x = 0)
    (g44 : ∑ x ∈ S, b₄ x * b₄ x = 3) (g45 : ∑ x ∈ S, b₄ x * b₅ x = 1)
    (g55 : ∑ x ∈ S, b₅ x * b₅ x = 3) :
    ∃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : L, ∃ ε ε₁ ε₂ ε₃ : ℤ,
      (c₁ ∈ S ∧ c₂ ∈ S ∧ c₃ ∈ S ∧ c₄ ∈ S ∧ c₅ ∈ S ∧ c₆ ∈ S ∧ c₇ ∈ S) ∧
      (c₁ ≠ p ∧ c₂ ≠ p ∧ c₃ ≠ p ∧ c₄ ≠ p ∧ c₅ ≠ p ∧ c₆ ≠ p ∧ c₇ ≠ p) ∧
      [c₁, c₂, c₃, c₄, c₅, c₆, c₇].Nodup ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      (∀ x ∈ S, b₁ x = (if x = p then 1 else 0) +
        ε * ((if x = c₁ then 1 else 0) - (if x = c₂ then 1 else 0))) ∧
      (∀ x ∈ S, b₂ x = ε * ((if x = c₁ then 1 else 0) - (if x = c₃ then 1 else 0))) ∧
      (∀ x ∈ S, b₃ x = ε * ((if x = c₃ then 1 else 0) - (if x = c₄ then 1 else 0))) ∧
      (∀ x ∈ S, b₄ x = ε * (if x = c₂ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₂ * (if x = c₆ then 1 else 0)) ∧
      (∀ x ∈ S, b₅ x = ε * (if x = c₁ then 1 else 0) + ε₁ * (if x = c₅ then 1 else 0) +
        ε₃ * (if x = c₇ then 1 else 0)) ∧
      deg c₂ = deg c₁ + ε ∧ deg c₃ = deg c₁ ∧ deg c₄ = deg c₁ ∧
      ε * deg c₂ + ε₁ * deg c₅ + ε₂ * deg c₆ = 0 ∧
      ε * deg c₁ + ε₁ * deg c₅ + ε₃ * deg c₇ = 0 := by
  obtain ⟨A, hA, B, hB, hAp, hBp, hAB, -, hb₁⟩ :=
    principal_norm_three_shape S hp deg hdeg hdegp b₁ hp₁ g11 hd₁
  obtain ⟨C, hC, D, hD, -, -, hCD, -, hb₂CD⟩ := norm_two_shape S deg hdeg b₂ hp₂ g22 hd₂
  have hval₂ : ∀ x ∈ S, b₂ x = -1 ∨ b₂ x = 0 ∨ b₂ x = 1 := by
    intro x hx
    rw [hb₂CD x hx]
    split_ifs <;> simp
  have h12' := sum_principal_diff_mul S b₁ b₂ hp hA hB 1 hb₁
  rw [g12, hp₂] at h12'
  have hcase : (b₂ A = 1 ∧ b₂ B = 0) ∨ (b₂ A = 0 ∧ b₂ B = -1) := by
    have := hval₂ A hA
    have := hval₂ B hB
    omega
  rcases hcase with ⟨hA₂, hB₂⟩ | ⟨hA₂, hB₂⟩
  · obtain ⟨c₃, hc₃, hc₃A, hc₃val, hb₂⟩ :=
      diff_normalize S b₂ hCD hC hD hb₂CD hA (Or.inl rfl) hA₂
    have hc₃B : c₃ ≠ B := fun h => by rw [h, hB₂] at hc₃val; norm_num at hc₃val
    have hc₃p : c₃ ≠ p := fun h => by rw [h, hp₂] at hc₃val; norm_num at hc₃val
    exact seven_labels_of_first_two S hp deg hdeg hdegp b₁ b₂ b₃ b₄ b₅ (Or.inl rfl) hA hB hc₃
      hAp hBp hc₃p hAB (Ne.symm hc₃A) (Ne.symm hc₃B) hb₁ hb₂ hp₃ hp₄ hp₅ hd₁ hd₂ hd₃ hd₄ hd₅
      g13 g14 g15 g23 g24 g25 g33 g34 g35 g44 g45 g55
  · obtain ⟨c₃, hc₃, hc₃B, hc₃val, hb₂⟩ :=
      diff_normalize S b₂ hCD hC hD hb₂CD hB (Or.inr rfl) hB₂
    have hc₃A : c₃ ≠ A := fun h => by rw [h, hA₂] at hc₃val; norm_num at hc₃val
    have hc₃p : c₃ ≠ p := fun h => by rw [h, hp₂] at hc₃val; norm_num at hc₃val
    have hb₁' : ∀ x ∈ S, b₁ x = (if x = p then 1 else 0) +
        (-1) * ((if x = B then 1 else 0) - (if x = A then 1 else 0)) := fun x hx => by
      rw [hb₁ x hx]
      ring
    exact seven_labels_of_first_two S hp deg hdeg hdegp b₁ b₂ b₃ b₄ b₅ (Or.inr rfl) hB hA hc₃
      hBp hAp hc₃p (Ne.symm hAB) (Ne.symm hc₃B) (Ne.symm hc₃A) hb₁' hb₂ hp₃ hp₄ hp₅ hd₁ hd₂
      hd₃ hd₄ hd₅ g13 g14 g15 g23 g24 g25 g33 g34 g35 g44 g45 g55

theorem single_apply_ind {M : Type*} [DecidableEq M] (a x : M) (b : ℤ) :
    Finsupp.single a b x = b * (if x = a then 1 else 0) := by
  rw [Finsupp.single_apply]
  by_cases h : x = a
  · rw [ite_eq_left h.symm, ite_eq_left h, mul_one]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]

end SevenIrreducibles

open SevenIrreducibles TwoRankLowerBound.Helpers

theorem five_virtual_characters_produce_seven_irreducibles {G : Type} [Group G] [Fintype G]
    {β₁ β₂ β₃ β₄ β₅ : G → ℂ} (hβ₁ : β₁ ∈ BlocksVChar G) (hβ₂ : β₂ ∈ BlocksVChar G)
    (hβ₃ : β₃ ∈ BlocksVChar G) (hβ₄ : β₄ ∈ BlocksVChar G) (hβ₅ : β₅ ∈ BlocksVChar G)
    (hdeg₁ : β₁ 1 = 0) (hdeg₂ : β₂ 1 = 0) (hdeg₃ : β₃ 1 = 0) (hdeg₄ : β₄ 1 = 0)
    (hdeg₅ : β₅ 1 = 0)
    (hprin₁ : BlocksInnerProduct β₁ 1 = 1) (hprin₂ : BlocksInnerProduct β₂ 1 = 0)
    (hprin₃ : BlocksInnerProduct β₃ 1 = 0) (hprin₄ : BlocksInnerProduct β₄ 1 = 0)
    (hprin₅ : BlocksInnerProduct β₅ 1 = 0)
    (g11 : BlocksInnerProduct β₁ β₁ = 3) (g12 : BlocksInnerProduct β₁ β₂ = 1)
    (g13 : BlocksInnerProduct β₁ β₃ = 0) (g14 : BlocksInnerProduct β₁ β₄ = -1)
    (g15 : BlocksInnerProduct β₁ β₅ = 1) (g22 : BlocksInnerProduct β₂ β₂ = 2)
    (g23 : BlocksInnerProduct β₂ β₃ = -1) (g24 : BlocksInnerProduct β₂ β₄ = 0)
    (g25 : BlocksInnerProduct β₂ β₅ = 1) (g33 : BlocksInnerProduct β₃ β₃ = 2)
    (g34 : BlocksInnerProduct β₃ β₄ = 0) (g35 : BlocksInnerProduct β₃ β₅ = 0)
    (g44 : BlocksInnerProduct β₄ β₄ = 3) (g45 : BlocksInnerProduct β₄ β₅ = 1)
    (g55 : BlocksInnerProduct β₅ β₅ = 3) :
    ∃ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
      (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      β₁ = 1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) ∧
      β₂ = (ε : ℂ) • ((χ₁ : G → ℂ) - χ₃) ∧
      β₃ = (ε : ℂ) • ((χ₃ : G → ℂ) - χ₄) ∧
      β₄ = (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) ∧
      β₅ = (ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ) ∧
      (χ₂ : G → ℂ) 1 = (χ₁ : G → ℂ) 1 + ε ∧ (χ₃ : G → ℂ) 1 = (χ₁ : G → ℂ) 1 ∧
      (χ₄ : G → ℂ) 1 = (χ₁ : G → ℂ) 1 ∧
      (ε : ℂ) * (χ₂ : G → ℂ) 1 + ε₁ * (χ₅ : G → ℂ) 1 + ε₂ * (χ₆ : G → ℂ) 1 = 0 ∧
      (ε : ℂ) * (χ₁ : G → ℂ) 1 + ε₁ * (χ₅ : G → ℂ) 1 + ε₃ * (χ₇ : G → ℂ) 1 = 0 := by
  classical
  obtain ⟨n₁, hn₁, -⟩ := blocksVChar_exists_unique_expansion hβ₁
  obtain ⟨n₂, hn₂, -⟩ := blocksVChar_exists_unique_expansion hβ₂
  obtain ⟨n₃, hn₃, -⟩ := blocksVChar_exists_unique_expansion hβ₃
  obtain ⟨n₄, hn₄, -⟩ := blocksVChar_exists_unique_expansion hβ₄
  obtain ⟨n₅, hn₅, -⟩ := blocksVChar_exists_unique_expansion hβ₅
  let p : BlocksIrr G := ⟨1, principal_mem_blocksIrr G⟩
  choose d hdpos hdval using fun χ : BlocksIrr G => blocksIrr_degree_eq_natCast χ
  let S : Finset (BlocksIrr G) :=
    insert p (n₁.support ∪ n₂.support ∪ n₃.support ∪ n₄.support ∪ n₅.support)
  have hpS : p ∈ S := Finset.mem_insert_self _ _
  have hS₁ : n₁.support ⊆ S := fun χ hχ => Finset.mem_insert_of_mem (by simp [hχ])
  have hS₂ : n₂.support ⊆ S := fun χ hχ => Finset.mem_insert_of_mem (by simp [hχ])
  have hS₃ : n₃.support ⊆ S := fun χ hχ => Finset.mem_insert_of_mem (by simp [hχ])
  have hS₄ : n₄.support ⊆ S := fun χ hχ => Finset.mem_insert_of_mem (by simp [hχ])
  have hS₅ : n₅.support ⊆ S := fun χ hχ => Finset.mem_insert_of_mem (by simp [hχ])
  have hdot : ∀ n m : BlocksIrr G →₀ ℤ, m.support ⊆ S →
      BlocksInnerProduct (blocksCharacterExpansion G n) (blocksCharacterExpansion G m) =
        ((∑ χ ∈ S, n χ * m χ : ℤ) : ℂ) := by
    intro n m hm
    rw [blocksInnerProduct_expansions]
    congr 1
    apply Finset.sum_subset hm
    intro χ _ hχ
    rw [Finsupp.notMem_support_iff.mp hχ, mul_zero]
  have hdegsum : ∀ n : BlocksIrr G →₀ ℤ, n.support ⊆ S →
      blocksCharacterExpansion G n 1 = ((∑ χ ∈ S, n χ * (d χ : ℤ) : ℤ) : ℂ) := by
    intro n hn
    rw [blocksCharacterExpansion_apply, Int.cast_sum]
    rw [Finset.sum_subset hn (fun χ _ hχ => by rw [Finsupp.notMem_support_iff.mp hχ]; simp)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hdval χ]
    push_cast
    ring
  have hdegp : ((d p : ℕ) : ℤ) = 1 := by
    have h : (1 : G → ℂ) 1 = (d p : ℂ) := hdval p
    rw [Pi.one_apply] at h
    exact_mod_cast h.symm
  have hdeg : ∀ n : BlocksIrr G →₀ ℤ, n.support ⊆ S → ∀ β : G → ℂ,
      blocksCharacterExpansion G n = β → β 1 = 0 → ∑ x ∈ S, n x * (d x : ℤ) = 0 := by
    intro n hn β hnβ hβ
    have h := hdegsum n hn
    rw [hnβ, hβ] at h
    exact_mod_cast h.symm
  have hprin : ∀ n : BlocksIrr G →₀ ℤ, ∀ β : G → ℂ, ∀ c : ℤ,
      blocksCharacterExpansion G n = β → BlocksInnerProduct β 1 = c → n p = c := by
    intro n β c hnβ hβ
    have h := blocksInnerProduct_expansion_coefficient n p
    rw [hnβ] at h
    change BlocksInnerProduct β 1 = _ at h
    rw [hβ] at h
    exact_mod_cast h.symm
  have hgram : ∀ n m : BlocksIrr G →₀ ℤ, m.support ⊆ S → ∀ β γ : G → ℂ, ∀ c : ℤ,
      blocksCharacterExpansion G n = β → blocksCharacterExpansion G m = γ →
        BlocksInnerProduct β γ = c → ∑ x ∈ S, n x * m x = c := by
    intro n m hm β γ c hnβ hmγ hβγ
    have h := hdot n m hm
    rw [hnβ, hmγ, hβγ] at h
    exact_mod_cast h.symm
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, ε, ε₁, ε₂, ε₃, ⟨hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇⟩,
      ⟨h1p, h2p, h3p, h4p, h5p, h6p, h7p⟩, hnodup, hε, hε₁, hε₂, hε₃, hf₁, hf₂, hf₃, hf₄, hf₅,
      hd₂₁, hd₃₁, hd₄₁, hd₄, hd₅⟩ :=
    seven_labels_coordinates S hpS (fun χ => (d χ : ℤ)) (fun χ _ => by exact_mod_cast hdpos χ)
      hdegp n₁ n₂ n₃ n₄ n₅ (hprin n₁ β₁ 1 hn₁ (by rw [hprin₁]; norm_num))
      (hprin n₂ β₂ 0 hn₂ (by rw [hprin₂]; norm_num))
      (hprin n₃ β₃ 0 hn₃ (by rw [hprin₃]; norm_num))
      (hprin n₄ β₄ 0 hn₄ (by rw [hprin₄]; norm_num))
      (hprin n₅ β₅ 0 hn₅ (by rw [hprin₅]; norm_num))
      (hdeg n₁ hS₁ β₁ hn₁ hdeg₁) (hdeg n₂ hS₂ β₂ hn₂ hdeg₂) (hdeg n₃ hS₃ β₃ hn₃ hdeg₃)
      (hdeg n₄ hS₄ β₄ hn₄ hdeg₄) (hdeg n₅ hS₅ β₅ hn₅ hdeg₅)
      (hgram n₁ n₁ hS₁ β₁ β₁ 3 hn₁ hn₁ (by rw [g11]; norm_num))
      (hgram n₁ n₂ hS₂ β₁ β₂ 1 hn₁ hn₂ (by rw [g12]; norm_num))
      (hgram n₁ n₃ hS₃ β₁ β₃ 0 hn₁ hn₃ (by rw [g13]; norm_num))
      (hgram n₁ n₄ hS₄ β₁ β₄ (-1) hn₁ hn₄ (by rw [g14]; norm_num))
      (hgram n₁ n₅ hS₅ β₁ β₅ 1 hn₁ hn₅ (by rw [g15]; norm_num))
      (hgram n₂ n₂ hS₂ β₂ β₂ 2 hn₂ hn₂ (by rw [g22]; norm_num))
      (hgram n₂ n₃ hS₃ β₂ β₃ (-1) hn₂ hn₃ (by rw [g23]; norm_num))
      (hgram n₂ n₄ hS₄ β₂ β₄ 0 hn₂ hn₄ (by rw [g24]; norm_num))
      (hgram n₂ n₅ hS₅ β₂ β₅ 1 hn₂ hn₅ (by rw [g25]; norm_num))
      (hgram n₃ n₃ hS₃ β₃ β₃ 2 hn₃ hn₃ (by rw [g33]; norm_num))
      (hgram n₃ n₄ hS₄ β₃ β₄ 0 hn₃ hn₄ (by rw [g34]; norm_num))
      (hgram n₃ n₅ hS₅ β₃ β₅ 0 hn₃ hn₅ (by rw [g35]; norm_num))
      (hgram n₄ n₄ hS₄ β₄ β₄ 3 hn₄ hn₄ (by rw [g44]; norm_num))
      (hgram n₄ n₅ hS₅ β₄ β₅ 1 hn₄ hn₅ (by rw [g45]; norm_num))
      (hgram n₅ n₅ hS₅ β₅ β₅ 3 hn₅ hn₅ (by rw [g55]; norm_num))
  have hout : ∀ x, x ∉ S → x ≠ p ∧ x ≠ c₁ ∧ x ≠ c₂ ∧ x ≠ c₃ ∧ x ≠ c₄ ∧ x ≠ c₅ ∧ x ≠ c₆ ∧
      x ≠ c₇ := fun x hx =>
    ⟨fun h => hx (h ▸ hpS), fun h => hx (h ▸ hc₁), fun h => hx (h ▸ hc₂),
      fun h => hx (h ▸ hc₃), fun h => hx (h ▸ hc₄), fun h => hx (h ▸ hc₅),
      fun h => hx (h ▸ hc₆), fun h => hx (h ▸ hc₇)⟩
  have hzero : ∀ n : BlocksIrr G →₀ ℤ, n.support ⊆ S → ∀ x, x ∉ S → n x = 0 :=
    fun n hn x hx => Finsupp.notMem_support_iff.mp fun h => hx (hn h)
  have hm₁ : n₁ = Finsupp.single p 1 + (Finsupp.single c₁ ε - Finsupp.single c₂ ε) := by
    ext x
    simp only [Finsupp.add_apply, Finsupp.sub_apply, single_apply_ind]
    by_cases hx : x ∈ S
    · rw [hf₁ x hx]
      ring
    · obtain ⟨hxp, hx1, hx2, -⟩ := hout x hx
      simp [hzero n₁ hS₁ x hx, hxp, hx1, hx2]
  have hm₂ : n₂ = Finsupp.single c₁ ε - Finsupp.single c₃ ε := by
    ext x
    simp only [Finsupp.sub_apply, single_apply_ind]
    by_cases hx : x ∈ S
    · rw [hf₂ x hx]
      ring
    · obtain ⟨-, hx1, -, hx3, -⟩ := hout x hx
      simp [hzero n₂ hS₂ x hx, hx1, hx3]
  have hm₃ : n₃ = Finsupp.single c₃ ε - Finsupp.single c₄ ε := by
    ext x
    simp only [Finsupp.sub_apply, single_apply_ind]
    by_cases hx : x ∈ S
    · rw [hf₃ x hx]
      ring
    · obtain ⟨-, -, -, hx3, hx4, -⟩ := hout x hx
      simp [hzero n₃ hS₃ x hx, hx3, hx4]
  have hm₄ : n₄ = Finsupp.single c₂ ε + Finsupp.single c₅ ε₁ + Finsupp.single c₆ ε₂ := by
    ext x
    simp only [Finsupp.add_apply, single_apply_ind]
    by_cases hx : x ∈ S
    · rw [hf₄ x hx]
    · obtain ⟨-, -, hx2, -, -, hx5, hx6, -⟩ := hout x hx
      simp [hzero n₄ hS₄ x hx, hx2, hx5, hx6]
  have hm₅ : n₅ = Finsupp.single c₁ ε + Finsupp.single c₅ ε₁ + Finsupp.single c₇ ε₃ := by
    ext x
    simp only [Finsupp.add_apply, single_apply_ind]
    by_cases hx : x ∈ S
    · rw [hf₅ x hx]
    · obtain ⟨-, hx1, -, -, -, hx5, -, hx7⟩ := hout x hx
      simp [hzero n₅ hS₅ x hx, hx1, hx5, hx7]
  have hp1 : ((1 : ℤ) : ℂ) • (p : G → ℂ) = 1 := by
    rw [Int.cast_one, one_smul]
  have hne1 : ∀ χ : BlocksIrr G, χ ≠ p → (χ : G → ℂ) ≠ 1 := fun χ hχ h =>
    hχ (Subtype.ext h)
  have hcast : ∀ χ : BlocksIrr G, (χ : G → ℂ) 1 = ((d χ : ℤ) : ℂ) := fun χ => by
    rw [hdval χ]
    push_cast
    rfl
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, ε, ε₁, ε₂, ε₃, hnodup, hne1 c₁ h1p, hne1 c₂ h2p,
    hne1 c₃ h3p, hne1 c₄ h4p, hne1 c₅ h5p, hne1 c₆ h6p, hne1 c₇ h7p, hε, hε₁, hε₂, hε₃,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn₁, hm₁, map_add, map_sub, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, blocksCharacterExpansion_single, hp1, smul_sub]
  · rw [← hn₂, hm₂, map_sub, blocksCharacterExpansion_single, blocksCharacterExpansion_single,
      smul_sub]
  · rw [← hn₃, hm₃, map_sub, blocksCharacterExpansion_single, blocksCharacterExpansion_single,
      smul_sub]
  · rw [← hn₄, hm₄, map_add, map_add, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, blocksCharacterExpansion_single]
  · rw [← hn₅, hm₅, map_add, map_add, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, blocksCharacterExpansion_single]
  · rw [hcast, hcast, hd₂₁]
    push_cast
    ring
  · rw [hcast, hcast, hd₃₁]
  · rw [hcast, hcast, hd₄₁]
  · rw [hcast, hcast, hcast]
    exact_mod_cast hd₄
  · rw [hcast, hcast, hcast]
    exact_mod_cast hd₅

end CFSG.Semidihedral.Principal
