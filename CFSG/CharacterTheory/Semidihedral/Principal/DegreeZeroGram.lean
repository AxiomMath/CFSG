module

public import CFSG.CharacterTheory.Blocks.NormTwoGram

public noncomputable section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators

theorem int_eq_neg_one_or_zero_or_one_of_mul_self_le_three {z : ℤ} (h : z * z ≤ 3) :
    z = -1 ∨ z = 0 ∨ z = 1 := by
  have hlower : -1 ≤ z := by nlinarith
  have hupper : z ≤ 1 := by nlinarith
  omega

theorem small_norm_support {L : Type*} (T : Finset L) (a : L → ℤ) {n : ℕ} (hn : n ≤ 3)
    (hnorm : ∑ x ∈ T, a x * a x = n) :
    ∃ N : Finset L, N ⊆ T ∧ N.card = n ∧ (∀ x ∈ N, a x = 1 ∨ a x = -1) ∧
      ∀ x ∈ T, x ∉ N → a x = 0 := by
  have hsmall : ∀ x ∈ T, a x = -1 ∨ a x = 0 ∨ a x = 1 := by
    intro x hx
    apply int_eq_neg_one_or_zero_or_one_of_mul_self_le_three
    have hle : a x * a x ≤ ∑ y ∈ T, a y * a y :=
      Finset.single_le_sum (f := fun y => a y * a y) (fun y _ => mul_self_nonneg (a y)) hx
    omega
  refine ⟨T.filter (fun x => a x ≠ 0), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · have hcard : ((T.filter (fun x => a x ≠ 0)).card : ℤ) = ∑ x ∈ T, a x * a x := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rcases hsmall x hx with h | h | h <;> simp [h]
    omega
  · intro x hx
    obtain ⟨hxT, hx0⟩ := Finset.mem_filter.mp hx
    rcases hsmall x hxT with h | h | h
    · exact Or.inr h
    · exact absurd h hx0
    · exact Or.inl h
  · intro x hx hxN
    by_contra hne
    exact hxN (Finset.mem_filter.mpr ⟨hx, hne⟩)

theorem principal_small_norm_support {L : Type*} [DecidableEq L] (S : Finset L) {p : L}
    (hp : p ∈ S) (a : L → ℤ) (hap : a p = 1) {n : ℕ} (hn : n ≤ 3)
    (hnorm : ∑ x ∈ S, a x * a x = 1 + n) :
    ∃ N : Finset L, N ⊆ S.erase p ∧ N.card = n ∧ (∀ x ∈ N, a x = 1 ∨ a x = -1) ∧
      ∀ x ∈ S, x ≠ p → x ∉ N → a x = 0 := by
  have herase : ∑ x ∈ S.erase p, a x * a x = n := by
    have h := Finset.sum_erase_add S (fun x => a x * a x) hp
    rw [hnorm, hap] at h
    linarith
  obtain ⟨N, hNT, hcard, hsign, hout⟩ := small_norm_support (S.erase p) a hn herase
  exact ⟨N, hNT, hcard, hsign, fun x hx hxp hxN => hout x (Finset.mem_erase.mpr ⟨hxp, hx⟩) hxN⟩

theorem sum_mul_two_labels {L : Type*} [DecidableEq L] (S : Finset L) (v : L → ℤ) {y s : L}
    (hy : y ∈ S) (hs : s ∈ S) (b c : ℤ) :
    ∑ x ∈ S, v x * (b * (if x = y then 1 else 0) + c * (if x = s then 1 else 0)) =
      b * v y + c * v s := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    hy, hs, ite_true]
  ring

theorem sum_mul_three_labels {L : Type*} [DecidableEq L] (S : Finset L) (v : L → ℤ)
    {p y s : L} (hp : p ∈ S) (hy : y ∈ S) (hs : s ∈ S) (a b c : ℤ) :
    ∑ x ∈ S, v x * (a * (if x = p then 1 else 0) + b * (if x = y then 1 else 0) +
      c * (if x = s then 1 else 0)) = a * v p + b * v y + c * v s := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    hp, hy, hs, ite_true]
  ring

theorem principal_norm_three_meets_support {L : Type*} [DecidableEq L] (S : Finset L) {p : L}
    (hp : p ∈ S) (θ a : L → ℤ) (hθp : θ p = 1) (N : Finset L)
    (hθN : ∀ x ∈ N, θ x = 1 ∨ θ x = -1) (hθout : ∀ x ∈ S, x ≠ p → x ∉ N → θ x = 0)
    (hap : a p = 1) (hnorm : ∑ x ∈ S, a x * a x = 3) (hcross : ∑ x ∈ S, θ x * a x = 2) :
    ∃ y ∈ N, ∃ s ∈ S, s ≠ p ∧ s ∉ N ∧ a y = θ y ∧ (a s = 1 ∨ a s = -1) ∧
      ∀ x ∈ S, x ≠ p → x ≠ y → x ≠ s → a x = 0 := by
  obtain ⟨M, hMS, hMcard, hMsign, hMout⟩ :=
    principal_small_norm_support S hp a hap (n := 2) (by norm_num) (by rw [hnorm]; norm_num)
  obtain ⟨m₁, m₂, hm, rfl⟩ := Finset.card_eq_two.mp hMcard
  have hm₁ : m₁ ∈ S.erase p := hMS (by simp)
  have hm₂ : m₂ ∈ S.erase p := hMS (by simp)
  have hsign₁ := hMsign m₁ (by simp)
  have hsign₂ := hMsign m₂ (by simp)
  have hθsmall : ∀ x ∈ S.erase p, θ x = -1 ∨ θ x = 0 ∨ θ x = 1 := by
    intro x hx
    by_cases hxN : x ∈ N
    · rcases hθN x hxN with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · exact Or.inr (Or.inl
        (hθout x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) hxN))
  have hsum : θ m₁ * a m₁ + θ m₂ * a m₂ = 1 := by
    have h := Finset.sum_erase_add S (fun x => θ x * a x) hp
    have hpair := Finset.sum_subset hMS (f := fun x => θ x * a x) (fun x hx hxM => by
      rw [hMout x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) hxM, mul_zero])
    rw [Finset.sum_pair hm] at hpair
    rw [hcross, hθp, hap, ← hpair] at h
    linarith
  have hθ₁ := hθsmall m₁ hm₁
  have hθ₂ := hθsmall m₂ hm₂
  have hkey : (θ m₁ = 0 ∧ θ m₂ = a m₂) ∨ (θ m₂ = 0 ∧ θ m₁ = a m₁) := by
    rcases hsign₁ with h₁ | h₁ <;> rcases hsign₂ with h₂ | h₂ <;>
      simp only [h₁, h₂] at hsum ⊢ <;> omega
  have hmemN : ∀ x ∈ S.erase p, θ x ≠ 0 → x ∈ N := by
    intro x hx hθx
    by_contra hxN
    exact hθx (hθout x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) hxN)
  have hnotN : ∀ x, θ x = 0 → x ∉ N := by
    intro x hθx hxN
    rcases hθN x hxN with h | h <;> omega
  rcases hkey with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨m₂, hmemN m₂ hm₂ (by rcases hsign₂ with h | h <;> omega), m₁,
      Finset.mem_of_mem_erase hm₁, Finset.ne_of_mem_erase hm₁, hnotN m₁ h₁, h₂.symm, hsign₁, ?_⟩
    intro x hx hxp hxy hxs
    exact hMout x hx hxp (by simp [hxy, hxs])
  · refine ⟨m₁, hmemN m₁ hm₁ (by rcases hsign₁ with h | h <;> omega), m₂,
      Finset.mem_of_mem_erase hm₂, Finset.ne_of_mem_erase hm₂, hnotN m₂ h₁, h₂.symm, hsign₂, ?_⟩
    intro x hx hxp hxy hxs
    exact hMout x hx hxp (by simp [hxy, hxs])

theorem principal_degree_zero_gram_common_constituents_coordinates
    {L J : Type*} [DecidableEq L] [Fintype J] [DecidableEq J] (hJ : Fintype.card J ≠ 2)
    (S : Finset L) {p : L} (hp : p ∈ S) (deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x)
    (hdegp : deg p = 1) (θ : L → ℤ) (e : J → L → ℤ)
    (hθdeg : ∑ x ∈ S, θ x * deg x = 0) (hedeg : ∀ j, ∑ x ∈ S, e j x * deg x = 0)
    (hθp : θ p = 1) (hep : ∀ j, e j p = 1) (hθθ : ∑ x ∈ S, θ x * θ x = 4)
    (hθe : ∀ j, ∑ x ∈ S, θ x * e j x = 2)
    (hee : ∀ j l, ∑ x ∈ S, e j x * e l x = 2 + if j = l then 1 else 0) :
    ∃ (c₁ c₂ c₃ : L) (δ₁ δ₂ δ₃ ε : ℤ) (s : J → L),
      c₁ ∈ S ∧ c₂ ∈ S ∧ c₃ ∈ S ∧ c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      c₁ ≠ p ∧ c₂ ≠ p ∧ c₃ ≠ p ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      Function.Injective s ∧ (∀ j, s j ∈ S ∧ s j ≠ p ∧ s j ≠ c₁ ∧ s j ≠ c₂ ∧ s j ≠ c₃) ∧
      (∀ x ∈ S, θ x = (if x = p then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
        δ₂ * (if x = c₂ then 1 else 0) + δ₃ * (if x = c₃ then 1 else 0)) ∧
      (∀ j, ∀ x ∈ S, e j x = (if x = p then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
        ε * (if x = s j then 1 else 0)) ∧
      (Nonempty J → 1 + δ₁ * deg c₁ ≠ 0 ∧ (∀ j, deg (s j) = |1 + δ₁ * deg c₁|) ∧
        ε = -Int.sign (1 + δ₁ * deg c₁)) := by
  obtain ⟨N, hNS, hNcard, hθN, hθout⟩ :=
    principal_small_norm_support S hp θ hθp (n := 3) le_rfl (by rw [hθθ]; norm_num)
  choose y hyN s hsS hsp hsN hey hes hevanish using fun j =>
    principal_norm_three_meets_support S hp θ (e j) hθp N hθN hθout (hep j)
      (by simpa using hee j j) (hθe j)
  have hyS : ∀ j, y j ∈ S := fun j => Finset.mem_of_mem_erase (hNS (hyN j))
  have hyp : ∀ j, y j ≠ p := fun j => Finset.ne_of_mem_erase (hNS (hyN j))
  have hys : ∀ j l, y j ≠ s l := fun j l h => hsN l (h ▸ hyN j)
  have hθy : ∀ j, θ (y j) = 1 ∨ θ (y j) = -1 := fun j => hθN _ (hyN j)
  have heform : ∀ j, ∀ x ∈ S, e j x = 1 * (if x = p then 1 else 0) +
      θ (y j) * (if x = y j then 1 else 0) + e j (s j) * (if x = s j then 1 else 0) := by
    intro j x hx
    by_cases hxp : x = p
    · rw [hxp, ite_eq_left rfl, ite_eq_right (hyp j).symm, ite_eq_right (hsp j).symm, hep j]
      ring
    by_cases hxy : x = y j
    · rw [hxy, ite_eq_right (hyp j), ite_eq_left rfl, ite_eq_right (hys j j), hey j]
      ring
    by_cases hxs : x = s j
    · rw [hxs, ite_eq_right (hsp j), ite_eq_right (hys j j).symm, ite_eq_left rfl]
      ring
    · rw [ite_eq_right hxp, ite_eq_right hxy, ite_eq_right hxs, hevanish j x hx hxp hxy hxs]
      ring
  have hpair : ∀ j l, j ≠ l →
      θ (y l) * (θ (y j) * (if y l = y j then 1 else 0)) +
        e l (s l) * (e j (s j) * (if s l = s j then 1 else 0)) = 1 := by
    intro j l hjl
    have h := hee j l
    have hform : ∑ x ∈ S, e j x * e l x = ∑ x ∈ S, e j x * (1 * (if x = p then 1 else 0) +
        θ (y l) * (if x = y l then 1 else 0) + e l (s l) * (if x = s l then 1 else 0)) :=
      Finset.sum_congr rfl fun x hx => by rw [heform l x hx]
    have hyl : e j (y l) = θ (y j) * (if y l = y j then 1 else 0) := by
      rw [heform j (y l) (hyS l), ite_eq_right (hyp l), ite_eq_right (hys l j)]
      ring
    have hsl : e j (s l) = e j (s j) * (if s l = s j then 1 else 0) := by
      rw [heform j (s l) (hsS l), ite_eq_right (hsp l), ite_eq_right (hys j l).symm]
      ring
    rw [hform, sum_mul_three_labels S (e j) hp (hyS l) (hsS l), hep j, hyl, hsl,
      ite_eq_right hjl] at h
    linarith
  have hsame : ∀ j l, j ≠ l → y j = y l → s j ≠ s l := by
    intro j l hjl hy hs
    have h := hpair j l hjl
    rw [ite_eq_left hy.symm, ite_eq_left hs.symm, hy, mul_one, mul_one] at h
    rcases hθy l with h₁ | h₁ <;> rcases hes j with h₂ | h₂ <;> rcases hes l with h₃ | h₃ <;>
      rw [h₁, h₂, h₃] at h <;> omega
  have hdiff : ∀ j l, j ≠ l → y j ≠ y l → s j = s l ∧ e j (s j) = e l (s l) := by
    intro j l hjl hy
    have h := hpair j l hjl
    rw [ite_eq_right (Ne.symm hy), mul_zero, mul_zero, zero_add] at h
    by_cases hs : s l = s j
    · rw [ite_eq_left hs, mul_one] at h
      refine ⟨hs.symm, ?_⟩
      rcases hes j with h₂ | h₂ <;> rcases hes l with h₃ | h₃ <;> rw [h₂, h₃] at h ⊢ <;> omega
    · rw [ite_eq_right hs, mul_zero, mul_zero] at h
      omega
  have hedeg' : ∀ j, 1 + θ (y j) * deg (y j) + e j (s j) * deg (s j) = 0 := by
    intro j
    have h := hedeg j
    have hform : ∑ x ∈ S, e j x * deg x = ∑ x ∈ S, deg x * (1 * (if x = p then 1 else 0) +
        θ (y j) * (if x = y j then 1 else 0) + e j (s j) * (if x = s j then 1 else 0)) :=
      Finset.sum_congr rfl fun x hx => by rw [heform j x hx]; ring
    rw [hform, sum_mul_three_labels S deg hp (hyS j) (hsS j), hdegp] at h
    linarith
  have hθdeg' : 1 + ∑ x ∈ N, θ x * deg x = 0 := by
    have h := Finset.sum_erase_add S (fun x => θ x * deg x) hp
    have hN' := Finset.sum_subset hNS (f := fun x => θ x * deg x) (fun x hx hxN => by
      rw [hθout x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) hxN, zero_mul])
    rw [hθdeg, hθp, hdegp, ← hN'] at h
    linarith
  have hcommon : ∀ j l, y j = y l := by
    intro j l
    by_contra hjl
    have hjl' : j ≠ l := fun h => hjl (congrArg y h)
    obtain ⟨h, hhj, hhl⟩ : ∃ h, h ≠ j ∧ h ≠ l := by
      by_contra hno
      push Not at hno
      apply hJ
      have hsub : (Finset.univ : Finset J) ⊆ {j, l} := by
        intro h _
        by_cases hhj : h = j
        · simp [hhj]
        · simp [hno h hhj]
      have h₁ : Fintype.card J ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
      have h₂ : 2 ≤ Fintype.card J := by
        rw [← Finset.card_pair hjl']
        exact Finset.card_le_univ _
      omega
    obtain ⟨hs_jl, he_jl⟩ := hdiff j l hjl' hjl
    have hyhj : y h ≠ y j := by
      intro hyeq
      have hhl' : y h ≠ y l := fun h' => hjl (hyeq.symm.trans h')
      exact hsame h j hhj hyeq ((hdiff h l hhl hhl').1.trans hs_jl.symm)
    have hyhl : y h ≠ y l := by
      intro hyeq
      have hhj' : y h ≠ y j := fun h' => hjl (h'.symm.trans hyeq)
      exact hsame h l hhl hyeq ((hdiff h j hhj hhj').1.trans hs_jl)
    obtain ⟨hs_hj, he_hj⟩ := hdiff h j hhj hyhj
    have hcard3 : ({y j, y l, y h} : Finset L).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hyhl)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hjl, fun h' => hyhj h'.symm⟩
    have hNeq : N = {y j, y l, y h} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hyN j
        · exact hyN l
        · exact hyN h
      · exact (hNcard.trans hcard3.symm).le
    rw [hNeq, Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hjl, fun h' => hyhj h'.symm⟩),
      Finset.sum_pair (Ne.symm hyhl)] at hθdeg'
    have hj := hedeg' j
    have hl := hedeg' l
    have hh := hedeg' h
    rw [← he_jl, ← hs_jl] at hl
    rw [he_hj, hs_hj] at hh
    have key : 3 * (e j (s j) * deg (s j)) = -2 := by linarith
    rcases hes j with hE | hE <;> rw [hE] at key <;> omega
  obtain ⟨c₁, hc₁N, hyc₁⟩ : ∃ c₁ ∈ N, ∀ j, y j = c₁ := by
    rcases isEmpty_or_nonempty J with hJe | ⟨⟨j₀⟩⟩
    · obtain ⟨c, hc⟩ := Finset.card_pos.mp (by rw [hNcard]; norm_num : 0 < N.card)
      exact ⟨c, hc, fun j => (hJe.false j).elim⟩
    · exact ⟨y j₀, hyN j₀, fun j => hcommon j j₀⟩
  have hcard2 : (N.erase c₁).card = 2 := by rw [Finset.card_erase_of_mem hc₁N, hNcard]
  obtain ⟨c₂, c₃, h23, hpair23⟩ := Finset.card_eq_two.mp hcard2
  have hc₂ : c₂ ∈ N.erase c₁ := by rw [hpair23]; simp
  have hc₃ : c₃ ∈ N.erase c₁ := by rw [hpair23]; simp
  have hc₂N := Finset.mem_of_mem_erase hc₂
  have hc₃N := Finset.mem_of_mem_erase hc₃
  have h21 : c₂ ≠ c₁ := Finset.ne_of_mem_erase hc₂
  have h31 : c₃ ≠ c₁ := Finset.ne_of_mem_erase hc₃
  have hNmem : ∀ x ∈ N, x = c₁ ∨ x = c₂ ∨ x = c₃ := by
    intro x hx
    by_cases hx1 : x = c₁
    · exact Or.inl hx1
    · have hxe : x ∈ N.erase c₁ := Finset.mem_erase.mpr ⟨hx1, hx⟩
      rw [hpair23] at hxe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      exact Or.inr hxe
  have hNS' : ∀ x ∈ N, x ∈ S ∧ x ≠ p := fun x hx =>
    ⟨Finset.mem_of_mem_erase (hNS hx), Finset.ne_of_mem_erase (hNS hx)⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ,
      ε = if 1 + θ c₁ * deg c₁ = 0 then 1 else -Int.sign (1 + θ c₁ * deg c₁) :=
    ⟨_, rfl⟩
  have hεsign : ε = 1 ∨ ε = -1 := by
    rw [hε]
    split_ifs with h0
    · exact Or.inl rfl
    · rcases lt_or_gt_of_ne h0 with hneg | hpos
      · exact Or.inl (by rw [Int.sign_eq_neg_one_of_neg hneg, neg_neg])
      · exact Or.inr (by rw [Int.sign_eq_one_of_pos hpos])
  have hεj : ∀ j, e j (s j) = ε ∧ 1 + θ c₁ * deg c₁ ≠ 0 ∧
      deg (s j) = |1 + θ c₁ * deg c₁| := by
    intro j
    have h := hedeg' j
    rw [hyc₁ j] at h
    have hD := hdeg (s j) (hsS j)
    rcases hes j with hE | hE
    · rw [hE] at h
      have hneg : 1 + θ c₁ * deg c₁ < 0 := by linarith
      refine ⟨?_, hneg.ne, ?_⟩
      · rw [hE, hε, ite_eq_right hneg.ne, Int.sign_eq_neg_one_of_neg hneg, neg_neg]
      · rw [abs_of_neg hneg]
        linarith
    · rw [hE] at h
      have hpos : 0 < 1 + θ c₁ * deg c₁ := by linarith
      refine ⟨?_, hpos.ne', ?_⟩
      · rw [hE, hε, ite_eq_right hpos.ne', Int.sign_eq_one_of_pos hpos]
      · rw [abs_of_pos hpos]
        linarith
  have hsinj : Function.Injective s := by
    intro j l hjl
    by_contra hne
    exact hsame j l hne ((hyc₁ j).trans (hyc₁ l).symm) hjl
  have hθform : ∀ x ∈ S, θ x = (if x = p then 1 else 0) + θ c₁ * (if x = c₁ then 1 else 0) +
      θ c₂ * (if x = c₂ then 1 else 0) + θ c₃ * (if x = c₃ then 1 else 0) := by
    intro x hx
    by_cases hxp : x = p
    · rw [hxp, ite_eq_left rfl, ite_eq_right (hNS' c₁ hc₁N).2.symm,
        ite_eq_right (hNS' c₂ hc₂N).2.symm, ite_eq_right (hNS' c₃ hc₃N).2.symm, hθp]
      ring
    by_cases hx1 : x = c₁
    · rw [hx1, ite_eq_right (hNS' c₁ hc₁N).2, ite_eq_left rfl, ite_eq_right h21.symm,
        ite_eq_right h31.symm]
      ring
    by_cases hx2 : x = c₂
    · rw [hx2, ite_eq_right (hNS' c₂ hc₂N).2, ite_eq_right h21, ite_eq_left rfl, ite_eq_right h23]
      ring
    by_cases hx3 : x = c₃
    · rw [hx3, ite_eq_right (hNS' c₃ hc₃N).2, ite_eq_right h31, ite_eq_right h23.symm,
        ite_eq_left rfl]
      ring
    · have hxN : x ∉ N := fun hxN => by
        rcases hNmem x hxN with h | h | h
        · exact hx1 h
        · exact hx2 h
        · exact hx3 h
      rw [ite_eq_right hxp, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hx3,
        hθout x hx hxp hxN]
      ring
  refine ⟨c₁, c₂, c₃, θ c₁, θ c₂, θ c₃, ε, s, (hNS' c₁ hc₁N).1, (hNS' c₂ hc₂N).1,
    (hNS' c₃ hc₃N).1, h21.symm, h31.symm, h23, (hNS' c₁ hc₁N).2, (hNS' c₂ hc₂N).2,
    (hNS' c₃ hc₃N).2, hθN c₁ hc₁N, hθN c₂ hc₂N, hθN c₃ hc₃N, hεsign, hsinj,
    fun j => ⟨hsS j, hsp j, fun h => hsN j (h ▸ hc₁N), fun h => hsN j (h ▸ hc₂N),
      fun h => hsN j (h ▸ hc₃N)⟩, hθform, fun j x hx => ?_, fun ⟨j₀⟩ =>
      ⟨(hεj j₀).2.1, fun j => (hεj j).2.2, by rw [hε, ite_eq_right (hεj j₀).2.1]⟩⟩
  rw [heform j x hx, hyc₁ j, (hεj j).1]
  ring

theorem principal_mem_blocksIrr (G : Type) [Group G] : (1 : G → ℂ) ∈ BlocksIrr G := by
  rw [blocksIrr_eq_irreducible_characters]
  exact ⟨principalFiniteComplexRepresentation G,
    principalFiniteComplexRepresentation_isIrreducible G,
    principalFiniteComplexRepresentation_character G⟩

theorem blocksIrr_degree_eq_natCast {G : Type} [Group G] (χ : BlocksIrr G) :
    ∃ d : ℕ, 0 < d ∧ (χ : G → ℂ) 1 = d := by
  obtain ⟨ρ, hρ, hρχ⟩ :=
    (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (χ : G → ℂ)).mp χ.property
  refine ⟨Module.finrank ℂ ρ.vector, Nat.pos_of_ne_zero fun hzero => ?_, ?_⟩
  · apply irreducible_character_degree_ne_zero ρ hρ
    rw [FiniteComplexRepresentation.character, Representation.char_one, hzero, Nat.cast_zero]
  · rw [← hρχ, FiniteComplexRepresentation.character, Representation.char_one]

theorem blocksCharacterExpansion_single {G : Type} [Group G] (χ : BlocksIrr G) (b : ℤ) :
    blocksCharacterExpansion G (Finsupp.single χ b) = (b : ℂ) • (χ : G → ℂ) := by
  rw [blocksCharacterExpansion, Finsupp.linearCombination_single]
  exact (Int.cast_smul_eq_zsmul ℂ b _).symm

theorem blocksVChar_principal_degree_zero_gram_common_constituents
    {G : Type} {J : Type*} [Group G] [Fintype G] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J ≠ 2) {Θ : G → ℂ} {E : J → G → ℂ} (hΘ : Θ ∈ BlocksVChar G)
    (hE : ∀ j, E j ∈ BlocksVChar G) (hΘdegree : Θ 1 = 0) (hEdegree : ∀ j, E j 1 = 0)
    (hΘprincipal : BlocksInnerProduct Θ 1 = 1)
    (hEprincipal : ∀ j, BlocksInnerProduct (E j) 1 = 1)
    (hΘnorm : BlocksInnerProduct Θ Θ = 4) (hΘE : ∀ j, BlocksInnerProduct Θ (E j) = 2)
    (hEgram : ∀ j l, BlocksInnerProduct (E j) (E l) = 2 + if j = l then 1 else 0) :
    ∃ (χ₁ χ₂ χ₃ : BlocksIrr G) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : J → BlocksIrr G),
      χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      Function.Injective ψ ∧
      (∀ j, (ψ j : G → ℂ) ≠ 1 ∧ ψ j ≠ χ₁ ∧ ψ j ≠ χ₂ ∧ ψ j ≠ χ₃) ∧
      Θ = 1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (δ₂ : ℂ) • (χ₂ : G → ℂ) + (δ₃ : ℂ) • (χ₃ : G → ℂ) ∧
      (∀ j, E j = 1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (ε : ℂ) • (ψ j : G → ℂ)) ∧
      (Nonempty J →
        1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1 ≠ 0 ∧
        (∀ j, (ψ j : G → ℂ) 1 = ‖1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1‖) ∧
        ε = -SignType.sign (1 + (δ₁ : ℂ) * (χ₁ : G → ℂ) 1).re) := by
  classical
  obtain ⟨nΘ, hnΘ, -⟩ := blocksVChar_exists_unique_expansion hΘ
  choose nE hnE _ using fun j => blocksVChar_exists_unique_expansion (hE j)
  let p : BlocksIrr G := ⟨1, principal_mem_blocksIrr G⟩
  choose d hdpos hdval using fun χ : BlocksIrr G => blocksIrr_degree_eq_natCast χ
  let S : Finset (BlocksIrr G) :=
    insert p (nΘ.support ∪ Finset.univ.biUnion fun j => (nE j).support)
  have hpS : p ∈ S := Finset.mem_insert_self _ _
  have hΘS : nΘ.support ⊆ S := fun χ hχ =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ hχ)
  have hES : ∀ j, (nE j).support ⊆ S := fun j χ hχ =>
    Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hχ⟩))
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
  have hθdeg : ∑ x ∈ S, nΘ x * (d x : ℤ) = 0 := by
    have h := hdegsum nΘ hΘS
    rw [hnΘ, hΘdegree] at h
    exact_mod_cast h.symm
  have hedeg : ∀ j, ∑ x ∈ S, nE j x * (d x : ℤ) = 0 := fun j => by
    have h := hdegsum (nE j) (hES j)
    rw [hnE j, hEdegree j] at h
    exact_mod_cast h.symm
  have hθp : nΘ p = 1 := by
    have h := blocksInnerProduct_expansion_coefficient nΘ p
    rw [hnΘ] at h
    change BlocksInnerProduct Θ 1 = _ at h
    rw [hΘprincipal] at h
    exact_mod_cast h.symm
  have hep : ∀ j, nE j p = 1 := fun j => by
    have h := blocksInnerProduct_expansion_coefficient (nE j) p
    rw [hnE j] at h
    change BlocksInnerProduct (E j) 1 = _ at h
    rw [hEprincipal j] at h
    exact_mod_cast h.symm
  have hθθ : ∑ x ∈ S, nΘ x * nΘ x = 4 := by
    have h := hdot nΘ nΘ hΘS
    rw [hnΘ, hΘnorm] at h
    exact_mod_cast h.symm
  have hθe : ∀ j, ∑ x ∈ S, nΘ x * nE j x = 2 := fun j => by
    have h := hdot nΘ (nE j) (hES j)
    rw [hnΘ, hnE j, hΘE j] at h
    exact_mod_cast h.symm
  have hee : ∀ j l, ∑ x ∈ S, nE j x * nE l x = 2 + if j = l then 1 else 0 := fun j l => by
    have h := hdot (nE j) (nE l) (hES l)
    rw [hnE j, hnE l, hEgram j l] at h
    by_cases hjl : j = l
    · rw [ite_eq_left hjl] at h ⊢
      exact_mod_cast h.symm
    · rw [ite_eq_right hjl] at h ⊢
      exact_mod_cast h.symm
  obtain ⟨c₁, c₂, c₃, δ₁, δ₂, δ₃, ε, s, hc₁S, hc₂S, hc₃S, h12, h13, h23, hc₁p, hc₂p, hc₃p,
      hδ₁, hδ₂, hδ₃, hε, hsinj, hsavoid, hθform, heform, hdegrees⟩ :=
    principal_degree_zero_gram_common_constituents_coordinates hJ S hpS (fun χ => (d χ : ℤ))
      (fun χ _ => by exact_mod_cast hdpos χ) hdegp nΘ (fun j => nE j) hθdeg hedeg hθp hep hθθ
      hθe hee
  have hsingle : ∀ (a x : BlocksIrr G) (b : ℤ),
      Finsupp.single a b x = b * (if x = a then 1 else 0) := by
    intro a x b
    rw [Finsupp.single_apply]
    by_cases h : x = a
    · rw [ite_eq_left h.symm, ite_eq_left h, mul_one]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]
  have hnotS : ∀ x, x ∉ S → x ≠ p ∧ x ≠ c₁ ∧ x ≠ c₂ ∧ x ≠ c₃ := fun x hx =>
    ⟨fun h => hx (h ▸ hpS), fun h => hx (h ▸ hc₁S), fun h => hx (h ▸ hc₂S),
      fun h => hx (h ▸ hc₃S)⟩
  have hnΘform : nΘ = Finsupp.single p 1 + Finsupp.single c₁ δ₁ + Finsupp.single c₂ δ₂ +
      Finsupp.single c₃ δ₃ := by
    ext x
    simp only [Finsupp.add_apply, hsingle]
    by_cases hx : x ∈ S
    · rw [hθform x hx]
      ring
    · obtain ⟨hxp, hx1, hx2, hx3⟩ := hnotS x hx
      rw [Finsupp.notMem_support_iff.mp fun h => hx (hΘS h), ite_eq_right hxp, ite_eq_right hx1,
        ite_eq_right hx2, ite_eq_right hx3]
      ring
  have hnEform : ∀ j, nE j = Finsupp.single p 1 + Finsupp.single c₁ δ₁ +
      Finsupp.single (s j) ε := by
    intro j
    ext x
    simp only [Finsupp.add_apply, hsingle]
    by_cases hx : x ∈ S
    · rw [heform j x hx]
      ring
    · obtain ⟨hxp, hx1, -, -⟩ := hnotS x hx
      have hxs : x ≠ s j := fun h => hx (h ▸ (hsavoid j).1)
      rw [Finsupp.notMem_support_iff.mp fun h => hx (hES j h), ite_eq_right hxp, ite_eq_right hx1,
        ite_eq_right hxs]
      ring
  have hp1 : ((1 : ℤ) : ℂ) • (p : G → ℂ) = 1 := by
    rw [Int.cast_one, one_smul]
  have hne1 : ∀ χ : BlocksIrr G, χ ≠ p → (χ : G → ℂ) ≠ 1 := fun χ hχ h =>
    hχ (Subtype.ext h)
  refine ⟨c₁, c₂, c₃, δ₁, δ₂, δ₃, ε, s, h12, h13, h23, hne1 c₁ hc₁p, hne1 c₂ hc₂p,
    hne1 c₃ hc₃p, hδ₁, hδ₂, hδ₃, hε, hsinj,
    fun j => ⟨hne1 (s j) (hsavoid j).2.1, (hsavoid j).2.2.1, (hsavoid j).2.2.2.1,
      (hsavoid j).2.2.2.2⟩, ?_, fun j => ?_, fun hJne => ?_⟩
  · rw [← hnΘ, hnΘform, map_add, map_add, map_add, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, hp1]
  · rw [← hnE j, hnEform j, map_add, map_add, blocksCharacterExpansion_single,
      blocksCharacterExpansion_single, blocksCharacterExpansion_single, hp1]
  · obtain ⟨hw, hψdeg, hεw⟩ := hdegrees hJne
    have hvalue : 1 + (δ₁ : ℂ) * (c₁ : G → ℂ) 1 = ((1 + δ₁ * (d c₁ : ℤ) : ℤ) : ℂ) := by
      rw [hdval c₁]
      push_cast
      ring
    refine ⟨?_, fun j => ?_, ?_⟩
    · rw [hvalue]
      exact_mod_cast hw
    · rw [hvalue, Complex.norm_intCast, ← Int.cast_abs, ← hψdeg j, hdval (s j)]
      push_cast
      rfl
    · rw [hvalue, Complex.intCast_re, sign_intCast, hεw, Int.sign_eq_sign]

theorem degree_zero_norm_two_coordinates {L : Type*} [DecidableEq L] (S : Finset L)
    (deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x) (a : L → ℤ) (hnorm : ∑ x ∈ S, a x * a x = 2)
    (hdegree : ∑ x ∈ S, a x * deg x = 0) :
    ∃ A ∈ S, ∃ B ∈ S, A ≠ B ∧ deg A = deg B ∧
      ∀ x ∈ S, a x = (if x = A then 1 else 0) - (if x = B then 1 else 0) := by
  obtain ⟨M, hMS, hMcard, hMsign, hMout⟩ :=
    small_norm_support S a (n := 2) (by norm_num) (by rw [hnorm]; norm_num)
  obtain ⟨m₁, m₂, hm, rfl⟩ := Finset.card_eq_two.mp hMcard
  have hm₁ : m₁ ∈ S := hMS (by simp)
  have hm₂ : m₂ ∈ S := hMS (by simp)
  have hform : ∀ x ∈ S, a x = a m₁ * (if x = m₁ then 1 else 0) +
      a m₂ * (if x = m₂ then 1 else 0) := by
    intro x hx
    by_cases h₁ : x = m₁
    · rw [h₁, ite_eq_left rfl, ite_eq_right hm]
      ring
    by_cases h₂ : x = m₂
    · rw [h₂, ite_eq_right (Ne.symm hm), ite_eq_left rfl]
      ring
    · rw [ite_eq_right h₁, ite_eq_right h₂, hMout x hx (by simp [h₁, h₂])]
      ring
  have hdeg₂ : a m₁ * deg m₁ + a m₂ * deg m₂ = 0 := by
    have h : ∑ x ∈ S, a x * deg x = ∑ x ∈ S, deg x * (a m₁ * (if x = m₁ then 1 else 0) +
        a m₂ * (if x = m₂ then 1 else 0)) :=
      Finset.sum_congr rfl fun x hx => by rw [hform x hx]; ring
    rw [h, sum_mul_two_labels S deg hm₁ hm₂] at hdegree
    linarith
  have hd₁ := hdeg m₁ hm₁
  have hd₂ := hdeg m₂ hm₂
  rcases hMsign m₁ (by simp) with h₁ | h₁ <;> rcases hMsign m₂ (by simp) with h₂ | h₂
  · rw [h₁, h₂] at hdeg₂
    linarith
  · refine ⟨m₁, hm₁, m₂, hm₂, hm, by rw [h₁, h₂] at hdeg₂; linarith, fun x hx => ?_⟩
    rw [hform x hx, h₁, h₂]
    ring
  · refine ⟨m₂, hm₂, m₁, hm₁, Ne.symm hm, by rw [h₁, h₂] at hdeg₂; linarith, fun x hx => ?_⟩
    rw [hform x hx, h₁, h₂]
    ring
  · rw [h₁, h₂] at hdeg₂
    linarith

theorem degree_zero_difference_star_coordinates
    {L I : Type*} [DecidableEq L] [Fintype I] [DecidableEq I] (zero : I)
    (hI : 3 ≤ Fintype.card I) (S : Finset L) (deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x)
    (f : I → L → ℤ) (hzero : ∀ x ∈ S, f zero x = 0)
    (hdegree : ∀ i, ∑ x ∈ S, f i x * deg x = 0)
    (hgram : ∀ i k, i ≠ zero → k ≠ zero →
      ∑ x ∈ S, f i x * f k x = 1 + if i = k then 1 else 0) :
    ∃ (ε : ℤ) (ν : I → L), (ε = 1 ∨ ε = -1) ∧ Function.Injective ν ∧ (∀ i, ν i ∈ S) ∧
      (∀ i k, deg (ν i) = deg (ν k)) ∧
      ∀ i, ∀ x ∈ S, f i x = ε * ((if x = ν i then 1 else 0) - (if x = ν zero then 1 else 0)) := by
  obtain ⟨other, hother⟩ : ∃ i : I, i ≠ zero := by
    by_contra hall
    push Not at hall
    have hle : Fintype.card I ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
    omega
  have : Nonempty {i : I // i ≠ zero} := ⟨⟨other, hother⟩⟩
  choose A hAS B hBS hAB hdegAB hform using fun i : {i : I // i ≠ zero} =>
    degree_zero_norm_two_coordinates S deg hdeg (f i)
      (by simpa using hgram i i i.property i.property) (hdegree i)
  have hshare : ∀ i k : {i : I // i ≠ zero}, i ≠ k → A i = A k ∨ B i = B k := by
    intro i k hik
    have hik' : (i : I) ≠ k := fun h => hik (Subtype.ext h)
    have h := hgram i k i.property k.property
    have hsum : ∑ x ∈ S, f i x * f k x = ∑ x ∈ S, f i x * (1 * (if x = A k then 1 else 0) +
        (-1) * (if x = B k then 1 else 0)) :=
      Finset.sum_congr rfl fun x hx => by rw [hform k x hx]; ring
    rw [hsum, sum_mul_two_labels S (f i) (hAS k) (hBS k), hform i (A k) (hAS k),
      hform i (B k) (hBS k), ite_eq_right hik'] at h
    by_contra hcon
    push Not at hcon
    rw [ite_eq_right (Ne.symm hcon.1), ite_eq_right (Ne.symm hcon.2)] at h
    split_ifs at h <;> omega
  obtain ⟨ε, hε, c, hcS, ν', hν'S, hν'c, hdegν', hformν'⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ c ∈ S, ∃ ν' : {i : I // i ≠ zero} → L, (∀ i, ν' i ∈ S) ∧ (∀ i, ν' i ≠ c) ∧
        (∀ i, deg (ν' i) = deg c) ∧ ∀ i : {i : I // i ≠ zero}, ∀ x ∈ S,
          f i x = ε * ((if x = ν' i then 1 else 0) - (if x = c then 1 else 0)) := by
    rcases pairwise_shared_pairs_have_common_coordinate A B hshare with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨-1, Or.inr rfl, c, hc ⟨other, hother⟩ ▸ hAS ⟨other, hother⟩, B, hBS,
        fun i h => hAB i ((hc i).trans h.symm), fun i => (hdegAB i).symm.trans (by rw [hc i]),
        fun i x hx => ?_⟩
      rw [hform i x hx, hc i]
      ring
    · refine ⟨1, Or.inl rfl, c, hc ⟨other, hother⟩ ▸ hBS ⟨other, hother⟩, A, hAS,
        fun i h => hAB i (h.trans (hc i).symm), fun i => (hdegAB i).trans (by rw [hc i]),
        fun i x hx => ?_⟩
      rw [hform i x hx, hc i]
      ring
  have hν'inj : Function.Injective ν' := by
    intro i k hik
    by_contra hne
    have hne' : (i : I) ≠ k := fun h => hne (Subtype.ext h)
    have h₁ := hgram i k i.property k.property
    have h₂ := hgram i i i.property i.property
    rw [ite_eq_right hne'] at h₁
    rw [ite_eq_left rfl] at h₂
    have h₃ : ∑ x ∈ S, f i x * f k x = ∑ x ∈ S, f i x * f i x :=
      Finset.sum_congr rfl fun x hx => by rw [hformν' k x hx, hformν' i x hx, hik]
    omega
  let ν : I → L := fun i => if h : i = zero then c else ν' ⟨i, h⟩
  have hνzero : ν zero = c := dite_eq_left rfl
  have hνrest : ∀ i (h : i ≠ zero), ν i = ν' ⟨i, h⟩ := fun i h => dite_eq_right h
  refine ⟨ε, ν, hε, ?_, fun i => ?_, fun i k => ?_, fun i x hx => ?_⟩
  · intro i k hik
    by_cases hi : i = zero
    · by_cases hk : k = zero
      · exact hi.trans hk.symm
      · rw [hi, hνzero, hνrest k hk] at hik
        exact (hν'c _ hik.symm).elim
    · by_cases hk : k = zero
      · rw [hk, hνzero, hνrest i hi] at hik
        exact (hν'c _ hik).elim
      · rw [hνrest i hi, hνrest k hk] at hik
        exact congrArg Subtype.val (hν'inj hik)
  · by_cases hi : i = zero
    · rw [hi, hνzero]
      exact hcS
    · rw [hνrest i hi]
      exact hν'S _
  · have hdegν : ∀ i, deg (ν i) = deg c := by
      intro i
      by_cases hi : i = zero
      · rw [hi, hνzero]
      · rw [hνrest i hi]
        exact hdegν' _
    rw [hdegν i, hdegν k]
  · by_cases hi : i = zero
    · rw [hi, hzero x hx]
      ring
    · rw [hνrest i hi, hνzero]
      exact hformν' ⟨i, hi⟩ x hx

theorem blocksVChar_degree_zero_difference_star
    {X I : Type} [Group X] [Fintype X] [Fintype I] [DecidableEq I] (zero : I)
    (hI : 3 ≤ Fintype.card I) {f : I → X → ℂ} (hf : ∀ i, f i ∈ BlocksVChar X)
    (hzero : f zero = 0) (hdegree : ∀ i, f i 1 = 0)
    (hgram : ∀ i k, i ≠ zero → k ≠ zero →
      BlocksInnerProduct (f i) (f k) = 1 + if i = k then 1 else 0) :
    ∃ (ε : ℤ) (ν : I → BlocksIrr X), (ε = 1 ∨ ε = -1) ∧ Function.Injective ν ∧
      (∀ i k, (ν i : X → ℂ) 1 = (ν k : X → ℂ) 1) ∧
      ∀ i, f i = (ε : ℂ) • ((ν i : X → ℂ) - (ν zero : X → ℂ)) := by
  obtain ⟨other, hother⟩ : ∃ i : I, i ≠ zero := by
    by_contra hall
    push Not at hall
    have hle : Fintype.card I ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (hall a).trans (hall b).symm
    omega
  have : Nonempty {i : I // i ≠ zero} := ⟨⟨other, hother⟩⟩
  obtain ⟨common, χ, ε, hχinj, hχne, hε, hχdeg, hrepr⟩ :=
    blocksVChar_norm_two_gram_common_sign (fun i : {i : I // i ≠ zero} => f i)
      (fun i => hf i) (fun i => hdegree i) (fun i k => by
        have h := hgram i k i.property k.property
        by_cases hik : i = k
        · subst hik
          simpa using h
        · have hik' : (i : I) ≠ k := fun h => hik (Subtype.ext h)
          simpa [hik, hik'] using h)
  let ν : I → BlocksIrr X := fun i => if h : i = zero then common else χ ⟨i, h⟩
  have hνzero : ν zero = common := dite_eq_left rfl
  have hνrest : ∀ i (h : i ≠ zero), ν i = χ ⟨i, h⟩ := fun i h => dite_eq_right h
  have hνdeg : ∀ i, (ν i : X → ℂ) 1 = (common : X → ℂ) 1 := by
    intro i
    by_cases hi : i = zero
    · rw [hi, hνzero]
    · rw [hνrest i hi]
      exact hχdeg _
  refine ⟨ε, ν, hε, ?_, fun i k => by rw [hνdeg i, hνdeg k], fun i => ?_⟩
  · intro i k hik
    by_cases hi : i = zero
    · by_cases hk : k = zero
      · exact hi.trans hk.symm
      · rw [hi, hνzero, hνrest k hk] at hik
        exact (hχne _ hik.symm).elim
    · by_cases hk : k = zero
      · rw [hk, hνzero, hνrest i hi] at hik
        exact (hχne _ hik).elim
      · rw [hνrest i hi, hνrest k hk] at hik
        exact congrArg Subtype.val (hχinj hik)
  · by_cases hi : i = zero
    · rw [hi, hzero, sub_self, smul_zero]
    · rw [hνrest i hi, hνzero]
      exact hrepr ⟨i, hi⟩

end CFSG.Semidihedral.Principal
