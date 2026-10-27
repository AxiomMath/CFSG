module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def zb : P10 := A6Models.perm10 [[0, 9], [3, 6], [4, 5], [7, 8]]

theorem zb_code : code zb = Core.zbC := by decide +kernel

@[expose] def InE4 (x : P10) : Prop :=
  x ∈ P0 ∧ ∀ d ∈ P0, d ∈ A6Models.psl29 → x * d = d * x

@[expose] def IsRefl (r : P10) : Prop :=
  r ∈ P0 ∧ r ∈ A6Models.psl29 ∧ r ≠ 1 ∧ r ≠ zb ∧ r * r = 1

@[expose] def KleinMem (r e : P10) : Prop := e = 1 ∨ e = zb ∨ e = r ∨ e = r * zb

theorem code_comm_iff {x y : P10} :
    x * y = y * x ↔ Core.cmul (code x) (code y) = Core.cmul (code y) (code x) := by
  constructor
  · intro h
    rw [← code_mul, ← code_mul, h]
  · intro h
    apply code_injective
    rw [code_mul, code_mul]
    exact h

theorem mem_D_iff (x : P10) : (x ∈ P0 ∧ x ∈ A6Models.psl29) ↔ code x ∈ Core.dLit := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [Core.d_eq, List.mem_filter]
    exact ⟨(mem_P0_iff x).1 h1, List.contains_iff_mem.mpr ((mem_psl29_iff x).1 h2)⟩
  · intro h
    rw [Core.d_eq, List.mem_filter] at h
    exact ⟨(mem_P0_iff x).2 h.1, (mem_psl29_iff x).2 (List.contains_iff_mem.mp h.2)⟩

theorem exists_D_of_code {c : List ℕ} (hc : c ∈ Core.dLit) :
    ∃ x, x ∈ P0 ∧ x ∈ A6Models.psl29 ∧ code x = c := by
  have hc' := hc
  rw [Core.d_eq, List.mem_filter] at hc'
  obtain ⟨x, hx, rfl⟩ := exists_P0_of_code hc'.1
  exact ⟨x, hx, (mem_psl29_iff x).2 (List.contains_iff_mem.mp hc'.2), rfl⟩

theorem zb_mem_P0 : zb ∈ P0 := by
  rw [mem_P0_iff, zb_code]
  exact List.contains_iff_mem.mp Core.zb_central.1

theorem zb_mem_psl29 : zb ∈ A6Models.psl29 := by
  have h := (mem_D_iff zb).2 (by rw [zb_code]; exact List.contains_iff_mem.mp Core.zb_mem_d)
  exact h.2

theorem zb_ne_one : zb ≠ 1 := by
  intro h
  have := congrArg code h
  rw [zb_code, code_one] at this
  have h2 := Core.zb_central.2.1
  simp only [bne_iff_ne, ne_eq] at h2
  exact h2 this

theorem zb_central : ∀ p ∈ P0, zb * p = p * zb := by
  intro p hp
  have hall := Core.zb_central.2.2
  rw [List.all_eq_true] at hall
  have h1 := hall (code p) ((mem_P0_iff p).1 hp)
  rw [code_comm_iff, zb_code]
  exact beq_iff_eq.mp h1

theorem zb_sq : zb * zb = 1 := by
  apply code_injective
  rw [code_mul, zb_code, code_one]
  exact Core.zb_sq

theorem center_P0 {a : P10} (ha : a ∈ P0) (hc : ∀ p ∈ P0, a * p = p * a) : a = 1 ∨ a = zb := by
  have hall := Core.center_p0
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) ((mem_P0_iff a).1 ha)
  have hcent : (Core.p0Lit.all fun p => Core.cmul (code a) p == Core.cmul p (code a)) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨p', hp', rfl⟩ := exists_P0_of_code hp
    rw [beq_iff_eq, ← code_mul, ← code_mul, hc p' hp']
  rw [hcent] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h | h
  · left
    apply code_injective
    rw [code_one]
    exact h
  · right
    apply code_injective
    rw [zb_code]
    exact h

theorem sq_mem_D {p : P10} (hp : p ∈ P0) : p * p ∈ P0 ∧ p * p ∈ A6Models.psl29 := by
  have h := Core.squares_in_d
  rw [List.all_eq_true] at h
  have h1 := h (code p) ((mem_P0_iff p).1 hp)
  rw [← code_mul] at h1
  exact (mem_D_iff _).2 (List.contains_iff_mem.mp h1)

theorem pow4_of_mem {p : P10} (hp : p ∈ P0) : p ^ 4 = 1 ∨ p ^ 4 = zb := by
  have h := Core.fourth_powers
  rw [List.all_eq_true] at h
  have h1 := h (code p) ((mem_P0_iff p).1 hp)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h | h
  · left
    apply code_injective
    rw [code_pow, code_one]
    exact h
  · right
    apply code_injective
    rw [code_pow, zb_code]
    exact h

theorem exists_pow4 : ∃ p ∈ P0, p ^ 4 = zb := by
  have h := Core.fourth_exists
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hc4⟩ := h
  obtain ⟨p, hp, rfl⟩ := exists_P0_of_code hc
  refine ⟨p, hp, ?_⟩
  apply code_injective
  rw [code_pow, zb_code]
  exact beq_iff_eq.mp hc4

theorem inE4_iff (x : P10) : InE4 x ↔ code x ∈ Core.e4Lit := by
  unfold Core.e4Lit InE4
  rw [List.mem_filter, ← mem_P0_iff]
  constructor
  · rintro ⟨hx, hd⟩
    refine ⟨hx, ?_⟩
    rw [List.all_eq_true]
    intro d hd'
    obtain ⟨d', hdP, hdpsl, rfl⟩ := exists_D_of_code hd'
    rw [beq_iff_eq, ← code_mul, ← code_mul, hd d' hdP hdpsl]
  · rintro ⟨hx, hd⟩
    refine ⟨hx, fun d hdP hdpsl => ?_⟩
    rw [List.all_eq_true] at hd
    have := hd (code d) ((mem_D_iff d).1 ⟨hdP, hdpsl⟩)
    rw [beq_iff_eq] at this
    exact code_comm_iff.mpr this

theorem E4_inter_psl29 {x : P10} (hx : InE4 x) (hxd : x ∈ A6Models.psl29) : x = 1 ∨ x = zb := by
  have h := Core.e4_inter_d
  rw [List.all_eq_true] at h
  have h1 := h (code x) ((inE4_iff x).1 hx)
  have hd : Core.dLit.contains (code x) = true :=
    List.contains_iff_mem.mpr ((mem_D_iff x).1 ⟨hx.1, hxd⟩)
  rw [hd] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h | h
  · left
    apply code_injective
    rw [code_one]
    exact h
  · right
    apply code_injective
    rw [zb_code]
    exact h

theorem exists_E4_not_psl : ∃ b, InE4 b ∧ b ∉ A6Models.psl29 := by
  have h := Core.e4_not_d
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hcd⟩ := h
  have hcP : c ∈ Core.p0Lit := by
    unfold Core.e4Lit at hc
    rw [List.mem_filter] at hc
    exact hc.1
  obtain ⟨x, hx, rfl⟩ := exists_P0_of_code hcP
  refine ⟨x, (inE4_iff x).2 hc, fun hxpsl => ?_⟩
  have := List.contains_iff_mem.mpr ((mem_D_iff x).1 ⟨hx, hxpsl⟩)
  rw [this] at hcd
  exact Bool.false_ne_true hcd

theorem E4_shape {β : P10} (hβ : InE4 β) (hβd : β ∉ A6Models.psl29) {c : P10} (hc : InE4 c) :
    c = 1 ∨ c = zb ∨ c = β ∨ c = β * zb := by
  have h := Core.e4_shape
  rw [List.all_eq_true] at h
  have h1 := h (code β) ((inE4_iff β).1 hβ)
  have hnd : Core.dLit.contains (code β) = false := by
    by_contra hcon
    have hcon' : Core.dLit.contains (code β) = true := by simpa using hcon
    exact hβd ((mem_D_iff β).2 (List.contains_iff_mem.mp hcon')).2
  rw [hnd, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 (code c) ((inE4_iff c).1 hc)
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with ((h | h) | h) | h
  · left
    apply code_injective
    rw [code_one]
    exact h
  · right; left
    apply code_injective
    rw [zb_code]
    exact h
  · right; right; left
    exact code_injective h
  · right; right; right
    apply code_injective
    rw [code_mul, zb_code]
    exact h

theorem klein_code_mem {r : P10} {c : List ℕ} :
    c ∈ Core.kleinOf (code r) ↔ ∃ e, KleinMem r e ∧ code e = c := by
  unfold Core.kleinOf KleinMem
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, code_one⟩
    · exact ⟨zb, Or.inr (Or.inl rfl), zb_code⟩
    · exact ⟨r, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨r * zb, Or.inr (Or.inr (Or.inr rfl)), by rw [code_mul, zb_code]⟩
  · rintro ⟨e, (rfl | rfl | rfl | rfl), rfl⟩
    · left
      exact code_one
    · right; left
      exact zb_code
    · right; right; left
      rfl
    · right; right; right
      rw [code_mul, zb_code]

theorem isRefl_of {r : P10} (hr : IsRefl r) : Core.isRefl (code r) = true := by
  unfold Core.isRefl
  obtain ⟨hP, hpsl, h1, hzb, hsq⟩ := hr
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨List.contains_iff_mem.mpr ((mem_D_iff r).1 ⟨hP, hpsl⟩), ?_⟩, ?_⟩, ?_⟩
  · intro h
    apply h1
    apply code_injective
    rw [code_one]
    exact h
  · intro h
    apply hzb
    apply code_injective
    rw [zb_code]
    exact h
  · rw [← code_mul, hsq, code_one]

theorem IsRefl.of_isRefl {r : P10} (h : Core.isRefl (code r) = true) : IsRefl r := by
  unfold Core.isRefl at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hd, h1⟩, h2⟩, h3⟩ := h
  obtain ⟨hP, hpsl⟩ := (mem_D_iff r).2 (List.contains_iff_mem.mp hd)
  refine ⟨hP, hpsl, ?_, ?_, ?_⟩
  · intro h
    apply h1
    rw [h, code_one]
  · intro h
    apply h2
    rw [h, zb_code]
  · apply code_injective
    rw [code_mul, code_one]
    exact h3

theorem klein_cent_aut {r β q : P10} (hr : IsRefl r) (hβ : InE4 β) (hβd : β ∉ A6Models.psl29)
    (hq : q ∈ A6Models.autA6) (hqr : q * r = r * q) (hqz : q * zb = zb * q) :
    q ∈ P0 ∧ (KleinMem r q ∨ ∃ e, KleinMem r e ∧ q = e * β) := by
  have hall := Core.klein_cent_aut
  rw [List.all_eq_true] at hall
  have h1 := hall (code r) (List.contains_iff_mem.mp (by
    have := isRefl_of hr
    unfold Core.isRefl at this
    simp only [Bool.and_eq_true] at this
    exact this.1.1.1))
  rw [isRefl_of hr, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have hnd : Core.dLit.contains (code β) = false := by
    by_contra hcon
    have hcon' : Core.dLit.contains (code β) = true := by simpa using hcon
    exact hβd ((mem_D_iff β).2 (List.contains_iff_mem.mp hcon')).2
  have h2 := h1 (code β) ((inE4_iff β).1 hβ)
  rw [hnd, Bool.false_or, List.all_eq_true] at h2
  have h3 := h2 (code q) (code_mem_autL hq)
  have hc1 : (Core.cmul (code q) (code r) == Core.cmul (code r) (code q)) = true := by
    rw [beq_iff_eq]
    exact code_comm_iff.mp hqr
  have hc2 : (Core.cmul (code q) Core.zbC == Core.cmul Core.zbC (code q)) = true := by
    rw [beq_iff_eq, ← zb_code]
    exact code_comm_iff.mp hqz
  rw [hc1, hc2] at h3
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h3
  obtain ⟨hP, hk⟩ := h3
  refine ⟨(mem_P0_iff q).2 (List.contains_iff_mem.mp hP), ?_⟩
  rw [Bool.or_eq_true] at hk
  rcases hk with hk | hk
  · obtain ⟨e, he, hec⟩ := klein_code_mem.mp (List.contains_iff_mem.mp hk)
    left
    have : e = q := code_injective hec
    rw [← this]
    exact he
  · rw [List.any_eq_true] at hk
    obtain ⟨e', he', hee⟩ := hk
    obtain ⟨e, he, rfl⟩ := klein_code_mem.mp he'
    right
    refine ⟨e, he, ?_⟩
    apply code_injective
    rw [code_mul]
    exact (beq_iff_eq.mp hee).symm

theorem conj_zb {a : P10} (haP : a ∈ P0) (hapsl : a ∈ A6Models.psl29) (hne : a ≠ 1)
    (ha2 : a * a = 1) : ∃ g ∈ A6Models.psl29, g * zb = a * g := by
  have hall := Core.conj_zb
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) ((mem_D_iff a).1 ⟨haP, hapsl⟩)
  have hne' : (code a == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro h
    exact hne (code_injective h)
  have hsq : (Core.cmul (code a) (code a) == Core.cid) = true := by
    rw [beq_iff_eq, ← code_mul, ha2, code_one]
  rw [hne', hsq] at h1
  simp only [Bool.false_or, Bool.not_true, Bool.false_or, List.any_eq_true] at h1
  obtain ⟨c, hc, hca⟩ := h1
  obtain ⟨g, hg, rfl⟩ := exists_psl29_of_code hc
  refine ⟨g, hg, ?_⟩
  apply code_injective
  rw [code_mul, code_mul, zb_code]
  exact beq_iff_eq.mp hca

theorem beq_cid_false {x : P10} (hx : x ≠ 1) : (code x == Core.cid) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  rw [← code_one]
  intro h
  exact hx (code_injective h)

theorem beq_sq_true {x : P10} (hx : x * x = 1) : (Core.cmul (code x) (code x) == Core.cid) = true := by
  rw [beq_iff_eq, ← code_mul, hx, code_one]

theorem beq_ne_false {x y : P10} (hxy : x ≠ y) : (code x == code y) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h
  exact hxy (code_injective h)

theorem beq_comm_true {x y : P10} (h : x * y = y * x) :
    (Core.cmul (code x) (code y) == Core.cmul (code y) (code x)) = true := by
  rw [beq_iff_eq]
  exact code_comm_iff.mp h

theorem isRefl_dLit {r : P10} (hr : IsRefl r) : Core.dLit.contains (code r) = true :=
  List.contains_iff_mem.mpr ((mem_D_iff r).1 ⟨hr.1, hr.2.1⟩)

theorem mem_kleinCent_iff {r y : P10} :
    code y ∈ Core.kleinCent (code r) ↔ y ∈ P0 ∧ y * r = r * y ∧ y * zb = zb * y := by
  unfold Core.kleinCent
  rw [List.mem_filter, ← mem_P0_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hy, h1, h2⟩
    refine ⟨hy, code_comm_iff.mpr h1, code_comm_iff.mpr ?_⟩
    rw [zb_code]
    exact h2
  · rintro ⟨hy, h1, h2⟩
    refine ⟨hy, code_comm_iff.mp h1, ?_⟩
    have := code_comm_iff.mp h2
    rw [zb_code] at this
    exact this

theorem d_klein_zb_mem {a b : P10} (haP : a ∈ P0) (hapsl : a ∈ A6Models.psl29) (hbP : b ∈ P0)
    (hbpsl : b ∈ A6Models.psl29) (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hb2 : b * b = 1) (hab : a * b = b * a) : a = zb ∨ b = zb ∨ a * b = zb := by
  have hall := Core.d_klein_zb
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) ((mem_D_iff a).1 ⟨haP, hapsl⟩)
  rw [beq_cid_false ha1, beq_sq_true ha2] at h1
  simp only [Bool.false_or, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 (code b) ((mem_D_iff b).1 ⟨hbP, hbpsl⟩)
  rw [beq_cid_false hb1, beq_ne_false hba, beq_sq_true hb2, beq_comm_true hab] at h2
  simp only [Bool.false_or, Bool.not_true, Bool.or_eq_true, beq_iff_eq] at h2
  rcases h2 with (h | h) | h
  · left
    apply code_injective
    rw [zb_code]
    exact h
  · right; left
    apply code_injective
    rw [zb_code]
    exact h
  · right; right
    apply code_injective
    rw [code_mul, zb_code]
    exact h

theorem klein_cent_comm_mem {r q q' : P10} (hr : IsRefl r) (hq : q ∈ P0) (hqr : q * r = r * q)
    (hqz : q * zb = zb * q) (hq' : q' ∈ P0) (hq'r : q' * r = r * q') (hq'z : q' * zb = zb * q') :
    q * q' = q' * q := by
  have hall := Core.klein_cent_comm
  rw [List.all_eq_true] at hall
  have h1 := hall (code r) (List.contains_iff_mem.mp (isRefl_dLit hr))
  rw [isRefl_of hr, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 (code q) (mem_kleinCent_iff.mpr ⟨hq, hqr, hqz⟩)
  rw [List.all_eq_true] at h2
  have h3 := h2 (code q') (mem_kleinCent_iff.mpr ⟨hq', hq'r, hq'z⟩)
  exact code_comm_iff.mpr (beq_iff_eq.mp h3)

theorem exists_noncomm_D : ∃ d d' : P10, d ∈ P0 ∧ d ∈ A6Models.psl29 ∧ d' ∈ P0 ∧
    d' ∈ A6Models.psl29 ∧ d * d' ≠ d' * d := by
  have h := Core.d_nonabelian
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, h1⟩ := h
  rw [List.any_eq_true] at h1
  obtain ⟨c', hc', h2⟩ := h1
  obtain ⟨d, hdP, hdpsl, rfl⟩ := exists_D_of_code hc
  obtain ⟨d', hdP', hdpsl', rfl⟩ := exists_D_of_code hc'
  refine ⟨d, d', hdP, hdpsl, hdP', hdpsl', fun hcomm => ?_⟩
  rw [beq_comm_true hcomm] at h2
  exact absurd h2 (by simp)

theorem refl_of_good {g : P10} (hgP : g ∈ P0) (hne : g ≠ 1) (hg2 : g * g = 1)
    (hgood : g ∈ A6Models.psl29 ∨ g ∈ s6) (hE4 : ¬ InE4 g) :
    ∃ r, IsRefl r ∧ ∀ q ∈ P0, q * g = g * q → q * r = r * q := by
  have hall := Core.refl_of_good
  rw [List.all_eq_true] at hall
  have h1 := hall (code g) ((mem_P0_iff g).1 hgP)
  have hgood' : (Core.pslLit.contains (code g) || Core.inS6 (code g)) = true := by
    rw [Bool.or_eq_true]
    rcases hgood with h | h
    · left
      exact List.contains_iff_mem.mpr ((mem_psl29_iff g).1 h)
    · right
      exact (mem_s6_iff g).1 h
  have hnE4 : Core.e4Lit.contains (code g) = false := by
    by_contra hcon
    have : Core.e4Lit.contains (code g) = true := by simpa using hcon
    exact hE4 ((inE4_iff g).2 (List.contains_iff_mem.mp this))
  rw [beq_cid_false hne, beq_sq_true hg2, hgood', hnE4] at h1
  simp only [Bool.false_or, Bool.not_true, Bool.or_false, List.any_eq_true, Bool.and_eq_true] at h1
  obtain ⟨c, hc, hrefl, hall'⟩ := h1
  obtain ⟨r, hrP, hrpsl, rfl⟩ := exists_D_of_code hc
  refine ⟨r, IsRefl.of_isRefl hrefl, fun q hq hqg => ?_⟩
  rw [List.all_eq_true] at hall'
  have := hall' (code q) ((mem_P0_iff q).1 hq)
  rw [beq_comm_true hqg, Bool.not_true, Bool.false_or] at this
  exact code_comm_iff.mpr (beq_iff_eq.mp this)

end CFSG.QuasithinUnique.A6Facts
