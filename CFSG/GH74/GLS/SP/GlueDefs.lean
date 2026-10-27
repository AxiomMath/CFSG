module

public import CFSG.GH74.BNPair.RootCalc
public import CFSG.GH74.BNPair.Positions

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

@[expose] def negGen (n : ℕ) (root : ℤ → Subgroup X) : Subgroup X :=
  ⨆ k ∈ Set.Icc (1 : ℤ) n, root (-k)

theorem mem_negGen_of_mem {n : ℕ} {root : ℤ → Subgroup X} {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    {y : X} (hy : y ∈ root (-k)) : y ∈ negGen n root :=
  Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem ⟨hk1, hkn⟩ hy)

structure RGD2 (n : ℕ) (H : Subgroup X) (r₁ r₂ : X) (U : Subgroup X) (root : ℤ → Subgroup X) :
    Prop where
  three_le : 3 ≤ n
  comm_H : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  nilpotent : Group.IsNilpotent U
  conj_H₁ : ∀ h ∈ H, r₁ * h * r₁⁻¹ ∈ H
  conj_H₂ : ∀ h ∈ H, r₂ * h * r₂⁻¹ ∈ H
  sq₁ : r₁ * r₁ ∈ H
  sq₂ : r₂ * r₂ ∈ H
  pow : (r₁ * r₂) ^ n ∈ H
  U_inf_H : U ⊓ H = ⊥
  ne_bot : ∀ i, IsRoot n i → root i ≠ ⊥
  invariant : ∀ i, IsRoot n i → ∀ h ∈ H, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i
  carrier_eq : (U : Set X) = chainProd root (intList 1 n)
  unique : ∀ f g : ℤ → X, (∀ k ∈ intList 1 n, f k ∈ root k) → (∀ k ∈ intList 1 n, g k ∈ root k) →
    ((intList 1 n).map f).prod = ((intList 1 n).map g).prod → ∀ k ∈ intList 1 n, f k = g k
  reverse_eq : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ n →
    chainProd root (intList i j) = chainProd root (intList i j).reverse
  subgroup : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ n →
    ∃ V : Subgroup X, (V : Set X) = chainProd root (intList i j) ∧ V ≤ U ∧
      (1 < i → ∀ x ∈ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < n → ∀ x ∈ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)
  act₁ : conjBy r₁⁻¹ (root 1) = root (-1) ∧ conjBy r₁⁻¹ (root (-1)) = root 1 ∧
    ∀ i : ℤ, 2 ≤ i → i ≤ n → conjBy r₁⁻¹ (root i) = root ((n : ℤ) + 2 - i) ∧
      conjBy r₁⁻¹ (root (-i)) = root (-((n : ℤ) + 2 - i))
  act₂ : conjBy r₂⁻¹ (root n) = root (-(n : ℤ)) ∧ conjBy r₂⁻¹ (root (-(n : ℤ))) = root n ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 → conjBy r₂⁻¹ (root i) = root ((n : ℤ) - i) ∧
      conjBy r₂⁻¹ (root (-i)) = root (-((n : ℤ) - i))
  meet_one : ∀ x ∈ H ⊔ U, x ∈ negGen n root → x = 1
  rank₁ : ∀ y ∈ root (-1), y ≠ 1 →
    y ∈ (root 1 : Set X) * (H : Set X) * {r₁} * (root 1 : Set X)
  rank₂ : ∀ y ∈ root (-(n : ℤ)), y ≠ 1 →
    y ∈ (root n : Set X) * (H : Set X) * {r₂} * (root n : Set X)

theorem isRoot_of_pos_le {n : ℕ} {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : IsRoot n k :=
  ⟨by omega, by omega⟩

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

include R in
theorem root_le_U {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : root k ≤ U := by
  obtain ⟨V, hV, hVU, -, -⟩ := R.subgroup k k hk1 le_rfl hkn
  intro x hx
  have : x ∈ chainProd root (intList k k) :=
    mem_chainProd_of_mem root (mem_intList_iff.2 ⟨le_rfl, le_rfl⟩) hx
  rw [← hV] at this
  exact hVU this

include R in
theorem conj_mem_U {h : X} (hh : h ∈ H) {u : X} (hu : u ∈ U) : h * u * h⁻¹ ∈ U := by
  have hu' : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
  refine chainProd_conj_mem root U h (intList 1 n) (fun k hk y hy => ?_) u hu'
  have hk' := mem_intList_iff.1 hk
  exact R.root_le_U hk'.1 hk'.2 (R.invariant k (isRoot_of_pos_le hk'.1 hk'.2) h hh y hy)

include R in
theorem H_le_normalizer_U : H ≤ Subgroup.normalizer (U : Set X) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => R.conj_mem_U hh hu, fun hu => ?_⟩
  have := R.conj_mem_U (H.inv_mem hh) hu
  simpa [mul_assoc] using this

include R in
theorem coe_sup_HU : ((H ⊔ U : Subgroup X) : Set X) = (H : Set X) * (U : Set X) :=
  Subgroup.coe_mul_of_left_le_normalizer_right H U R.H_le_normalizer_U

include R in
theorem coe_sup_UH : ((U ⊔ H : Subgroup X) : Set X) = (U : Set X) * (H : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left U H R.H_le_normalizer_U

include R in
theorem sq₁_inv : r₁⁻¹ * r₁⁻¹ ∈ H := by
  have := H.inv_mem R.sq₁
  simpa [mul_inv_rev] using this

include R in
theorem sq₂_inv : r₂⁻¹ * r₂⁻¹ ∈ H := by
  have := H.inv_mem R.sq₂
  simpa [mul_inv_rev] using this

include R in
theorem conj_H₁' {h : X} (hh : h ∈ H) : r₁⁻¹ * h * r₁ ∈ H := by
  have h1 := H.mul_mem (H.mul_mem R.sq₁_inv (R.conj_H₁ h hh)) R.sq₁
  have e : r₁⁻¹ * r₁⁻¹ * (r₁ * h * r₁⁻¹) * (r₁ * r₁) = r₁⁻¹ * h * r₁ := by group
  rwa [e] at h1

include R in
theorem conj_H₂' {h : X} (hh : h ∈ H) : r₂⁻¹ * h * r₂ ∈ H := by
  have h1 := H.mul_mem (H.mul_mem R.sq₂_inv (R.conj_H₂ h hh)) R.sq₂
  have e : r₂⁻¹ * r₂⁻¹ * (r₂ * h * r₂⁻¹) * (r₂ * r₂) = r₂⁻¹ * h * r₂ := by group
  rwa [e] at h1

end RGD2

theorem Rt_add_n {n : ℕ} (hn : 0 < n) (p : ℤ) : Rt n (p + n) = -Rt n p := by
  have h2n : (0 : ℤ) < 2 * n := by omega
  have e := Int.emod_add_mul_ediv p (2 * (n : ℤ))
  have hv0 := Int.emod_nonneg p h2n.ne'
  have hv1 := Int.emod_lt_of_pos p h2n
  set v := p % (2 * (n : ℤ)) with hv
  set k := p / (2 * (n : ℤ)) with hk
  have h1 : Rt n p = Rt n v := by
    rw [← e, Rt_add_mul]
  have h2 : Rt n (p + n) = Rt n (v + n) := by
    rw [← e, show v + 2 * (n : ℤ) * k + n = (v + n) + 2 * (n : ℤ) * k by ring, Rt_add_mul]
  rw [h1, h2]
  rcases lt_or_ge v n with h | h
  · rw [Rt_of_lt hv0 h, Rt_of_ge (by omega) (by omega)]
    ring
  · rw [Rt_of_ge h hv1, show v + (n : ℤ) = (v - n) + 2 * (n : ℤ) * 1 by ring, Rt_add_mul,
      Rt_of_lt (by omega) (by omega)]
    ring

theorem Rt_sub_n {n : ℕ} (hn : 0 < n) (p : ℤ) : Rt n (p - n) = -Rt n p := by
  rw [← Rt_add_n hn, show p - (n : ℤ) = (p + n) + 2 * (n : ℤ) * (-1) by ring, Rt_add_mul]

@[expose] def ActsPos (n : ℕ) (root : ℤ → Subgroup X) (m : X) (f : ℤ → ℤ) : Prop :=
  ∀ q : ℤ, ∀ x ∈ root (Rt n q), m * x * m⁻¹ ∈ root (Rt n (f q))

@[expose] def IsAff (f : ℤ → ℤ) : Prop := (∃ c, ∀ q, f q = q + c) ∨ ∃ c, ∀ q, f q = c - q

theorem isAff_id : IsAff (fun q => q) := Or.inl ⟨0, fun q => by simp⟩

theorem IsAff.comp {f g : ℤ → ℤ} (hf : IsAff f) (hg : IsAff g) : IsAff (fun q => f (g q)) := by
  rcases hf with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases hg with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨b + a, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inr ⟨b + a, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inr ⟨a - b, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inl ⟨a - b, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩

theorem IsAff.rt_add_n {n : ℕ} (hn : 0 < n) {f : ℤ → ℤ} (hf : IsAff f) (q : ℤ) :
    Rt n (f (q + n)) = -Rt n (f q) := by
  rcases hf with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc, hc, show q + (n : ℤ) + c = (q + c) + n by ring, Rt_add_n hn]
  · rw [hc, hc, show c - (q + (n : ℤ)) = (c - q) - n by ring, Rt_sub_n hn]

theorem ActsPos.mul {n : ℕ} {root : ℤ → Subgroup X} {m m' : X} {f g : ℤ → ℤ}
    (hm : ActsPos n root m f) (hm' : ActsPos n root m' g) :
    ActsPos n root (m * m') (fun q => f (g q)) := by
  intro q x hx
  have := hm (g q) _ (hm' q x hx)
  have e : m * (m' * x * m'⁻¹) * m⁻¹ = m * m' * x * (m * m')⁻¹ := by group
  rwa [e] at this

theorem ActsPos.one {n : ℕ} {root : ℤ → Subgroup X} : ActsPos n root (1 : X) (fun q => q) := by
  intro q x hx
  simpa using hx

@[expose] def GoodAct (n : ℕ) (root : ℤ → Subgroup X) (m : X) : Prop :=
  ∃ f g : ℤ → ℤ, IsAff f ∧ IsAff g ∧ ActsPos n root m f ∧ ActsPos n root m⁻¹ g

theorem GoodAct.mul {n : ℕ} {root : ℤ → Subgroup X} {m m' : X} (h : GoodAct n root m)
    (h' : GoodAct n root m') : GoodAct n root (m * m') := by
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := h
  obtain ⟨f', g', hf', hg', hmf', hmg'⟩ := h'
  refine ⟨fun q => f (f' q), fun q => g' (g q), hf.comp hf', hg'.comp hg, hmf.mul hmf', ?_⟩
  rw [mul_inv_rev]
  exact hmg'.mul hmg

theorem GoodAct.inv {n : ℕ} {root : ℤ → Subgroup X} {m : X} (h : GoodAct n root m) :
    GoodAct n root m⁻¹ := by
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := h
  exact ⟨g, f, hg, hf, hmg, by rwa [inv_inv]⟩

theorem GoodAct.one {n : ℕ} {root : ℤ → Subgroup X} : GoodAct n root (1 : X) :=
  ⟨fun q => q, fun q => q, isAff_id, isAff_id, ActsPos.one, by rw [inv_one]; exact ActsPos.one⟩

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

include R in
theorem actsPos_of_mem_H {h : X} (hh : h ∈ H) : ActsPos n root h (fun q => q) := by
  intro q x hx
  exact R.invariant _ (Rt_isRoot (by have := R.three_le; omega) q) h hh x hx

include R in
theorem goodAct_of_mem_H {h : X} (hh : h ∈ H) : GoodAct n root h := by
  refine ⟨fun q => q, fun q => q, isAff_id, isAff_id, R.actsPos_of_mem_H hh, ?_⟩
  exact R.actsPos_of_mem_H (H.inv_mem hh)

include R in
theorem actsPos_r₁ : ActsPos n root r₁ (fun q => (n : ℤ) - q) := by
  have hn := R.three_le
  obtain ⟨a1, a2, a3⟩ := R.act₁
  intro q x hx
  set v := q % (2 * (n : ℤ)) with hv
  have hv0 : 0 ≤ v := Int.emod_nonneg q (by omega)
  have hv1 : v < 2 * (n : ℤ) := Int.emod_lt_of_pos q (by omega)
  have hq : Rt n q = Rt n v := Rt_congr (by rw [hv, Int.emod_emod])
  have hq' : Rt n ((n : ℤ) - q) = Rt n ((n : ℤ) - v) :=
    Rt_congr (by rw [Int.sub_emod, Int.sub_emod (n : ℤ) v, hv, Int.emod_emod])
  rw [hq] at hx
  rw [hq']
  rcases Int.lt_trichotomy v 0 with h | h | h
  · omega
  · rw [h] at hx ⊢
    rw [Rt_of_lt (le_refl 0) (by omega)] at hx
    rw [sub_zero, Rt_of_ge (le_refl _) (by omega)]
    have := mem_of_conjBy_inv a1 hx
    simpa using this
  · rcases lt_trichotomy v n with h' | h' | h'
    · rw [Rt_of_lt (by omega) h'] at hx
      rw [Rt_of_lt (by omega) (by omega)]
      have := mem_of_conjBy_inv (a3 (v + 1) (by omega) (by omega)).1 hx
      convert this using 2
      ring
    · rw [h'] at hx ⊢
      rw [Rt_of_ge (le_refl _) (by omega)] at hx
      rw [sub_self, Rt_of_lt (le_refl 0) (by omega)]
      have hx' : x ∈ root (-1) := by
        convert hx using 2
        ring
      have := mem_of_conjBy_inv a2 hx'
      simpa using this
    · rw [Rt_of_ge h'.le hv1] at hx
      rw [Rt_of_neg (by omega) (by omega)]
      have := mem_of_conjBy_inv (a3 (v - n + 1) (by omega) (by omega)).2 hx
      convert this using 2
      ring

include R in
theorem actsPos_r₂ : ActsPos n root r₂ (fun q => (n : ℤ) - 2 - q) := by
  have hn := R.three_le
  obtain ⟨b1, b2, b3⟩ := R.act₂
  intro q x hx
  set v := q % (2 * (n : ℤ)) with hv
  have hv0 : 0 ≤ v := Int.emod_nonneg q (by omega)
  have hv1 : v < 2 * (n : ℤ) := Int.emod_lt_of_pos q (by omega)
  have hq : Rt n q = Rt n v := Rt_congr (by rw [hv, Int.emod_emod])
  have hq' : Rt n ((n : ℤ) - 2 - q) = Rt n ((n : ℤ) - 2 - v) :=
    Rt_congr (by rw [Int.sub_emod, Int.sub_emod ((n : ℤ) - 2) v, hv, Int.emod_emod])
  rw [hq] at hx
  rw [hq']
  by_cases h1 : v ≤ (n : ℤ) - 2
  · rw [Rt_of_lt hv0 (by omega)] at hx
    rw [Rt_of_lt (by omega) (by omega)]
    have := mem_of_conjBy_inv (b3 (v + 1) (by omega) (by omega)).1 hx
    convert this using 2
    ring
  by_cases h2 : v = (n : ℤ) - 1
  · rw [h2, Rt_of_lt (by omega) (by omega)] at hx
    rw [h2, Rt_of_neg (by omega) (by omega)]
    have hx' : x ∈ root (n : ℤ) := by
      convert hx using 2
      ring
    have := mem_of_conjBy_inv b1 hx'
    convert this using 2
    ring
  by_cases h3 : v = 2 * (n : ℤ) - 1
  · rw [h3, Rt_of_ge (by omega) (by omega)] at hx
    rw [h3, show (n : ℤ) - 2 - (2 * (n : ℤ) - 1) = ((n : ℤ) - 1) + 2 * (n : ℤ) * (-1) by ring,
      Rt_add_mul, Rt_of_lt (by omega) (by omega)]
    have hx' : x ∈ root (-(n : ℤ)) := by
      convert hx using 2
      ring
    have := mem_of_conjBy_inv b2 hx'
    convert this using 2
    ring
  · rw [Rt_of_ge (by omega) hv1] at hx
    rw [Rt_of_neg (by omega) (by omega)]
    have := mem_of_conjBy_inv (b3 (v - n + 1) (by omega) (by omega)).2 hx
    convert this using 2
    ring

include R in
theorem actsPos_inv_of_sq {m : X} (hm : m * m ∈ H) {f : ℤ → ℤ} (hf : ActsPos n root m f) :
    ActsPos n root m⁻¹ f := by
  intro q x hx
  have h1 := hf q x hx
  have hh : m⁻¹ * m⁻¹ ∈ H := by
    have := H.inv_mem hm
    simpa [mul_inv_rev] using this
  have h2 := R.invariant _ (Rt_isRoot (by have := R.three_le; omega) (f q)) (m⁻¹ * m⁻¹) hh _ h1
  have e : m⁻¹ * m⁻¹ * (m * x * m⁻¹) * (m⁻¹ * m⁻¹)⁻¹ = m⁻¹ * x * (m⁻¹)⁻¹ := by group
  rwa [e] at h2

include R in
theorem goodAct_r₁ : GoodAct n root r₁ :=
  ⟨fun q => (n : ℤ) - q, fun q => (n : ℤ) - q, Or.inr ⟨n, fun _ => rfl⟩, Or.inr ⟨n, fun _ => rfl⟩,
    R.actsPos_r₁, R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁⟩

include R in
theorem goodAct_r₂ : GoodAct n root r₂ :=
  ⟨fun q => (n : ℤ) - 2 - q, fun q => (n : ℤ) - 2 - q, Or.inr ⟨(n : ℤ) - 2, fun _ => rfl⟩,
    Or.inr ⟨(n : ℤ) - 2, fun _ => rfl⟩, R.actsPos_r₂, R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂⟩

@[expose] def N (_R : RGD2 n H r₁ r₂ U root) : Subgroup X :=
  Subgroup.closure ((H : Set X) ∪ {r₁, r₂})

include R in
theorem goodAct_of_mem_N {m : X} (hm : m ∈ R.N) : GoodAct n root m := by
  unfold N at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact R.goodAct_of_mem_H hx
    · rcases hx with rfl | rfl
      · exact R.goodAct_r₁
      · exact R.goodAct_r₂
  | one => exact GoodAct.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

end RGD2

end CFSG.GH74.GLS.SP
