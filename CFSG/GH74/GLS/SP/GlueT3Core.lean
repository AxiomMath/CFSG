module

public import CFSG.GH74.GLS.SP.GlueT3

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

structure RGD2Core (n : ℕ) (H : Subgroup X) (r₁ r₂ : X) (U : Subgroup X)
    (root : ℤ → Subgroup X) : Prop where
  three_le : 3 ≤ n
  conj_H₁ : ∀ h ∈ H, r₁ * h * r₁⁻¹ ∈ H
  conj_H₂ : ∀ h ∈ H, r₂ * h * r₂⁻¹ ∈ H
  sq₁ : r₁ * r₁ ∈ H
  sq₂ : r₂ * r₂ ∈ H
  ne_bot : ∀ i, IsRoot n i → root i ≠ ⊥
  invariant : ∀ i, IsRoot n i → ∀ h ∈ H, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i
  carrier_eq : (U : Set X) = chainProd root (intList 1 n)
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
  meet_one : ∀ x ∈ H ⊔ U, x ∈ chainProd root ((intList 1 n).map Neg.neg) → x = 1
  rank₁ : ∀ y ∈ root (-1), y ≠ 1 →
    y ∈ (root 1 : Set X) * (H : Set X) * {r₁} * (root 1 : Set X)
  rank₂ : ∀ y ∈ root (-(n : ℤ)), y ≠ 1 →
    y ∈ (root n : Set X) * (H : Set X) * {r₂} * (root n : Set X)

theorem closure_union_pair_eq_of_quotient_closure_eq_top {G : Type*} [Group G]
    {H N : Subgroup G} [(H.subgroupOf N).Normal] (hHN : H ≤ N) {r₁ r₂ : G}
    (h₁ : r₁ ∈ N) (h₂ : r₂ ∈ N)
    (hgen : Subgroup.closure ({((⟨r₁, h₁⟩ : N) : N ⧸ H.subgroupOf N),
      ((⟨r₂, h₂⟩ : N) : N ⧸ H.subgroupOf N)} : Set (N ⧸ H.subgroupOf N)) = ⊤) :
    Subgroup.closure ((H : Set G) ∪ {r₁, r₂}) = N := by
  let K : Subgroup G := Subgroup.closure ((H : Set G) ∪ {r₁, r₂})
  have hKH : H ≤ K := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hr₁K : r₁ ∈ K := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hr₂K : r₂ ∈ K := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hKN : K ≤ N := by
    refine (Subgroup.closure_le N).2 ?_
    rintro x (hx | hx)
    · exact hHN hx
    · rcases hx with rfl | rfl
      · exact h₁
      · exact h₂
  have hmap : (K.subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N)) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro w (rfl | rfl)
    · exact ⟨⟨r₁, h₁⟩, Subgroup.mem_subgroupOf.mpr hr₁K, rfl⟩
    · exact ⟨⟨r₂, h₂⟩, Subgroup.mem_subgroupOf.mpr hr₂K, rfl⟩
  refine le_antisymm hKN ?_
  intro x hx
  have hxmap : (QuotientGroup.mk' (H.subgroupOf N)) ⟨x, hx⟩ ∈
      (K.subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N)) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hyK, hyx⟩ := Subgroup.mem_map.mp hxmap
  have hyx' : (y : G)⁻¹ * (x : G) ∈ H := by
    have := QuotientGroup.eq.mp hyx
    simpa using (Subgroup.mem_subgroupOf.mp this)
  have hxeq : (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
  rw [hxeq]
  exact K.mul_mem (Subgroup.mem_subgroupOf.mp hyK) (hKH hyx')

namespace RGD2Core

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2Core n H r₁ r₂ U root)

include R in
theorem root_le_U {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : root k ≤ U := by
  obtain ⟨V, hV, hVU, -, -⟩ := R.subgroup k k hk1 le_rfl hkn
  intro x hx
  have : x ∈ chainProd root (intList k k) :=
    mem_chainProd_of_mem root (mem_intList_iff.2 ⟨le_rfl, le_rfl⟩) hx
  rw [← hV] at this
  exact hVU this

include R in
theorem mem_chainProd_neg {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) {y : X}
    (hy : y ∈ root (-k)) : y ∈ chainProd root ((intList 1 n).map Neg.neg) :=
  mem_chainProd_of_mem root
    (List.mem_map.2 ⟨k, mem_intList_iff.2 ⟨hk1, hkn⟩, by simp⟩) hy

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
    rw [h3, show (n : ℤ) - 2 - (2 * (n : ℤ) - 1) =
      ((n : ℤ) - 1) + 2 * (n : ℤ) * (-1) by ring,
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
  ⟨fun q => (n : ℤ) - q, fun q => (n : ℤ) - q, Or.inr ⟨n, fun _ => rfl⟩,
    Or.inr ⟨n, fun _ => rfl⟩, R.actsPos_r₁, R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁⟩

include R in
theorem goodAct_r₂ : GoodAct n root r₂ :=
  ⟨fun q => (n : ℤ) - 2 - q, fun q => (n : ℤ) - 2 - q,
    Or.inr ⟨(n : ℤ) - 2, fun _ => rfl⟩, Or.inr ⟨(n : ℤ) - 2, fun _ => rfl⟩,
    R.actsPos_r₂, R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂⟩

@[expose] def N (_R : RGD2Core n H r₁ r₂ U root) : Subgroup X :=
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

include R in
theorem mem_sup_iff_UH {b : X} : b ∈ H ⊔ U ↔ ∃ u ∈ U, ∃ h ∈ H, b = u * h := by
  rw [sup_comm, ← SetLike.mem_coe, R.coe_sup_UH]
  constructor
  · intro hb
    obtain ⟨u, hu, h, hh, rfl⟩ := Set.mem_mul.1 hb
    exact ⟨u, hu, h, hh, rfl⟩
  · rintro ⟨u, hu, h, hh, rfl⟩
    exact Set.mul_mem_mul hu hh

include R in
theorem N_normalizes_H {x : X} (hx : x ∈ R.N) :
    ∀ h ∈ H, x * h * x⁻¹ ∈ H ∧ x⁻¹ * h * x ∈ H := by
  unfold N at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · intro h hh
      exact ⟨H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx),
        H.mul_mem (H.mul_mem (H.inv_mem hx) hh) hx⟩
    · rcases hx with rfl | rfl
      · exact fun h hh => ⟨R.conj_H₁ h hh, R.conj_H₁' hh⟩
      · exact fun h hh => ⟨R.conj_H₂ h hh, R.conj_H₂' hh⟩
  | one => exact fun h hh => ⟨by simpa using hh, by simpa using hh⟩
  | mul x y _ _ hx hy =>
    intro h hh
    refine ⟨?_, ?_⟩
    · have := (hx _ (hy h hh).1).1
      rwa [show x * (y * h * y⁻¹) * x⁻¹ = x * y * h * (x * y)⁻¹ by group] at this
    · have := (hy _ (hx h hh).2).2
      rwa [show y⁻¹ * (x⁻¹ * h * x) * y = (x * y)⁻¹ * h * (x * y) by group] at this
  | inv x _ hx =>
    intro h hh
    exact ⟨by simpa using (hx h hh).2, by simpa using (hx h hh).1⟩

include R in
theorem r₁_mem_N : r₁ ∈ R.N :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

include R in
theorem r₂_mem_N : r₂ ∈ R.N :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

include R in
theorem dichotomy {r : X} {Xa : Subgroup X} {p₀ : ℤ} (hXa : Xa = root (Rt n p₀))
    (hr : ∀ y ∈ Xa, r * y * r⁻¹ ∈ root (Rt n (p₀ + n))) {x : X} (hx : x ∈ R.N) :
    (∀ y ∈ Xa, x⁻¹ * y * x ∈ U) ∨ (∀ y ∈ Xa, (r⁻¹ * x)⁻¹ * y * (r⁻¹ * x) ∈ U) := by
  have hn : 0 < n := by have := R.three_le; omega
  obtain ⟨f, g, hf, hg, hxf, hxg⟩ := R.goodAct_of_mem_N hx
  have hk := Rt_isRoot hn (g p₀)
  have hk1 := hk.1
  have hk2 := hk.2
  rcases lt_or_gt_of_ne hk1 with h | h
  · right
    intro y hy
    have h1 := hxg (p₀ + n) _ (hr y hy)
    have h2 := hg.rt_add_n hn p₀
    have h3 : 1 ≤ Rt n (g (p₀ + n)) := by omega
    have h4 : Rt n (g (p₀ + n)) ≤ n := by
      have := (Rt_isRoot hn (g (p₀ + n))).2
      omega
    have h5 := R.root_le_U h3 h4 h1
    rw [inv_inv] at h5
    have e : (r⁻¹ * x)⁻¹ * y * (r⁻¹ * x) = x⁻¹ * (r * y * r⁻¹) * x := by group
    rw [e]
    exact h5
  · left
    intro y hy
    have h1 := hxg p₀ y (hXa ▸ hy)
    rw [inv_inv] at h1
    exact R.root_le_U (by omega) (by omega) h1

include R in
theorem t3_aux {r : X} (hrN : r ∈ R.N) (hr2 : r * r ∈ H) {Xa V : Subgroup X} (hXaU : Xa ≤ U)
    (hVU : V ≤ U) (hdecomp : ∀ u ∈ U, ∃ v ∈ V, ∃ y ∈ Xa, u = v * y)
    (hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V)
    (hrank : ∀ y ∈ Xa, r * y * r⁻¹ = 1 ∨
      r * y * r⁻¹ ∈ (Xa : Set X) * (H : Set X) * {r} * (Xa : Set X))
    (hdich : ∀ x ∈ R.N, (∀ y ∈ Xa, x⁻¹ * y * x ∈ U) ∨
      (∀ y ∈ Xa, (r⁻¹ * x)⁻¹ * y * (r⁻¹ * x) ∈ U)) :
    ∀ x ∈ R.N, ∀ b ∈ H ⊔ U,
      (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r * b * x = b₁ * (r * x) * b₂) ∨
      (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r * b * x = b₁ * x * b₂) := by
  have hUB : U ≤ H ⊔ U := le_sup_right
  have hHB : H ≤ H ⊔ U := le_sup_left
  have hVB : V ≤ H ⊔ U := hVU.trans hUB
  have hXaB : Xa ≤ H ⊔ U := hXaU.trans hUB
  have hr2' : r⁻¹ * r⁻¹ ∈ H := by
    have := H.inv_mem hr2
    simpa [mul_inv_rev] using this
  have caseA : ∀ x ∈ R.N, (∀ y ∈ Xa, x⁻¹ * y * x ∈ U) → ∀ b ∈ H ⊔ U,
      ∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r * b * x = b₁ * (r * x) * b₂ := by
    intro x hx hpos b hb
    obtain ⟨u, hu, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hb
    obtain ⟨v, hv, y, hy, rfl⟩ := hdecomp u hu
    refine ⟨r * v * r⁻¹, hVB (hrV v hv), (x⁻¹ * y * x) * (x⁻¹ * h * x),
      (H ⊔ U).mul_mem (hUB (hpos y hy)) (hHB ((R.N_normalizes_H hx h hh).2)), ?_⟩
    group
  have rank1 : ∀ b ∈ H ⊔ U, r * b * r ∈ H ⊔ U ∨
      ∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r * b * r = b₁ * r * b₂ := by
    intro b hb
    obtain ⟨u, hu, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hb
    obtain ⟨v, hv, y, hy, rfl⟩ := hdecomp u hu
    have hh1 : r * h * r⁻¹ ∈ H := (R.N_normalizes_H hrN h hh).1
    have hh' : (r * h * r⁻¹) * (r * r) ∈ H := H.mul_mem hh1 hr2
    have e : r * (v * y * h) * r =
        (r * v * r⁻¹) * (r * y * r⁻¹) * ((r * h * r⁻¹) * (r * r)) := by group
    rw [e]
    rcases hrank y hy with h0 | h0
    · left
      rw [h0, mul_one]
      exact (H ⊔ U).mul_mem (hVB (hrV v hv)) (hHB hh')
    · right
      obtain ⟨a, ha, y₂, hy₂, hz⟩ := Set.mem_mul.1 h0
      obtain ⟨c, hc, r', hr', hcr⟩ := Set.mem_mul.1 ha
      obtain ⟨y₁, hy₁, h₁, hh₁, hyh⟩ := Set.mem_mul.1 hc
      rw [Set.mem_singleton_iff] at hr'
      rw [hr'] at hcr
      have hzz : r * y * r⁻¹ = y₁ * h₁ * r * y₂ := by rw [← hz, ← hcr, ← hyh]
      refine ⟨(r * v * r⁻¹) * y₁ * h₁,
        (H ⊔ U).mul_mem ((H ⊔ U).mul_mem (hVB (hrV v hv)) (hXaB hy₁)) (hHB hh₁),
        y₂ * ((r * h * r⁻¹) * (r * r)), (H ⊔ U).mul_mem (hXaB hy₂) (hHB hh'), ?_⟩
      rw [hzz]
      group
  intro x hx b hb
  rcases hdich x hx with hA | hA
  · exact Or.inl (caseA x hx hA b hb)
  · have hx' : r⁻¹ * x ∈ R.N := R.N.mul_mem (R.N.inv_mem hrN) hx
    rcases rank1 b hb with h0 | ⟨b₁, hb₁, b₂, hb₂, hbr⟩
    · left
      refine ⟨(r * b * r) * (r⁻¹ * r⁻¹), (H ⊔ U).mul_mem h0 (hHB hr2'), 1,
        (H ⊔ U).one_mem, ?_⟩
      group
    · right
      obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := caseA (r⁻¹ * x) hx' hA b₂ hb₂
      refine ⟨b₁ * c₁, (H ⊔ U).mul_mem hb₁ hc₁, c₂, hc₂, ?_⟩
      calc r * b * x = (r * b * r) * (r⁻¹ * x) := by group
        _ = (b₁ * r * b₂) * (r⁻¹ * x) := by rw [hbr]
        _ = b₁ * (r * b₂ * (r⁻¹ * x)) := by group
        _ = b₁ * (c₁ * (r * (r⁻¹ * x)) * c₂) := by rw [hcc]
        _ = (b₁ * c₁) * x * c₂ := by group

include R in
theorem t3_r₁ : ∀ x ∈ R.N, ∀ b ∈ H ⊔ U,
    (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r₁ * b * x = b₁ * (r₁ * x) * b₂) ∨
    (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r₁ * b * x = b₁ * x * b₂) := by
  have h3 := R.three_le
  have hn : 0 < n := by omega
  obtain ⟨V, hV, hVU, hVnorm, -⟩ := R.subgroup 2 n (by norm_num) (by omega) le_rfl
  obtain ⟨a1, a2, a3⟩ := R.act₁
  refine R.t3_aux R.r₁_mem_N R.sq₁ (Xa := root 1) (V := V)
    (R.root_le_U le_rfl (by omega)) hVU ?_ ?_ ?_ ?_
  · intro u hu
    have hu' : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
    rw [intList_cons (by omega : (1 : ℤ) ≤ n), chainProd_cons,
      show (1 : ℤ) + 1 = 2 by norm_num] at hu'
    obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.1 hu'
    have hwV : w ∈ V := by
      rw [← SetLike.mem_coe, hV]
      exact hw
    refine ⟨y * w * y⁻¹, hVnorm (by norm_num) y (by simpa using hy) w hwV, y, hy,
      by group⟩
  · intro v hv
    have hv' : v ∈ chainProd root (intList 2 n) := by rw [← hV]; exact hv
    refine chainProd_conj_mem root V r₁ (intList 2 n) (fun k hk y hy => ?_) v hv'
    have hk' := mem_intList_iff.1 hk
    have h1 := mem_of_conjBy_inv (a3 k hk'.1 hk'.2).1 hy
    have h2 : r₁ * y * r₁⁻¹ ∈ chainProd root (intList 2 n) :=
      mem_chainProd_of_mem root (k := (n : ℤ) + 2 - k)
        (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
    rw [← hV] at h2
    exact h2
  · intro y hy
    have hz : r₁ * y * r₁⁻¹ ∈ root (-1) := mem_of_conjBy_inv a1 hy
    by_cases h : r₁ * y * r₁⁻¹ = 1
    · exact Or.inl h
    · exact Or.inr (R.rank₁ _ hz h)
  · intro x hx
    refine R.dichotomy (p₀ := 0) (r := r₁) ?_ ?_ hx
    · rw [Rt_zero hn]
    · intro y hy
      have hz : r₁ * y * r₁⁻¹ ∈ root (-1) := mem_of_conjBy_inv a1 hy
      rwa [zero_add, Rt_self hn]

include R in
theorem t3_r₂ : ∀ x ∈ R.N, ∀ b ∈ H ⊔ U,
    (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r₂ * b * x = b₁ * (r₂ * x) * b₂) ∨
    (∃ b₁ ∈ H ⊔ U, ∃ b₂ ∈ H ⊔ U, r₂ * b * x = b₁ * x * b₂) := by
  have h3 := R.three_le
  have hn : 0 < n := by omega
  obtain ⟨V, hV, hVU, -, -⟩ := R.subgroup 1 ((n : ℤ) - 1) le_rfl (by omega) (by omega)
  obtain ⟨b1, b2, b3⟩ := R.act₂
  refine R.t3_aux R.r₂_mem_N R.sq₂ (Xa := root n) (V := V)
    (R.root_le_U (by omega) le_rfl) hVU ?_ ?_ ?_ ?_
  · intro u hu
    have hu' : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
    rw [intList_snoc (by omega : (1 : ℤ) ≤ n), chainProd_append,
      chainProd_singleton] at hu'
    obtain ⟨w, hw, y, hy, rfl⟩ := Set.mem_mul.1 hu'
    refine ⟨w, ?_, y, hy, rfl⟩
    rw [← SetLike.mem_coe, hV]
    exact hw
  · intro v hv
    have hv' : v ∈ chainProd root (intList 1 ((n : ℤ) - 1)) := by rw [← hV]; exact hv
    refine chainProd_conj_mem root V r₂ (intList 1 ((n : ℤ) - 1)) (fun k hk y hy => ?_) v hv'
    have hk' := mem_intList_iff.1 hk
    have h1 := mem_of_conjBy_inv (b3 k hk'.1 hk'.2).1 hy
    have h2 : r₂ * y * r₂⁻¹ ∈ chainProd root (intList 1 ((n : ℤ) - 1)) :=
      mem_chainProd_of_mem root (k := (n : ℤ) - k)
        (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
    rw [← hV] at h2
    exact h2
  · intro y hy
    have hz : r₂ * y * r₂⁻¹ ∈ root (-(n : ℤ)) := mem_of_conjBy_inv b1 hy
    by_cases h : r₂ * y * r₂⁻¹ = 1
    · exact Or.inl h
    · exact Or.inr (R.rank₂ _ hz h)
  · intro x hx
    refine R.dichotomy (p₀ := (n : ℤ) - 1) (r := r₂) ?_ ?_ hx
    · rw [Rt_pred hn]
    · intro y hy
      have hz : r₂ * y * r₂⁻¹ ∈ root (-(n : ℤ)) := mem_of_conjBy_inv b1 hy
      rwa [Rt_pred_add hn]

include R in
theorem t4_aux {r : X} {Xa : Subgroup X} (hne : Xa ≠ ⊥) (hXaU : Xa ≤ U)
    (hneg : ∀ y ∈ Xa, r * y * r⁻¹ ∈ chainProd root ((intList 1 n).map Neg.neg)) :
    ¬ (({r} : Set X) * ((H ⊔ U : Subgroup X) : Set X) * {r⁻¹} ⊆
      ((H ⊔ U : Subgroup X) : Set X)) := by
  intro hsub
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyB : y ∈ H ⊔ U := (le_sup_right : U ≤ H ⊔ U) (hXaU hy)
  have hmem : r * y * r⁻¹ ∈ ({r} : Set X) * ((H ⊔ U : Subgroup X) : Set X) * {r⁻¹} :=
    Set.mem_mul.2 ⟨r * y, Set.mem_mul.2 ⟨r, rfl, y, hyB, rfl⟩, r⁻¹, rfl, rfl⟩
  have h1 := R.meet_one _ (hsub hmem) (hneg y hy)
  apply hy1'
  have := congrArg (fun z => r⁻¹ * z * r) h1
  simpa [mul_assoc] using this

include R in
theorem t4_r₁ : ¬ (({r₁} : Set X) * ((H ⊔ U : Subgroup X) : Set X) * {r₁⁻¹} ⊆
    ((H ⊔ U : Subgroup X) : Set X)) := by
  have h3 := R.three_le
  refine R.t4_aux (Xa := root 1) (R.ne_bot 1 (isRoot_of_pos_le le_rfl (by omega)))
    (R.root_le_U le_rfl (by omega)) ?_
  intro y hy
  have hz : r₁ * y * r₁⁻¹ ∈ root (-1) := mem_of_conjBy_inv R.act₁.1 hy
  exact R.mem_chainProd_neg le_rfl (by omega) hz

include R in
theorem t4_r₂ : ¬ (({r₂} : Set X) * ((H ⊔ U : Subgroup X) : Set X) * {r₂⁻¹} ⊆
    ((H ⊔ U : Subgroup X) : Set X)) := by
  have h3 := R.three_le
  refine R.t4_aux (Xa := root n) (R.ne_bot n (isRoot_of_pos_le (by omega) le_rfl))
    (R.root_le_U (by omega) le_rfl) ?_
  intro y hy
  have hz : r₂ * y * r₂⁻¹ ∈ root (-(n : ℤ)) := mem_of_conjBy_inv R.act₂.1 hy
  exact R.mem_chainProd_neg (by omega) le_rfl hz

open Classical in
open Classical in
theorem isTitsSystem_of_two_generators {G : Type*} [Group G] {B N : Subgroup G}
    [(cartan B N).Normal] {n₁ n₂ : N}
    (hgen : B ⊔ N = ⊤)
    (hord : ∀ i : Fin 2, orderOf ((![n₁, n₂] i : N) : WeylGroup B N) = 2)
    (hclos : Subgroup.closure (Set.range fun i : Fin 2 =>
      ((![n₁, n₂] i : N) : WeylGroup B N)) = ⊤)
    (hmul : ∀ i : Fin 2, ∀ x : N,
      ({((![n₁, n₂] i : N) : G)} : Set G) * (B : Set G) * {(x : G)} ⊆
        dc B N (((![n₁, n₂] i : N) : WeylGroup B N) * (x : WeylGroup B N)) ∪
          dc B N (x : WeylGroup B N))
    (hne : ∀ i : Fin 2, ¬ ({((![n₁, n₂] i : N) : G)} : Set G) * (B : Set G) *
      {((![n₁, n₂] i : N) : G)⁻¹} ⊆ (B : Set G)) :
    IsTitsSystem B N
      {((![n₁, n₂] 0 : N) : WeylGroup B N), ((![n₁, n₂] 1 : N) : WeylGroup B N)} := by
  let S : Finset (WeylGroup B N) :=
    {((![n₁, n₂] 0 : N) : WeylGroup B N), ((![n₁, n₂] 1 : N) : WeylGroup B N)}
  have hS : ∀ s : WeylGroup B N, s ∈ S ↔
      ∃ i : Fin 2, ((![n₁, n₂] i : N) : WeylGroup B N) = s := by
    intro s
    dsimp [S]
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
  have key : ∀ n' : N, ((n' : N) : WeylGroup B N) ∈ S →
      ∃ (i : Fin 2) (h' : G), h' ∈ B ∧ (n' : G) = (![n₁, n₂] i : G) * h' := by
    intro n' hn'
    obtain ⟨i, hi⟩ := (hS _).1 hn'
    refine ⟨i, (![n₁, n₂] i : G)⁻¹ * n', mk_eq_mk_iff.1 hi, by simp⟩
  refine { gen := hgen, involution := ?_, closure_eq := ?_, mul_subset := ?_, ne := ?_ }
  · intro s hs
    obtain ⟨i, rfl⟩ := (hS s).1 hs
    exact hord i
  · have hcoe : (S : Set (WeylGroup B N)) =
        Set.range (fun i : Fin 2 => ((![n₁, n₂] i : N) : WeylGroup B N)) := by
      ext s
      exact hS s
    rw [hcoe]
    exact hclos
  · intro n' m hn'
    obtain ⟨i, h', hh', e⟩ := key n' hn'
    have hmk : ((![n₁, n₂] i : N) : WeylGroup B N) = (n' : WeylGroup B N) :=
      mk_eq_mk_iff.2 (by
        have : (![n₁, n₂] i : G)⁻¹ * (n' : G) = h' := by rw [e]; simp
        rw [this]; exact hh')
    intro x hx
    have hxnp : x ∈ ({((![n₁, n₂] i : N) : G)} : Set G) * (B : Set G) * {(m : G)} := by
      obtain ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩ := hx
      refine Set.mem_mul.2 ⟨(![n₁, n₂] i : G) * (h' * b), Set.mem_mul.2
        ⟨![n₁, n₂] i, rfl, h' * b, B.mul_mem hh' hb, rfl⟩, m, rfl, ?_⟩
      rw [e]; simp [mul_assoc]
    rcases hmul i m hxnp with h1 | h1
    · left
      rwa [hmk] at h1
    · exact Or.inr h1
  · intro n' hn' heq
    obtain ⟨i, h', hh', e⟩ := key n' hn'
    have hmk : ((![n₁, n₂] i : N) : WeylGroup B N) = (n' : WeylGroup B N) :=
      mk_eq_mk_iff.2 (by
        have : (![n₁, n₂] i : G)⁻¹ * (n' : G) = h' := by rw [e]; simp
        rw [this]; exact hh')
    have hsq : (n' : G) * n' ∈ B := by
      have h2 := hord i
      have h3 : ((![n₁, n₂] i : N) : WeylGroup B N) *
          (![n₁, n₂] i : N) = 1 := by
        have := pow_orderOf_eq_one ((![n₁, n₂] i : N) : WeylGroup B N)
        rw [h2, sq] at this
        exact this
      rw [hmk] at h3
      have : ((n' * n' : N) : WeylGroup B N) = 1 := by
        rw [QuotientGroup.mk_mul]; exact h3
      simpa using mk_eq_one_iff.1 this
    refine hne i ?_
    rintro x ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
    have hc : h'⁻¹ * b * h' ∈ B := B.mul_mem (B.mul_mem (B.inv_mem hh') hb) hh'
    have h4 : (n' : G) * (h'⁻¹ * b * h') * n' ∈ (B : Set G) := by
      rw [← heq]
      exact Set.mem_mul.2 ⟨n' * (h'⁻¹ * b * h'), Set.mem_mul.2
        ⟨n', rfl, h'⁻¹ * b * h', hc, rfl⟩, n', rfl, rfl⟩
    have h5 : (![n₁, n₂] i : G) * b * ((![n₁, n₂] i : G))⁻¹ =
        ((n' : G) * (h'⁻¹ * b * h') * n') * ((n' : G) * n')⁻¹ := by
      have : (![n₁, n₂] i : G) = (n' : G) * h'⁻¹ := by rw [e]; simp
      rw [this]; group
    show (![n₁, n₂] i : G) * b * ((![n₁, n₂] i : G))⁻¹ ∈ B
    rw [h5]
    exact B.mul_mem h4 (B.inv_mem hsq)

end RGD2Core

end CFSG.GH74.GLS.SP
