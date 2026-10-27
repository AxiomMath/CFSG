module

public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

theorem Rt_zero {n : ℕ} (hn : 0 < n) : Rt n 0 = 1 := by
  rw [Rt_of_lt (le_refl 0) (by omega)]
  ring

theorem Rt_self {n : ℕ} (hn : 0 < n) : Rt n n = -1 := by
  rw [Rt_of_ge (le_refl _) (by omega)]
  ring

theorem Rt_pred {n : ℕ} (hn : 0 < n) : Rt n ((n : ℤ) - 1) = n := by
  rw [Rt_of_lt (by omega) (by omega)]
  ring

theorem Rt_pred_add {n : ℕ} (hn : 0 < n) : Rt n (((n : ℤ) - 1) + n) = -(n : ℤ) := by
  rw [Rt_of_ge (by omega) (by omega)]
  ring

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

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
theorem H_le_N : H ≤ R.N := fun _ hh => Subgroup.subset_closure (Or.inl hh)

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
    have e : r * (v * y * h) * r = (r * v * r⁻¹) * (r * y * r⁻¹) * ((r * h * r⁻¹) * (r * r)) := by
      group
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
      refine ⟨(r * b * r) * (r⁻¹ * r⁻¹), (H ⊔ U).mul_mem h0 (hHB hr2'), 1, (H ⊔ U).one_mem, ?_⟩
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
    refine ⟨y * w * y⁻¹, hVnorm (by norm_num) y (by simpa using hy) w hwV, y, hy, by group⟩
  · intro v hv
    have hv' : v ∈ chainProd root (intList 2 n) := by rw [← hV]; exact hv
    refine chainProd_conj_mem root V r₁ (intList 2 n) (fun k hk y hy => ?_) v hv'
    have hk' := mem_intList_iff.1 hk
    have h1 := mem_of_conjBy_inv (a3 k hk'.1 hk'.2).1 hy
    have h2 : r₁ * y * r₁⁻¹ ∈ chainProd root (intList 2 n) :=
      mem_chainProd_of_mem root (k := (n : ℤ) + 2 - k) (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
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
    rw [intList_snoc (by omega : (1 : ℤ) ≤ n), chainProd_append, chainProd_singleton] at hu'
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
      mem_chainProd_of_mem root (k := (n : ℤ) - k) (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
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
    (hneg : ∀ y ∈ Xa, r * y * r⁻¹ ∈ negGen n root) :
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
  exact mem_negGen_of_mem (k := 1) le_rfl (by omega) hz

include R in
theorem t4_r₂ : ¬ (({r₂} : Set X) * ((H ⊔ U : Subgroup X) : Set X) * {r₂⁻¹} ⊆
    ((H ⊔ U : Subgroup X) : Set X)) := by
  have h3 := R.three_le
  refine R.t4_aux (Xa := root n) (R.ne_bot n (isRoot_of_pos_le (by omega) le_rfl))
    (R.root_le_U (by omega) le_rfl) ?_
  intro y hy
  have hz : r₂ * y * r₂⁻¹ ∈ root (-(n : ℤ)) := mem_of_conjBy_inv R.act₂.1 hy
  exact mem_negGen_of_mem (k := (n : ℤ)) (by omega) le_rfl hz

end RGD2

end CFSG.GH74.GLS.SP
