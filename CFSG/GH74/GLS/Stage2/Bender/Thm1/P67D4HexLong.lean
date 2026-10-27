module

public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair

variable {X : Type*} [Group X]

theorem Rt_even_iff {n : ℕ} (hn : (n : ℤ) % 2 = 0) (p : ℤ) :
    Rt n p % 2 = 0 ↔ p % 2 = 1 := by
  unfold Rt
  have h2 : (p % (2 * (n : ℤ))) % 2 = p % 2 :=
    Int.emod_emod_of_dvd _ ⟨(n : ℤ), rfl⟩
  split_ifs with h
  · omega
  · omega

@[expose] def IsEvenAff (f : ℤ → ℤ) : Prop :=
  (∃ c, c % 2 = 0 ∧ ∀ q, f q = q + c) ∨ ∃ c, c % 2 = 0 ∧ ∀ q, f q = c - q

theorem IsEvenAff.comp {f g : ℤ → ℤ} (hf : IsEvenAff f) (hg : IsEvenAff g) :
    IsEvenAff (fun q => f (g q)) := by
  rcases hf with ⟨a, ha2, ha⟩ | ⟨a, ha2, ha⟩ <;> rcases hg with ⟨b, hb2, hb⟩ | ⟨b, hb2, hb⟩
  · exact Or.inl ⟨b + a, by omega, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inr ⟨b + a, by omega, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inr ⟨a - b, by omega, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩
  · exact Or.inl ⟨a - b, by omega, fun q => by show f (g q) = _; rw [hb, ha]; ring⟩

theorem IsEvenAff.parity {f : ℤ → ℤ} (hf : IsEvenAff f) (q : ℤ) : f q % 2 = q % 2 := by
  rcases hf with ⟨c, hc2, hc⟩ | ⟨c, hc2, hc⟩
  · rw [hc]; omega
  · rw [hc]; omega

theorem isEvenAff_id : IsEvenAff (fun q => q) := Or.inl ⟨0, by norm_num, fun q => by simp⟩

@[expose] def GoodActEven (n : ℕ) (root : ℤ → Subgroup X) (m : X) : Prop :=
  ∃ f g : ℤ → ℤ, IsEvenAff f ∧ IsEvenAff g ∧ ActsPos n root m f ∧ ActsPos n root m⁻¹ g

theorem GoodActEven.mul {n : ℕ} {root : ℤ → Subgroup X} {m m' : X} (h : GoodActEven n root m)
    (h' : GoodActEven n root m') : GoodActEven n root (m * m') := by
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := h
  obtain ⟨f', g', hf', hg', hmf', hmg'⟩ := h'
  refine ⟨fun q => f (f' q), fun q => g' (g q), hf.comp hf', hg'.comp hg, hmf.mul hmf', ?_⟩
  rw [mul_inv_rev]
  exact hmg'.mul hmg

theorem GoodActEven.inv {n : ℕ} {root : ℤ → Subgroup X} {m : X} (h : GoodActEven n root m) :
    GoodActEven n root m⁻¹ := by
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := h
  exact ⟨g, f, hg, hf, hmg, by rwa [inv_inv]⟩

theorem GoodActEven.one {n : ℕ} {root : ℤ → Subgroup X} : GoodActEven n root (1 : X) :=
  ⟨fun q => q, fun q => q, isEvenAff_id, isEvenAff_id, ActsPos.one,
    by rw [inv_one]; exact ActsPos.one⟩

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

include R in
theorem goodActEven_r₁ (hn : n % 2 = 0) : GoodActEven n root r₁ :=
  ⟨fun q => (n : ℤ) - q, fun q => (n : ℤ) - q, Or.inr ⟨n, by omega, fun _ => rfl⟩,
    Or.inr ⟨n, by omega, fun _ => rfl⟩, R.actsPos_r₁, R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁⟩

include R in
theorem goodActEven_r₂ (hn : n % 2 = 0) : GoodActEven n root r₂ :=
  ⟨fun q => (n : ℤ) - 2 - q, fun q => (n : ℤ) - 2 - q,
    Or.inr ⟨(n : ℤ) - 2, by omega, fun _ => rfl⟩, Or.inr ⟨(n : ℤ) - 2, by omega, fun _ => rfl⟩,
    R.actsPos_r₂, R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂⟩

include R in
theorem goodActEven_of_mem_H {h : X} (hh : h ∈ H) : GoodActEven n root h :=
  ⟨fun q => q, fun q => q, isEvenAff_id, isEvenAff_id, R.actsPos_of_mem_H hh,
    R.actsPos_of_mem_H (H.inv_mem hh)⟩

include R in
theorem goodActEven_of_mem_N (hn : n % 2 = 0) {m : X} (hm : m ∈ R.N) :
    GoodActEven n root m := by
  unfold N at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact R.goodActEven_of_mem_H hx
    · rcases hx with rfl | rfl
      · exact R.goodActEven_r₁ hn
      · exact R.goodActEven_r₂ hn
  | one => exact GoodActEven.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

end RGD2

@[expose] def longSub (n : ℕ) (root : ℤ → Subgroup X) : Subgroup X :=
  Subgroup.closure {x | ∃ k, IsRoot n k ∧ k % 2 = 0 ∧ x ∈ root k}

theorem root_le_longSub {n : ℕ} {root : ℤ → Subgroup X} {k : ℤ} (hk : IsRoot n k)
    (hk2 : k % 2 = 0) : root k ≤ longSub n root :=
  fun _ hx => Subgroup.subset_closure ⟨k, hk, hk2, hx⟩

theorem conj_mem_longSub {n : ℕ} (hn : 0 < n) (hn2 : n % 2 = 0) {root : ℤ → Subgroup X} {m : X}
    (hm : GoodActEven n root m) {x : X} (hx : x ∈ longSub n root) :
    m * x * m⁻¹ ∈ longSub n root := by
  obtain ⟨f, g, hf, hg, hmf, hmg⟩ := hm
  unfold longSub at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, hk2, hxk⟩ := hx
    obtain ⟨q, hq⟩ : ∃ q : ℤ, Rt n q = k := by
      by_cases hpos : 0 < k
      · exact ⟨k - 1, by rw [Rt_of_lt (by omega) (by have := hk.2; omega)]; ring⟩
      · refine ⟨(n : ℤ) - k - 1, ?_⟩
        have hk3 : k < 0 := by have := hk.1; omega
        have hk4 : -(n : ℤ) ≤ k := by have := hk.2; omega
        rw [Rt_of_ge (by omega) (by omega)]
        ring
    have hqodd : q % 2 = 1 := (Rt_even_iff (by exact_mod_cast hn2) q).1 (hq ▸ hk2)
    have h1 := hmf q x (hq ▸ hxk)
    refine Subgroup.subset_closure ⟨Rt n (f q), Rt_isRoot hn _, ?_, h1⟩
    rw [Rt_even_iff (by exact_mod_cast hn2), hf.parity]
    exact hqodd
  | one => simp
  | mul x y _ _ hx hy =>
    have e : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end CFSG.GH74.GLS.SP
