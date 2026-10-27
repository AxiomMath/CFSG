module

public import CFSG.RankThree.SubgroupLists.ExtraspecialCore
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbedding.KFactProofs.OrbitsCube

open scoped commutatorElement
open CFSG.RankThree.SubgroupLists

theorem card_center_of_card_pow_three {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (hcard : Nat.card S = p ^ 3) (hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) :
    Nat.card (Subgroup.center S) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (G := S) (p := p)
    (n := 3) hcard (by norm_num)
  have hdvd : Nat.card (Subgroup.center S) ∣ p ^ 3 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  by_contra hk1
  have hk1' : k ≠ 1 := fun h => hk1 (by rw [h, pow_one])
  have hk2 : 2 ≤ k := by omega
  have hidx : (Subgroup.center S).index ∣ p := by
    have h := Subgroup.index_mul_card (Subgroup.center S)
    rw [hk, hcard] at h
    obtain ⟨j, hj⟩ : ∃ j, 3 = k + j := ⟨3 - k, by omega⟩
    have hj' : (Subgroup.center S).index = p ^ j := by
      have h' : (Subgroup.center S).index * p ^ k = p ^ k * p ^ j := by
        rw [h, hj, pow_add]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos k) (by rw [h']; ring)
    rw [hj']
    have : j ≤ 1 := by omega
    interval_cases j
    · simp
    · simp
  have hcyc : IsCyclic (S ⧸ Subgroup.center S) := by
    apply isCyclic_of_card_dvd_prime (p := p)
    rwa [← Subgroup.index]
  have hcomm := isMulCommutative_of_isCyclic_quotient_center_self S
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact hab (congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : S) ⟨b, hb⟩))

theorem commutator_le_center_of_card_pow_three {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (hcard : Nat.card S = p ^ 3) (hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) :
    commutator S ≤ Subgroup.center S := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ := card_center_of_card_pow_three hp S hcard hnc
  have hq : Nat.card (S ⧸ Subgroup.center S) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hcard, hZ] at h
    have hp0 : 0 < p := hp.pos
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at h
    exact (Nat.eq_of_mul_eq_mul_right hp0 h).symm
  have hcomm : IsMulCommutative (S ⧸ Subgroup.center S) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm.is_comm.comm _ _)

section NormalForm

variable {R : Type*} [Group R]

theorem normalForm_mul {x y : R} (hclass : commutator R ≤ Subgroup.center R) (i j i' j' : ℕ)
    {w w' : R} (hw : w ∈ Subgroup.center R) :
    ∃ c ∈ Subgroup.center R, x ^ i * y ^ j * w * (x ^ i' * y ^ j' * w') =
      x ^ (i + i') * y ^ (j + j') * (c * w') := by
  have hc := commutatorElement_mem_center hclass (y ^ j) (x ^ i')
  have hcc := Subgroup.mem_center_iff.mp hc
  have hww := Subgroup.mem_center_iff.mp hw
  have hswap : y ^ j * x ^ i' = ⁅y ^ j, x ^ i'⁆ * (x ^ i' * y ^ j) := by
    rw [commutatorElement_def]; group
  refine ⟨⁅y ^ j, x ^ i'⁆ * w, mul_mem hc hw, ?_⟩
  have e1 : x ^ i' * w = w * x ^ i' := hww _
  have e2 : y ^ j' * w = w * y ^ j' := hww _
  have e3 : x ^ i * ⁅y ^ j, x ^ i'⁆ = ⁅y ^ j, x ^ i'⁆ * x ^ i := hcc _
  have e4 : x ^ (i + i') * y ^ (j + j') * ⁅y ^ j, x ^ i'⁆ =
      ⁅y ^ j, x ^ i'⁆ * (x ^ (i + i') * y ^ (j + j')) := hcc _
  calc x ^ i * y ^ j * w * (x ^ i' * y ^ j' * w')
      = x ^ i * y ^ j * (w * x ^ i') * y ^ j' * w' := by group
    _ = x ^ i * (y ^ j * x ^ i') * (w * y ^ j') * w' := by rw [← e1]; group
    _ = x ^ i * (y ^ j * x ^ i') * (y ^ j' * w) * w' := by rw [← e2]
    _ = x ^ i * (⁅y ^ j, x ^ i'⁆ * (x ^ i' * y ^ j)) * y ^ j' * (w * w') := by rw [hswap]; group
    _ = (x ^ i * ⁅y ^ j, x ^ i'⁆) * (x ^ i' * y ^ j) * y ^ j' * (w * w') := by group
    _ = ⁅y ^ j, x ^ i'⁆ * (x ^ (i + i') * y ^ (j + j')) * (w * w') := by rw [e3]; group
    _ = x ^ (i + i') * y ^ (j + j') * ⁅y ^ j, x ^ i'⁆ * (w * w') := by rw [e4]
    _ = x ^ (i + i') * y ^ (j + j') * (⁅y ^ j, x ^ i'⁆ * w * w') := by group

theorem exists_normalForm {p : ℕ} (hp : 0 < p) (hclass : commutator R ≤ Subgroup.center R)
    {x y : R} (hgen : Subgroup.closure ({x, y} : Set R) = ⊤) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (t : R) : ∃ i j : ℕ, ∃ w ∈ Subgroup.center R, t = x ^ i * y ^ j * w := by
  have hmul : ∀ a b : R, (∃ i j : ℕ, ∃ w ∈ Subgroup.center R, a = x ^ i * y ^ j * w) →
      (∃ i j : ℕ, ∃ w ∈ Subgroup.center R, b = x ^ i * y ^ j * w) →
      ∃ i j : ℕ, ∃ w ∈ Subgroup.center R, a * b = x ^ i * y ^ j * w := by
    rintro a b ⟨i, j, w, hw, rfl⟩ ⟨i', j', w', hw', rfl⟩
    obtain ⟨c, hc, h⟩ := normalForm_mul (x := x) (y := y) hclass i j i' j' (w' := w') hw
    exact ⟨i + i', j + j', c * w', mul_mem hc hw', h⟩
  have hinvpow : ∀ (g : R) (k : ℕ), g ^ p = 1 → (g ^ k)⁻¹ = g ^ (k * (p - 1)) := by
    intro g k hg
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add]
    have : k + k * (p - 1) = p * k := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [this, pow_mul, hg, one_pow]
  have ht : t ∈ Subgroup.closure ({x, y} : Set R) := by rw [hgen]; exact Subgroup.mem_top t
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact ⟨1, 0, 1, one_mem _, by simp⟩
    · exact ⟨0, 1, 1, one_mem _, by simp⟩
  | one => exact ⟨0, 0, 1, one_mem _, by simp⟩
  | mul a b ha hb iha ihb => exact hmul a b iha ihb
  | inv a ha iha =>
    obtain ⟨i, j, w, hw, rfl⟩ := iha
    have h1 : (x ^ i * y ^ j * w)⁻¹ = w⁻¹ * (y ^ j)⁻¹ * (x ^ i)⁻¹ := by group
    rw [h1, hinvpow y j hy, hinvpow x i hx]
    exact hmul _ _ (hmul _ _ ⟨0, 0, w⁻¹, inv_mem hw, by simp⟩
      ⟨0, j * (p - 1), 1, one_mem _, by simp⟩) ⟨i * (p - 1), 0, 1, one_mem _, by simp⟩

theorem pow_normalForm (hclass : commutator R ≤ Subgroup.center R) (x y : R) (a b e i : ℕ) :
    ∃ c ∈ Subgroup.center R,
      (x ^ a * y ^ b * ⁅x, y⁆ ^ e) ^ i = x ^ (a * i) * y ^ (b * i) * c := by
  have hz : ⁅x, y⁆ ∈ Subgroup.center R := commutatorElement_mem_center hclass x y
  have hze : ⁅x, y⁆ ^ e ∈ Subgroup.center R := pow_mem hz e
  have hcomm : Commute (x ^ a * y ^ b) (⁅x, y⁆ ^ e) := Subgroup.mem_center_iff.mp hze _
  refine ⟨⁅y ^ b, x ^ a⁆ ^ (∑ k ∈ Finset.range i, k) * (⁅x, y⁆ ^ e) ^ i,
    mul_mem (pow_mem (commutatorElement_mem_center hclass _ _) _) (pow_mem hze _), ?_⟩
  rw [hcomm.mul_pow, mul_pow_eq_class_two hclass (x ^ a) (y ^ b) i, ← pow_mul, ← pow_mul]
  group

theorem map_normalForm (hclass : commutator R ≤ Subgroup.center R) (x y : R) (α : MulAut R)
    (a b c d e f i j : ℕ) {w : R} (hw : w ∈ Subgroup.center R)
    (hαx : α x = x ^ a * y ^ b * ⁅x, y⁆ ^ e) (hαy : α y = x ^ c * y ^ d * ⁅x, y⁆ ^ f) :
    ∃ w' ∈ Subgroup.center R,
      α (x ^ i * y ^ j * w) = x ^ (a * i + c * j) * y ^ (b * i + d * j) * w' := by
  have hαw : α w ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.mp hw (α.symm g)
    have h2 := congrArg α h
    simpa using h2
  obtain ⟨c₁, hc₁, h₁⟩ := pow_normalForm hclass x y a b e i
  obtain ⟨c₂, hc₂, h₂⟩ := pow_normalForm hclass x y c d f j
  obtain ⟨c₃, hc₃, h₃⟩ := normalForm_mul (x := x) (y := y) hclass (a * i) (b * i) (c * j) (d * j)
    (w := c₁) (w' := c₂) hc₁
  refine ⟨c₃ * c₂ * α w, ?_, ?_⟩
  · exact mul_mem (mul_mem hc₃ hc₂) hαw
  · rw [map_mul, map_mul, map_pow, map_pow, hαx, hαy, h₁, h₂, h₃]
    simp only [mul_assoc]

theorem commutator_normalForm (hclass : commutator R ≤ Subgroup.center R) (x y : R)
    (i j A B : ℕ) {w w' : R} (hw : w ∈ Subgroup.center R) (hw' : w' ∈ Subgroup.center R) :
    ⁅x ^ i * y ^ j * w, x ^ A * y ^ B * w'⁆ = ⁅x, y⁆ ^ (B * i) * (⁅x, y⁆⁻¹) ^ (A * j) := by
  have hwg : ∀ g : R, ⁅w, g⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp hw g).symm
  have hwg' : ∀ g : R, ⁅g, w'⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp hw' g)
  simp only [commutatorElement_mul_left hclass, commutatorElement_mul_right hclass,
    commutatorElement_pow_left hclass, commutatorElement_pow_right hclass, commutatorElement_self,
    hwg, hwg', one_pow, mul_one, one_mul]
  rw [← pow_mul, ← pow_mul, (commutatorElement_inv x y).symm]

theorem commutator_ne_one_of_anisotropic {p : ℕ} (hp : p.Prime)
    (hclass : commutator R ≤ Subgroup.center R) {x y : R}
    (hgen : Subgroup.closure ({x, y} : Set R) = ⊤) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : ⁅x, y⁆ ≠ 1) (α : MulAut R) (a b c d e f : ℕ)
    (hαx : α x = x ^ a * y ^ b * ⁅x, y⁆ ^ e) (hαy : α y = x ^ c * y ^ d * ⁅x, y⁆ ^ f)
    (hΔ : ∀ i j : ZMod p, (i ≠ 0 ∨ j ≠ 0) →
      i * (b * i + d * j) - j * (a * i + c * j) ≠ 0)
    {t : R} (ht : t ∉ Subgroup.center R) : ⁅t, α t⁆ ≠ 1 := by
  have hp0 : 0 < p := hp.pos
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, j, w, hw, rfl⟩ := exists_normalForm hp0 hclass hgen hx hy t
  obtain ⟨w', hw', hα⟩ := map_normalForm hclass x y α a b c d e f i j hw hαx hαy
  rw [hα, commutator_normalForm hclass x y i j _ _ hw hw']
  have hzp : ⁅x, y⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left hclass, hx]
    simp [commutatorElement_def]
  have hzo : orderOf ⁅x, y⁆ = p := orderOf_eq_prime hzp hz
  intro h1
  have h2 : ⁅x, y⁆ ^ ((((b * i + d * j) * i : ℕ) : ℤ) - (((a * i + c * j) * j : ℕ) : ℤ)) = 1 := by
    rw [sub_eq_add_neg, zpow_add, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow]
    exact h1
  have h3 : (p : ℤ) ∣ (((b * i + d * j) * i : ℕ) : ℤ) - (((a * i + c * j) * j : ℕ) : ℤ) := by
    rw [← hzo]
    exact orderOf_dvd_iff_zpow_eq_one.2 h2
  have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
  push_cast at h5
  by_cases hij : (i : ZMod p) ≠ 0 ∨ (j : ZMod p) ≠ 0
  · exact hΔ i j hij (by linear_combination h5)
  · push Not at hij
    obtain ⟨hi0, hj0⟩ := hij
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff i p).1 hi0
    obtain ⟨n, hn⟩ := (ZMod.natCast_eq_zero_iff j p).1 hj0
    apply ht
    have : x ^ i * y ^ j * w = w := by
      rw [hm, hn, pow_mul, pow_mul, hx, hy]
      simp
    rw [this]
    exact hw

theorem automorphism_commutator_ne {p : ℕ} (hp : p.Prime)
    (hclass : commutator R ≤ Subgroup.center R) {x y : R} (hx : x ^ p = 1) (hz : ⁅x, y⁆ ≠ 1)
    (α : MulAut R) (a b c d e f : ℕ)
    (hαx : α x = x ^ a * y ^ b * ⁅x, y⁆ ^ e) (hαy : α y = x ^ c * y ^ d * ⁅x, y⁆ ^ f)
    (hdet : (a : ZMod p) * d - b * c ≠ 1) : α ⁅x, y⁆ ≠ ⁅x, y⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have hzc : ⁅x, y⁆ ∈ Subgroup.center R := commutatorElement_mem_center hclass x y
  have hα : α ⁅x, y⁆ = ⁅x, y⁆ ^ (d * a) * (⁅x, y⁆⁻¹) ^ (c * b) := by
    rw [show α ⁅x, y⁆ = ⁅α x, α y⁆ from map_commutatorElement α.toMonoidHom x y, hαx, hαy,
      commutator_normalForm hclass x y a b c d (pow_mem hzc e) (pow_mem hzc f)]
  have hzp : ⁅x, y⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left hclass, hx]
    simp [commutatorElement_def]
  have hzo : orderOf ⁅x, y⁆ = p := orderOf_eq_prime hzp hz
  rw [hα]
  intro h1
  rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_succ'] at h1
  have h2 := pow_eq_pow_iff_modEq.1 h1
  rw [hzo] at h2
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  push_cast at h3
  exact hdet (by linear_combination h3)

end NormalForm

private theorem exists_lift {G : Type*} [Group G] {p : ℕ} (S : Subgroup G) {x y : G}
    (hSxy : S = Subgroup.closure ({x, y} : Set G)) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : ⁅x, y⁆ ≠ 1) {h : G} (hh : h ∈ Subgroup.normalizer (S : Set G)) (a b c d e f : ℕ)
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ e)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ f) :
    ∃ (xS yS : S) (α : MulAut S), (xS : G) = x ∧ (yS : G) = y ∧
      (∀ u : S, ((α u : S) : G) = h * u * h⁻¹) ∧ Subgroup.closure ({xS, yS} : Set S) = ⊤ ∧
      xS ^ p = 1 ∧ yS ^ p = 1 ∧ (⁅xS, yS⁆ : S) ≠ 1 ∧
      α xS = xS ^ a * yS ^ b * (⁅xS, yS⁆ : S) ^ e ∧
      α yS = xS ^ c * yS ^ d * (⁅xS, yS⁆ : S) ^ f := by
  have hxS : x ∈ S := hSxy ▸ Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := hSxy ▸ Subgroup.subset_closure (by simp)
  obtain ⟨xS, hxc⟩ : ∃ xS : S, (xS : G) = x := ⟨⟨x, hxS⟩, rfl⟩
  obtain ⟨yS, hyc⟩ : ∃ yS : S, (yS : G) = y := ⟨⟨y, hyS⟩, rfl⟩
  have hgen : Subgroup.closure ({xS, yS} : Set S) = ⊤ := by
    have h1 : ({xS, yS} : Set S) = ((↑) : S → G) ⁻¹' ({x, y} : Set G) := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl)
        · left; exact hxc
        · right; exact hyc
      · rintro (h | h)
        · left; exact Subtype.ext (h.trans hxc.symm)
        · right; exact Subtype.ext (h.trans hyc.symm)
    rw [h1]
    subst hSxy
    exact Subgroup.closure_closure_coe_preimage
  have hcomm : ∀ u v : S, (((⁅u, v⁆ : S)) : G) = ⁅(u : G), (v : G)⁆ := fun u v => by
    simp [commutatorElement_def]
  let α : MulAut S := S.normalizerMonoidHom ⟨h, hh⟩
  have hα : ∀ u : S, ((α u : S) : G) = h * u * h⁻¹ := fun u => rfl
  refine ⟨xS, yS, α, hxc, hyc, hα, hgen, Subtype.ext (by simpa [hxc] using hx),
    Subtype.ext (by simpa [hyc] using hy), ?_, ?_, ?_⟩
  · intro h1
    apply hz
    have := congrArg Subtype.val h1
    rw [hcomm, hxc, hyc] at this
    simpa using this
  · apply Subtype.ext
    rw [hα, hxc]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hcomm, hxc, hyc]
    exact hhx
  · apply Subtype.ext
    rw [hα, hyc]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hcomm, hxc, hyc]
    exact hhy

theorem noncomm_conj_of_anisotropic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (hcard : Nat.card S = p ^ 3) (hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a)
    {x y : G} (hSxy : S = Subgroup.closure ({x, y} : Set G)) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : ⁅x, y⁆ ≠ 1) {h : G} (hh : h ∈ Subgroup.normalizer (S : Set G)) (a b c d e f : ℕ)
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ e)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ f)
    (hΔ : ∀ i j : ZMod p, (i ≠ 0 ∨ j ≠ 0) → i * (b * i + d * j) - j * (a * i + c * j) ≠ 0)
    {t : G} (ht : t ∈ S) (htn : ∃ b' ∈ S, t * b' ≠ b' * t) : ⁅t, h * t * h⁻¹⁆ ≠ 1 := by
  have hclass := commutator_le_center_of_card_pow_three hp S hcard hnc
  obtain ⟨xS, yS, α, hxc, hyc, hα, hgen, hxp, hyp, hz', hαx, hαy⟩ :=
    exists_lift S hSxy hx hy hz hh a b c d e f hhx hhy
  have hcomm : ∀ u v : S, (((⁅u, v⁆ : S)) : G) = ⁅(u : G), (v : G)⁆ := fun u v => by
    simp [commutatorElement_def]
  have hnc' : (⟨t, ht⟩ : S) ∉ Subgroup.center S := by
    obtain ⟨b', hb', hne⟩ := htn
    intro hc
    exact hne (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc ⟨b', hb'⟩).symm))
  have := commutator_ne_one_of_anisotropic hp hclass hgen hxp hyp hz' α a b c d e f hαx hαy hΔ hnc'
  intro h1
  apply this
  apply Subtype.ext
  rw [hcomm]
  simpa [hα] using h1

theorem conjWitness_of_data {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x y h : G}
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hh : h ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G))
    (a b c d e f : ℕ) (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ e)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ f)
    (hΔ : ∀ i j : ZMod p, (i ≠ 0 ∨ j ≠ 0) → i * (b * i + d * j) - j * (a * i + c * j) ≠ 0)
    (hdet : (a : ZMod p) * d - b * c ≠ 1) :
    (∃ z ∈ Subgroup.closure ({x, y} : Set G),
      (∀ u ∈ Subgroup.closure ({x, y} : Set G), z * u = u * z) ∧ h * z * h⁻¹ ≠ z) ∧
    ∀ t ∈ Subgroup.closure ({x, y} : Set G),
      (∃ u ∈ Subgroup.closure ({x, y} : Set G), t * u ≠ u * t) → ⁅t, h * t * h⁻¹⁆ ≠ 1 := by
  set S : Subgroup G := Subgroup.closure ({x, y} : Set G) with hS
  have hxS : x ∈ S := Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := Subgroup.subset_closure (by simp)
  have hnc : ∃ u ∈ S, ∃ v ∈ S, u * v ≠ v * u :=
    ⟨x, hxS, y, hyS, fun h' => hz (commutatorElement_eq_one_iff_mul_comm.2 h')⟩
  have hclass := commutator_le_center_of_card_pow_three hp S hcard hnc
  obtain ⟨xS, yS, α, hxc, hyc, hα, -, hxp, -, hz', hαx, hαy⟩ :=
    exists_lift S hS hx hy hz hh a b c d e f hhx hhy
  have hcomm : ∀ u v : S, (((⁅u, v⁆ : S)) : G) = ⁅(u : G), (v : G)⁆ := fun u v => by
    simp [commutatorElement_def]
  refine ⟨⟨⁅x, y⁆, ?_, ?_, ?_⟩, fun t ht htn => ?_⟩
  · have := (⁅xS, yS⁆ : S).2
    rwa [hcomm, hxc, hyc] at this
  · intro u hu
    have h1 := Subgroup.mem_center_iff.mp (commutatorElement_mem_center hclass xS yS) ⟨u, hu⟩
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcomm, hxc, hyc] at h2
    exact h2.symm
  · have h1 := automorphism_commutator_ne hp hclass hxp hz' α a b c d e f hαx hαy hdet
    intro h2
    apply h1
    apply Subtype.ext
    rw [hα, hcomm, hxc, hyc]
    exact h2
  · exact noncomm_conj_of_anisotropic hp S hcard hnc hS hx hy hz hh a b c d e f hhx hhy hΔ ht htn

theorem mem_normalizer_closure_pair {G : Type*} [Group G] [Finite G] {x y h : G}
    (hx : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G))
    (hy : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G)) :
    h ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  set S : Subgroup G := Subgroup.closure ({x, y} : Set G) with hS
  have hle : S.map (MulAut.conj h).toMonoidHom ≤ S := by
    rw [Subgroup.map_le_iff_le_comap, hS, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hx
    · exact hy
  have heq : S.map (MulAut.conj h).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact hle ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨s, hs, hsg⟩ := hg
    have : s = g := by
      simpa using hsg
    rwa [← this]

@[expose] def NormalizerWitness {G : Type*} [Group G] (T : Subgroup G) : Prop :=
  ∃ n₁ ∈ Subgroup.normalizer (T : Set G), ∃ n₂ ∈ Subgroup.normalizer (T : Set G),
    (∃ z ∈ T, (∀ b ∈ T, z * b = b * z) ∧ n₁ * z * n₁⁻¹ ≠ z) ∧
    ∀ t ∈ T, (∃ b ∈ T, t * b ≠ b * t) → ⁅t, n₂ * t * n₂⁻¹⁆ ≠ 1

theorem NormalizerWitness.of_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {T : Subgroup G} (h : NormalizerWitness (T.map e.toMonoidHom)) : NormalizerWitness T := by
  obtain ⟨n₁, hn₁, n₂, hn₂, ⟨z, hz, hzc, hzn⟩, h2⟩ := h
  have hmem : ∀ g : G, e g ∈ T.map e.toMonoidHom ↔ g ∈ T := fun g => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hN : ∀ n : H, n ∈ Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup H) : Set H) →
      e.symm n ∈ Subgroup.normalizer (T : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro g
    have h1 := hn (e g)
    have h4 : n * e g * n⁻¹ = e (e.symm n * g * (e.symm n)⁻¹) := by simp
    rw [← hmem, h1, h4, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨e.symm n₁, hN n₁ hn₁, e.symm n₂, hN n₂ hn₂, ?_, ?_⟩
  · refine ⟨e.symm z, ?_, ?_, ?_⟩
    · exact (hmem (e.symm z)).1 (by simpa using hz)
    · intro b hb
      have := hzc (e b) ((hmem b).2 hb)
      apply e.injective
      simpa using this
    · intro h1
      apply hzn
      have := congrArg e h1
      simpa using this
  · intro t ht htn
    obtain ⟨b, hb, hne⟩ := htn
    have hh := h2 (e t) ((hmem t).2 ht)
      ⟨e b, (hmem b).2 hb, fun h' => hne (e.injective (by simpa using h'))⟩
    intro h1
    apply hh
    have := congrArg e h1
    simpa using this

theorem NormalizerWitness.of_sylow_equiv {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] (e : G ≃* H) {S : Sylow p H} (hS : NormalizerWitness (S : Subgroup H))
    (T : Sylow p G) : NormalizerWitness (T : Subgroup G) := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  set U' := T.mapSurjective (f := (e : G →* H)) e.surjective with hU'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H U' S
  refine NormalizerWitness.of_map (e.trans (MulAut.conj g)) ?_
  have h2 : ((g • U' : Sylow p H) : Subgroup H) =
      (U' : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg, hU', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
  have h3 : (T : Subgroup G).map (e.trans (MulAut.conj g)).toMonoidHom = S := h2.symm
  rw [h3]
  exact hS

theorem normalizerWitness_subgroupOf {G : Type*} [Group G] {P Q : Subgroup G} (hQP : Q ≤ P)
    {h : G} (hhP : h ∈ P) (hh : h ∈ Subgroup.normalizer (Q : Set G))
    (h1 : ∃ z ∈ Q, (∀ u ∈ Q, z * u = u * z) ∧ h * z * h⁻¹ ≠ z)
    (h2 : ∀ t ∈ Q, (∃ u ∈ Q, t * u ≠ u * t) → ⁅t, h * t * h⁻¹⁆ ≠ 1) :
    NormalizerWitness (Q.subgroupOf P) := by
  have hn : (⟨h, hhP⟩ : P) ∈ Subgroup.normalizer ((Q.subgroupOf P : Subgroup P) : Set P) := by
    rw [Subgroup.mem_normalizer_iff] at hh ⊢
    intro g
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hh (g : G)
  refine ⟨⟨h, hhP⟩, hn, ⟨h, hhP⟩, hn, ?_, ?_⟩
  · obtain ⟨z, hz, hzc, hzn⟩ := h1
    refine ⟨⟨z, hQP hz⟩, hz, fun u hu => ?_, fun h' => hzn ?_⟩
    · exact Subtype.ext (hzc u hu)
    · simpa using congrArg Subtype.val h'
  · intro t ht htn
    obtain ⟨u, hu, hne⟩ := htn
    intro h'
    refine h2 t ht ⟨u, hu, fun h'' => hne (Subtype.ext h'')⟩ ?_
    simpa [commutatorElement_def] using congrArg Subtype.val h'

theorem orbitsCube_of_witness {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (T : Subgroup G)
    (hcard : Nat.card T = p ^ 3) (hnc : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a)
    (hw : NormalizerWitness T) :
    (∀ X : Subgroup G, X ≤ T →
      (∀ n ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ X, n * x * n⁻¹ ∈ X) → Nat.card X ≠ p ^ 2) ∧
    (∀ t ∈ T, t ≠ 1 → ∃ n ∈ Subgroup.normalizer (T : Set G), n * t * n⁻¹ ≠ t) := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ := card_center_of_card_pow_three hp T hcard hnc
  have hZfin : Finite (Subgroup.center T) :=
    Nat.finite_of_card_ne_zero (by rw [hZ]; exact hp.ne_zero)
  obtain ⟨n₁, hn₁, n₂, hn₂, ⟨z, hz, hzc, hzn⟩, h2⟩ := hw
  constructor
  · intro X hXT hXinv hXcard
    have hcomm : IsMulCommutative X := IsPGroup.isMulCommutative_of_card_eq_prime_sq hXcard
    have hex : ∃ t ∈ X, ∃ b ∈ T, t * b ≠ b * t := by
      by_contra hno
      push Not at hno
      have hle : X.subgroupOf T ≤ Subgroup.center T := by
        intro u hu
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hno u (Subgroup.mem_subgroupOf.mp hu) g g.2).symm
      have h1 : Nat.card (X.subgroupOf T) ≤ Nat.card (Subgroup.center T) :=
        Subgroup.card_le_of_le hle
      have h2' : Nat.card (X.subgroupOf T) = p ^ 2 := by
        rw [← hXcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXT).toEquiv
      rw [h2', hZ] at h1
      have := hp.two_le
      nlinarith [Nat.one_lt_pow (two_ne_zero) hp.one_lt]
    obtain ⟨t, htX, b, hb, hne⟩ := hex
    have ht' : n₂ * t * n₂⁻¹ ∈ X := hXinv n₂ hn₂ t htX
    have h3 : ⁅t, n₂ * t * n₂⁻¹⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hcomm.is_comm.comm (⟨t, htX⟩ : X) ⟨_, ht'⟩)
    exact h2 t (hXT htX) ⟨b, hb, hne⟩ h3
  · intro t ht ht1
    by_cases hct : ∃ b ∈ T, t * b ≠ b * t
    · refine ⟨n₂, hn₂, fun h1 => h2 t ht hct ?_⟩
      rw [h1]
      exact commutatorElement_self t
    · push Not at hct
      have ht' : (⟨t, ht⟩ : T) ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hct g g.2).symm
      have htp : (⟨t, ht⟩ : T) ^ p = 1 := by
        have h1 := pow_card_eq_one' (G := Subgroup.center T) (x := ⟨⟨t, ht⟩, ht'⟩)
        rw [hZ] at h1
        simpa using congrArg Subtype.val h1
      have ht1' : (⟨t, ht⟩ : T) ≠ 1 := fun h' => ht1 (by simpa using congrArg Subtype.val h')
      have hord : orderOf (⟨t, ht⟩ : T) = p := orderOf_eq_prime htp ht1'
      have hzp : Subgroup.zpowers (⟨t, ht⟩ : T) = Subgroup.center T := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ht')
        rw [Nat.card_zpowers, hord, hZ]
      have hzmem : (⟨z, hz⟩ : T) ∈ Subgroup.zpowers (⟨t, ht⟩ : T) := by
        rw [hzp, Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hzc g g.2).symm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
      have hkz : t ^ k = z := by simpa using congrArg Subtype.val hk
      refine ⟨n₁, hn₁, fun h1 => hzn ?_⟩
      rw [← hkz, ← conj_zpow, h1]

end CFSG.AGLEmbedding.KFactProofs.OrbitsCube
