module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Branch55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Normal55

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure Lattice57 (G : Type) [Group G] (K Y R : Subgroup G) (z t : G) : Prop where
  z_ord : orderOf z = 2
  t_ord : orderOf t = 2
  zt_comm : z * t = t * z
  z_mem : z ∈ Y
  t_mem : t ∈ Y
  Y_le_R : Y ≤ R
  Y_le_K : Y ≤ K
  t_mem_K : t ∈ K
  K_z : ∀ k ∈ K, k * z = z * k
  K_t : ∀ k ∈ K, k * t = t * k
  K_Y : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y
  z_central : ∀ r ∈ R, r * z = z * r
  R_comm : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ zpowers z
  index : ∀ a ∈ R, ∀ b ∈ R, a ∉ Y → b ∉ Y → a⁻¹ * b ∈ Y
  swap : ∀ a ∈ R, a ∉ Y → a * t * a⁻¹ = t * z
  irred : ∀ W : Subgroup G, pair z t ≤ W → W ≤ Y → (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) →
    W = pair z t ∨ W = Y
  nonsplit : ∀ A₁ : Subgroup G, A₁ ≤ Y → (∀ k ∈ K, ∀ w ∈ A₁, k * w * k⁻¹ ∈ A₁) → z ∈ A₁ →
    (∀ y ∈ Y, y ∈ A₁ ∨ y * t ∈ A₁) → t ∈ A₁

section Main

variable [Finite G] {K Y R : Subgroup G} {z t : G}

theorem Lattice57.z_mul_self (h : Lattice57 G K Y R z t) : z * z = 1 := by
  rw [← pow_two, ← h.z_ord]; exact pow_orderOf_eq_one z

theorem Lattice57.t_mul_self (h : Lattice57 G K Y R z t) : t * t = 1 := by
  rw [← pow_two, ← h.t_ord]; exact pow_orderOf_eq_one t

theorem Lattice57.conj_zpowers_z (h : Lattice57 G K Y R z t) {k : G} (hk : k ∈ K) :
    ∀ w ∈ zpowers z, k * w * k⁻¹ ∈ zpowers z := by
  refine conj_mem_zpowers_of_conj_mem ?_
  rw [mul_inv_eq_iff_eq_mul.2 (h.K_z k hk)]
  exact mem_zpowers z

theorem Lattice57.conj_zpowers_t (h : Lattice57 G K Y R z t) {k : G} (hk : k ∈ K) :
    ∀ w ∈ zpowers t, k * w * k⁻¹ ∈ zpowers t := by
  refine conj_mem_zpowers_of_conj_mem ?_
  rw [mul_inv_eq_iff_eq_mul.2 (h.K_t k hk)]
  exact mem_zpowers t

theorem Lattice57.pair_le_Y (h : Lattice57 G K Y R z t) : pair z t ≤ Y :=
  sup_le (zpowers_le.2 h.z_mem) (zpowers_le.2 h.t_mem)

theorem Lattice57.mem_of_invariant (h : Lattice57 G K Y R z t) {A : Subgroup G} (hAR : A ≤ R)
    (hzA : z ∈ A) (hAK : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hne : ∃ a ∈ A, a ∉ zpowers z) : t ∈ A := by
  have hzz := h.z_mul_self
  have htt := h.t_mul_self
  by_cases hcase : ∃ s ∈ A ⊓ Y, s ∉ zpowers z
  · obtain ⟨s, hsAY, hsz⟩ := hcase
    have hsA : s ∈ A := (mem_inf.1 hsAY).1
    set S : Subgroup G := A ⊓ Y with hS
    have hSK : ∀ k ∈ K, ∀ w ∈ S, k * w * k⁻¹ ∈ S := fun k hk w hw =>
      mem_inf.2 ⟨hAK k hk w (mem_inf.1 hw).1, h.K_Y k hk w (mem_inf.1 hw).2⟩
    have hpairK : ∀ k ∈ K, ∀ w ∈ pair z t, k * w * k⁻¹ ∈ pair z t := fun k hk =>
      conj_mem_sup_of_invariant (h.conj_zpowers_z hk) (h.conj_zpowers_t hk)
    have hWK : ∀ k ∈ K, ∀ w ∈ S ⊔ pair z t, k * w * k⁻¹ ∈ S ⊔ pair z t := fun k hk =>
      conj_mem_sup_of_invariant (hSK k hk) (hpairK k hk)
    have hWY : S ⊔ pair z t ≤ Y := sup_le inf_le_right h.pair_le_Y
    rcases h.irred (S ⊔ pair z t) le_sup_right hWY hWK with hW | hW
    · have hsW : s ∈ S ⊔ pair z t := mem_sup_left hsAY
      rw [hW] at hsW
      rcases mem_pair_cases h.z_ord h.t_ord h.zt_comm hsW with h1 | h1 | h1 | h1
      · exact absurd (h1 ▸ one_mem _) hsz
      · exact absurd (h1 ▸ mem_zpowers z) hsz
      · exact h1 ▸ hsA
      · have : t = z * s := by rw [h1, ← mul_assoc, hzz, one_mul]
        rw [this]
        exact mul_mem hzA hsA
    · have htS : t ∈ normalizer (S : Set G) := by
        rw [mem_normalizer_iff]
        intro a
        refine ⟨fun ha => hSK t h.t_mem_K a ha, fun ha => ?_⟩
        have := hSK t⁻¹ (inv_mem h.t_mem_K) _ ha
        have e : t⁻¹ * (t * a * t⁻¹) * t⁻¹⁻¹ = a := by group
        rwa [e] at this
      have hzS : z ∈ S := mem_inf.2 ⟨hzA, h.z_mem⟩
      have ht2 : t ^ 2 ∈ S := by rw [pow_two, htt]; exact one_mem _
      have hcos : ∀ y ∈ Y, y ∈ S ∨ y * t ∈ S := by
        intro y hy
        have hyW : y ∈ S ⊔ zpowers t := by
          have hle : Y ≤ S ⊔ zpowers t := by
            rw [← hW]
            exact sup_le le_sup_left (sup_le (zpowers_le.2 (mem_sup_left hzS))
              (zpowers_le.2 (mem_sup_right (mem_zpowers t))))
          exact hle hy
        rcases mem_or_exists_mul_of_mem_sup_zpowers htS ht2 hyW with hyS | ⟨r, hr, rfl⟩
        · exact Or.inl hyS
        · right
          rwa [mul_assoc, htt, mul_one]
      exact (mem_inf.1 (h.nonsplit S inf_le_right hSK hzS hcos)).1
  · exfalso
    push Not at hcase
    obtain ⟨a, haA, haz⟩ := hne
    have haY : a ∉ Y := fun hY => haz (hcase a (mem_inf.2 ⟨haA, hY⟩))
    have haR : a ∈ R := hAR haA
    have hconj : ∀ k ∈ K, ∃ w ∈ zpowers z, k⁻¹ * a * k = a * w := by
      intro k hk
      have ha' : k⁻¹ * a * k ∈ A := by
        have := hAK k⁻¹ (inv_mem hk) a haA
        rwa [inv_inv] at this
      have ha'Y : k⁻¹ * a * k ∉ Y := by
        intro hY
        apply haY
        have := h.K_Y k hk _ hY
        have e : k * (k⁻¹ * a * k) * k⁻¹ = a := by group
        rwa [e] at this
      have hw := hcase _ (mem_inf.2 ⟨mul_mem (inv_mem haA) ha',
        h.index a haR _ (hAR ha') haY ha'Y⟩)
      exact ⟨a⁻¹ * (k⁻¹ * a * k), hw, by group⟩
    have hinv : ∀ w ∈ zpowers z, ∀ y ∈ Y, y * w = w * y := by
      intro w hw y hy
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
      exact ((Commute.zpow_right (show Commute y z from h.K_z y (h.Y_le_K hy)) n).eq)
    set A₁ : Subgroup G := Y ⊓ centralizer ({a} : Set G) with hA₁
    have hA₁K : ∀ k ∈ K, ∀ w ∈ A₁, k * w * k⁻¹ ∈ A₁ := by
      intro k hk y hy
      obtain ⟨hyY, hyc⟩ := mem_inf.1 hy
      have hya : a * y = y * a := (mem_centralizer_singleton_iff.1 hyc).symm
      refine mem_inf.2 ⟨h.K_Y k hk y hyY, mem_centralizer_singleton_iff.2 (Eq.symm ?_)⟩
      obtain ⟨w, hw, hkw⟩ := hconj k hk
      have hya' : y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y := by
        rw [hkw]
        calc y * (a * w) = (y * a) * w := by rw [mul_assoc]
          _ = (a * y) * w := by rw [hya]
          _ = a * (y * w) := by rw [mul_assoc]
          _ = a * (w * y) := by rw [hinv w hw y hyY]
          _ = (a * w) * y := by rw [mul_assoc]
      have e1 : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
      calc a * (k * y * k⁻¹) = k * ((k⁻¹ * a * k) * y) * k⁻¹ := by group
        _ = k * (y * (k⁻¹ * a * k)) * k⁻¹ := by rw [hya']
        _ = (k * y * k⁻¹) * a := by group
    have hzA₁ : z ∈ A₁ :=
      mem_inf.2 ⟨h.z_mem, mem_centralizer_singleton_iff.2 (h.z_central a haR).symm⟩
    have hcos : ∀ y ∈ Y, y ∈ A₁ ∨ y * t ∈ A₁ := by
      intro y hy
      have hyR : y ∈ R := h.Y_le_R hy
      have hyz : y * z = z * y := h.K_z y (h.Y_le_K hy)
      have hyt : y * t = t * y := h.K_t y (h.Y_le_K hy)
      have hcz := h.R_comm a haR y hyR
      rcases eq_one_or_eq_of_mem_zpowers_two h.z_ord hcz with hc | hc
      · left
        refine mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩
        exact (commutatorElement_eq_one_iff_mul_comm.1 hc).symm
      · right
        refine mem_inf.2 ⟨mul_mem hy h.t_mem, mem_centralizer_singleton_iff.2 (Eq.symm ?_)⟩
        have hay : a * y * a⁻¹ = z * y := by
          have : a * y * a⁻¹ * y⁻¹ = z := hc
          calc a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
            _ = z * y := by rw [this]
        have hat := h.swap a haR haY
        have hconj' : a * (y * t) * a⁻¹ = y * t := by
          calc a * (y * t) * a⁻¹ = (a * y * a⁻¹) * (a * t * a⁻¹) := by group
            _ = (z * y) * (t * z) := by rw [hay, hat]
            _ = (y * z) * (t * z) := by rw [← hyz]
            _ = y * (z * t) * z := by group
            _ = y * (t * z) * z := by rw [h.zt_comm]
            _ = y * t * (z * z) := by group
            _ = y * t := by rw [hzz, mul_one]
        calc a * (y * t) = (a * (y * t) * a⁻¹) * a := by group
          _ = (y * t) * a := by rw [hconj']
    have htA₁ := h.nonsplit A₁ inf_le_left hA₁K hzA₁ hcos
    have hat : a * t = t * a := (mem_centralizer_singleton_iff.1 (mem_inf.1 htA₁).2).symm
    have hsw := h.swap a haR haY
    have h1 : t = t * z := by
      calc t = (t * a) * a⁻¹ := by group
        _ = (a * t) * a⁻¹ := by rw [hat]
        _ = t * z := hsw
    have h2 : z = 1 := mul_left_cancel (a := t) (by rw [mul_one]; exact h1.symm)
    have := h.z_ord
    rw [h2, orderOf_one] at this
    omega

end Main

end CFSG.EvenSporadicStandard.TwoB
