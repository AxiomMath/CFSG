module

public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.Goldschmidt.G37

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_centralizer' (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  intro x hx
  have hx' : ∀ y, y ∈ L ↔ x * y * x⁻¹ ∈ L := Subgroup.mem_normalizer_iff.mp hx
  have hx'' : ∀ y, y ∈ L → x⁻¹ * y * x ∈ L := by
    intro y hy
    rw [hx']
    simpa [mul_assoc] using hy
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have h1 := hc (x⁻¹ * y * x) (hx'' y hy)
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * y := by group
  · intro hc y hy
    have h1 := hc (x * y * x⁻¹) ((hx' y).mp hy)
    have h2 : (x * y * x⁻¹) * (x * c * x⁻¹) = x * (y * c) * x⁻¹ := by group
    have h3 : (x * c * x⁻¹) * (x * y * x⁻¹) = x * (c * y) * x⁻¹ := by group
    rw [h2, h3] at h1
    have h4 := congrArg (fun z => x⁻¹ * z * x) h1
    simpa [mul_assoc] using h4

theorem le_normalizer_centralizer (L : Subgroup G) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer' L)

theorem normalizer_le_normalizer_centralizer {L Z : Subgroup G}
    (hZL : Z ≤ Subgroup.normalizer (L : Set G)) :
    Z ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
  hZL.trans (normalizer_le_normalizer_centralizer' L)

@[expose] def proj (L Z : Subgroup G) : Subgroup G :=
  (Z ⊔ Subgroup.centralizer (L : Set G)) ⊓ L

theorem proj_le (L Z : Subgroup G) : proj L Z ≤ L := inf_le_right

theorem proj_mono {L Z₀ Z : Subgroup G} (h : Z₀ ≤ Z) : proj L Z₀ ≤ proj L Z :=
  inf_le_inf_right L (sup_le_sup_right h _)

theorem le_proj_sup_centralizer {L Z : Subgroup G}
    (hZ : Z ≤ L ⊔ Subgroup.centralizer (L : Set G)) :
    Z ≤ proj L Z ⊔ Subgroup.centralizer (L : Set G) := by
  intro z hz
  obtain ⟨ℓ, hℓ, c, hc, hℓc⟩ := mem_sup_of_le_normalizer (le_normalizer_centralizer L) (hZ hz)
  have hℓW : ℓ ∈ proj L Z := by
    refine Subgroup.mem_inf.mpr ⟨?_, hℓ⟩
    have : ℓ = z * c⁻¹ := by rw [← hℓc]; group
    rw [this]
    exact Subgroup.mul_mem _ (le_sup_left (a := Z) hz)
      (le_sup_right (a := Z) (Subgroup.inv_mem _ hc))
  rw [← hℓc]
  exact Subgroup.mul_mem _ (le_sup_left (a := proj L Z) hℓW) (le_sup_right (a := proj L Z) hc)

theorem mem_sup_centralizer {L Z : Subgroup G} (hZL : Z ≤ Subgroup.normalizer (L : Set G))
    {w : G} (hw : w ∈ Z ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ z ∈ Z, ∃ c ∈ Subgroup.centralizer (L : Set G), z * c = w :=
  mem_sup_of_le_normalizer (normalizer_le_normalizer_centralizer hZL) hw

theorem odd_orderOf_of_mem_proj [Finite G] {L Z : Subgroup G}
    (hZL : Z ≤ Subgroup.normalizer (L : Set G))
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hZ : Odd (Nat.card Z)) {w : G}
    (hw : w ∈ proj L Z) : Odd (orderOf w) := by
  obtain ⟨hwZC, hwL⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨z, hz, c, hc, rfl⟩ := mem_sup_centralizer hZL hwZC
  have hcw : c * (z * c) = (z * c) * c := (Subgroup.mem_centralizer_iff.mp hc _ hwL).symm
  have hcz : Commute z c := by
    have : c * z = z * c := by
      have h1 := hcw
      rw [← mul_assoc] at h1
      exact mul_right_cancel h1
    exact this.symm
  have hzodd : Odd (orderOf z) := by
    have h1 : orderOf (⟨z, hz⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hZ.of_dvd_nat h1
  set n := orderOf z with hn
  have hpow : (z * c) ^ n = c ^ n := by
    rw [hcz.mul_pow, pow_orderOf_eq_one, one_mul]
  have hcnL : c ^ n ∈ L := hpow ▸ L.pow_mem hwL n
  have hcnC : c ^ n ∈ Subgroup.centralizer (L : Set G) := Subgroup.pow_mem _ hc n
  have h1 : c ^ n = 1 := by
    have : c ^ n ∈ L ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hcnL, hcnC⟩
    rw [hLC] at this
    exact this
  have h2 : orderOf (z * c) ∣ n := orderOf_dvd_of_pow_eq_one (by rw [hpow, h1])
  exact hzodd.of_dvd_nat h2

theorem odd_card_of_forall_odd_orderOf [Finite G] {W : Subgroup G}
    (h : ∀ w ∈ W, Odd (orderOf w)) : Odd (Nat.card W) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (even_iff_two_dvd.mp hne)
  have h1 := h (x : G) x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (Nat.not_odd_iff_even.mpr even_two) h1

theorem odd_card_proj [Finite G] {L Z : Subgroup G} (hZL : Z ≤ Subgroup.normalizer (L : Set G))
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hZ : Odd (Nat.card Z)) :
    Odd (Nat.card (proj L Z)) :=
  odd_card_of_forall_odd_orderOf fun _ hw => odd_orderOf_of_mem_proj hZL hLC hZ hw

theorem proj_le_centralizer {L Z B : Subgroup G} (hBL : B ≤ L)
    (hZB : Z ≤ Subgroup.centralizer (B : Set G)) :
    proj L Z ≤ Subgroup.centralizer (B : Set G) := by
  refine inf_le_left.trans (sup_le hZB ?_)
  exact Subgroup.centralizer_le hBL

theorem proj_le_normalizer {L Z : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    g ∈ Subgroup.normalizer (proj L Z : Set G) := by
  apply Subgroup.inf_normalizer_le_normalizer_inf
  refine Subgroup.mem_inf.mpr ⟨?_, hgL⟩
  exact CFSG.Walter.mem_normalizer_sup hgZ (normalizer_le_normalizer_centralizer' L hgL)

theorem le_centralizer_of_proj_eq_bot {L Z : Subgroup G}
    (hZ : Z ≤ L ⊔ Subgroup.centralizer (L : Set G)) (h : proj L Z = ⊥) :
    Z ≤ Subgroup.centralizer (L : Set G) := by
  have h1 := le_proj_sup_centralizer hZ
  rwa [h, bot_sup_eq] at h1

theorem proj_eq_bot_of_le_centralizer {L Z : Subgroup G}
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (h : Z ≤ Subgroup.centralizer (L : Set G)) : proj L Z = ⊥ := by
  rw [proj, sup_eq_right.mpr h, inf_comm, hLC]

theorem exists_zpowers_of_isCyclic_proj {L Z : Subgroup G}
    (hZL : Z ≤ Subgroup.normalizer (L : Set G)) (hZ : Z ≤ L ⊔ Subgroup.centralizer (L : Set G))
    (hcyc : IsCyclic (proj L Z)) :
    ∃ z ∈ Z, Z ≤ Subgroup.zpowers z ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨⟨w, hw⟩, hgen⟩ := hcyc.exists_generator
  obtain ⟨hwZC, hwL⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨z, hz, c, hc, hzc⟩ := mem_sup_centralizer hZL hwZC
  refine ⟨z, hz, fun y hy => ?_⟩
  have hy1 := le_proj_sup_centralizer hZ hy
  obtain ⟨ℓ, hℓ, c', hc', hℓc'⟩ :=
    mem_sup_of_le_normalizer (proj_le L Z |>.trans (le_normalizer_centralizer L)) hy1
  obtain ⟨k, hk⟩ := hgen ⟨ℓ, hℓ⟩
  have hk' : w ^ k = ℓ := congrArg Subtype.val hk
  have hcz : Commute z c := by
    have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hwL).symm
    rw [← hzc] at hcw
    have : c * z = z * c := by
      have h1 := hcw
      rw [← mul_assoc] at h1
      exact mul_right_cancel h1
    exact this.symm
  have hwk : w ^ k = z ^ k * c ^ k := by rw [← hzc, hcz.mul_zpow]
  rw [← hℓc', ← hk', hwk, mul_assoc]
  exact Subgroup.mul_mem _ (le_sup_left (a := Subgroup.zpowers z)
      (Subgroup.zpow_mem_zpowers z k))
    (le_sup_right (a := Subgroup.zpowers z) (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hc k) hc'))

theorem commutator_mem_centralizer_of_inner {L : Subgroup G} {g h ℓ m : G}
    (hg : ∀ x ∈ L, g * x * g⁻¹ = ℓ * x * ℓ⁻¹) (hh : ∀ x ∈ L, h * x * h⁻¹ = m * x * m⁻¹)
    (hℓL : ℓ ∈ L) (hmL : m ∈ L) (hℓm : ℓ * m = m * ℓ) :
    ⁅g, h⁆ ∈ Subgroup.centralizer (L : Set G) := by
  have hg' : ∀ x ∈ L, g⁻¹ * x * g = ℓ⁻¹ * x * ℓ := by
    intro x hx
    have hy : ℓ⁻¹ * x * ℓ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hℓL) hx) hℓL
    have h1 := hg _ hy
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have h3 : ℓ * (ℓ⁻¹ * x * ℓ) * ℓ⁻¹ = x := by group
    have h4 : g * (g⁻¹ * x * g) * g⁻¹ = g * (ℓ⁻¹ * x * ℓ) * g⁻¹ := by rw [h2, h1, h3]
    have h5 := congrArg (fun y => g⁻¹ * y * g) h4
    simpa [mul_assoc] using h5
  have hh' : ∀ x ∈ L, h⁻¹ * x * h = m⁻¹ * x * m := by
    intro x hx
    have hy : m⁻¹ * x * m ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hmL) hx) hmL
    have h1 := hh _ hy
    have h2 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    have h3 : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    have h4 : h * (h⁻¹ * x * h) * h⁻¹ = h * (m⁻¹ * x * m) * h⁻¹ := by rw [h2, h1, h3]
    have h5 := congrArg (fun y => h⁻¹ * y * h) h4
    simpa [mul_assoc] using h5
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hm1 : m⁻¹ * x * m ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hmL) hx) hmL
  have hm2 : ℓ⁻¹ * (m⁻¹ * x * m) * ℓ ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem hℓL) hm1) hℓL
  have key : ⁅g, h⁆ * x * ⁅g, h⁆⁻¹ = x := by
    rw [commutatorElement_def]
    calc g * h * g⁻¹ * h⁻¹ * x * (g * h * g⁻¹ * h⁻¹)⁻¹
        = g * (h * (g⁻¹ * (h⁻¹ * x * h) * g) * h⁻¹) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * (m⁻¹ * x * m) * g) * h⁻¹) * g⁻¹ := by rw [hh' x hx]
      _ = g * (h * (ℓ⁻¹ * (m⁻¹ * x * m) * ℓ) * h⁻¹) * g⁻¹ := by rw [hg' _ hm1]
      _ = g * (m * (ℓ⁻¹ * (m⁻¹ * x * m) * ℓ) * m⁻¹) * g⁻¹ := by rw [hh _ hm2]
      _ = ℓ * (m * (ℓ⁻¹ * (m⁻¹ * x * m) * ℓ) * m⁻¹) * ℓ⁻¹ := by
          rw [hg _ (L.mul_mem (L.mul_mem hmL hm2) (L.inv_mem hmL))]
      _ = (ℓ * m) * ℓ⁻¹ * m⁻¹ * x * (m * ℓ) * m⁻¹ * ℓ⁻¹ := by group
      _ = (m * ℓ) * ℓ⁻¹ * m⁻¹ * x * (ℓ * m) * m⁻¹ * ℓ⁻¹ := by rw [hℓm]
      _ = x := by group
  calc x * ⁅g, h⁆ = (⁅g, h⁆ * x * ⁅g, h⁆⁻¹) * ⁅g, h⁆ := by rw [key]
    _ = ⁅g, h⁆ * x := by group

end CFSG.Goldschmidt.G37
