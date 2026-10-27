module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma13dNC

variable {A : Type*} [Group A]

theorem mem_of_pow_mem_of_coprime (M : Subgroup A) {g : A} {u v : ℕ} (huv : Nat.Coprime u v)
    (hu : g ^ u ∈ M) (hv : g ^ v ∈ M) : g ∈ M := by
  have hab := Nat.gcd_eq_gcd_ab u v
  rw [huv.gcd_eq_one] at hab
  have h : (g ^ u) ^ Nat.gcdA u v * (g ^ v) ^ Nat.gcdB u v = g := by
    rw [← zpow_natCast g u, ← zpow_natCast g v, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (u : ℤ) * Nat.gcdA u v + (v : ℤ) * Nat.gcdB u v = 1 := by simpa using hab.symm
    rw [this, zpow_one]
  rw [← h]
  exact M.mul_mem (M.zpow_mem hu _) (M.zpow_mem hv _)

theorem mem_sup_zpowers {X : Subgroup A} {c : A}
    (hc : ∀ i : ℤ, ∀ x ∈ X, c ^ i * x * (c ^ i)⁻¹ ∈ X) {y : A}
    (hy : y ∈ X ⊔ Subgroup.zpowers c) : ∃ x ∈ X, ∃ i : ℤ, y = x * c ^ i := by
  let S : Subgroup A :=
    { carrier := {y | ∃ x ∈ X, ∃ i : ℤ, y = x * c ^ i}
      one_mem' := ⟨1, X.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, i, rfl⟩ ⟨x', hx', i', rfl⟩
        refine ⟨x * (c ^ i * x' * (c ^ i)⁻¹), X.mul_mem hx (hc i x' hx'), i + i', ?_⟩
        rw [zpow_add]
        group
      inv_mem' := by
        rintro _ ⟨x, hx, i, rfl⟩
        refine ⟨c ^ (-i) * x⁻¹ * (c ^ (-i))⁻¹, hc (-i) _ (X.inv_mem hx), -i, ?_⟩
        group }
  have hle : X ⊔ Subgroup.zpowers c ≤ S := by
    refine sup_le (fun x hx => ⟨x, hx, 0, by simp⟩) ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨1, X.one_mem, i, by simp⟩
  exact hle hy

theorem pow_mul_zpow_mem {C D : Subgroup A} (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) {c₀ : A}
    (hc₀ : c₀ ∈ C) {d : A} (hd : d ∈ D) (j : ℤ) (m : ℕ) :
    ∃ d' ∈ D, (d * c₀ ^ j) ^ m = d' * c₀ ^ (j * m) := by
  induction m with
  | zero => exact ⟨1, D.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨d', hd', h⟩ := ih
    refine ⟨d' * (c₀ ^ (j * m) * d * (c₀ ^ (j * m))⁻¹),
      D.mul_mem hd' (hCD _ (C.zpow_mem hc₀ _) d hd), ?_⟩
    rw [pow_succ, h]
    push_cast
    rw [mul_add, mul_one, zpow_add]
    group

theorem pow_mul_mem {Y : Subgroup A} {g y : A} (hg : ∀ z ∈ Y, g⁻¹ * z * g ∈ Y) (hy : y ∈ Y)
    (m : ℕ) : ∃ y' ∈ Y, (g * y) ^ m = g ^ m * y' := by
  induction m with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨y', hy', h⟩ := ih
    refine ⟨g⁻¹ * y' * g * y, Y.mul_mem (hg y' hy') hy, ?_⟩
    rw [pow_succ, h]
    group

section Quotient

variable [Finite A]

theorem exists_card_eq_of_forall_exists_pow_mem {H M : Subgroup A} (hMH : M ≤ H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (h2 : ∀ h ∈ H, ∃ t : ℕ, h ^ 2 ^ t ∈ M) :
    ∃ k : ℕ, Nat.card M * 2 ^ k = Nat.card H := by
  have : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hMH).mpr fun h k hh hk => hnorm k hk h hh
  have hp : IsPGroup 2 (↥H ⧸ M.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨t, ht⟩ := h2 h h.2
      refine ⟨t, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ht
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf H), hk, mul_comm]
  congr 1
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv).symm

theorem pow_mem_of_card_eq {H M : Subgroup A} (hMH : M ≤ H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) {s : ℕ} (hcard : Nat.card H = 2 ^ s * Nat.card M)
    {g : A} (hgH : g ∈ H) : g ^ 2 ^ s ∈ M := by
  have : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hMH).mpr fun h k hh hk => hnorm k hk h hh
  have hidx : (M.subgroupOf H).index = 2 ^ s := by
    have h1 := Subgroup.card_mul_index (M.subgroupOf H)
    have h2 : Nat.card (M.subgroupOf H) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv
    rw [h2, hcard, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have := Subgroup.pow_index_mem (M.subgroupOf H) ⟨g, hgH⟩
  rw [hidx] at this
  exact this

theorem mem_of_odd_orderOf {H M : Subgroup A} (hMH : M ≤ H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) {s : ℕ} (hcard : Nat.card H = 2 ^ s * Nat.card M)
    {g : A} (hgH : g ∈ H) (hodd : Odd (orderOf g)) : g ∈ M :=
  mem_of_pow_mem_of_coprime M (Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hodd))
    (pow_mem_of_card_eq hMH hnorm hcard hgH) (by rw [pow_orderOf_eq_one]; exact M.one_mem)

end Quotient

theorem quotient_data {X Y : Subgroup A} {c₁ : A} (hXY : X ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hc₁ : c₁ ∈ Y) (hodd : Odd (orderOf c₁))
    (hdec : ∀ y ∈ Y, ∃ x ∈ X, ∃ i : ℤ, y = x * c₁ ^ i) (hXodd : Odd (Nat.card X)) :
    ∃ (_ : (X.subgroupOf Y).Normal), IsCyclic (↥Y ⧸ X.subgroupOf Y) ∧ Odd (Nat.card Y) := by
  have hN : (X.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hXY).mpr fun h k hh hk => hnorm k hk h hh
  refine ⟨hN, ?_⟩
  let g : ↥Y ⧸ X.subgroupOf Y := QuotientGroup.mk ⟨c₁, hc₁⟩
  have hg : ∀ z : ↥Y ⧸ X.subgroupOf Y, z ∈ Subgroup.zpowers g := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨x, hx, i, hxi⟩ := hdec y y.2
      refine ⟨i, ?_⟩
      have hy : y = ⟨x, hXY hx⟩ * ⟨c₁, hc₁⟩ ^ i := Subtype.ext (by simp [hxi])
      have hx1 : (QuotientGroup.mk ⟨x, hXY hx⟩ : ↥Y ⧸ X.subgroupOf Y) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hx
      show g ^ i = QuotientGroup.mk y
      rw [hy, QuotientGroup.mk_mul, hx1, one_mul, QuotientGroup.mk_zpow]
  refine ⟨⟨g, hg⟩, ?_⟩
  have hord : orderOf g = Nat.card (↥Y ⧸ X.subgroupOf Y) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : orderOf g ∣ orderOf c₁ := by
    have := orderOf_map_dvd (QuotientGroup.mk' (X.subgroupOf Y)) (⟨c₁, hc₁⟩ : ↥Y)
    rwa [Subgroup.orderOf_mk] at this
  have hodd' : Odd (Nat.card (↥Y ⧸ X.subgroupOf Y)) := hord ▸ Odd.of_dvd_nat hodd hdvd
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (X.subgroupOf Y)]
  refine hodd'.mul ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv]
  exact hXodd

end Lemma13dNC

open Lemma13dNC

theorem exists_normal_two_complement {A : Type*} [Group A] [Finite A] (C D X : Subgroup A)
    (hDC : D ≤ C) (hXD : X ≤ D)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hCX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hXodd : Odd (Nat.card X)) (hD2 : ∃ s : ℕ, Nat.card D = 2 ^ s * Nat.card X)
    (hcyc : ∃ c₀ ∈ C, ∀ c ∈ C, ∃ d ∈ D, ∃ j : ℤ, c = d * c₀ ^ j)
    (hK : ∀ c ∈ C, Odd (orderOf c) → ∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ X) :
    ∃ Y : Subgroup A, Y ≤ C ∧ X ≤ Y ∧ (∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) ∧ Odd (Nat.card Y) ∧
      (∃ k : ℕ, Nat.card Y * 2 ^ k = Nat.card C) ∧ Y ⊓ D = X ∧
      (∀ c ∈ C, Odd (orderOf c) → c ∈ Y) ∧
      (∃ c₁ ∈ C, Odd (orderOf c₁) ∧ Y = X ⊔ Subgroup.zpowers c₁) ∧
      ∃ (_ : (X.subgroupOf Y).Normal), IsCyclic (↥Y ⧸ X.subgroupOf Y) := by
  obtain ⟨c₀, hc₀C, hcyc'⟩ := hcyc
  obtain ⟨s, hs⟩ := hD2
  have hXC : X ≤ C := hXD.trans hDC
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c₀).ne'
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : A, c₁ = c₀ ^ 2 ^ a := ⟨_, rfl⟩
  have hc₁C : c₁ ∈ C := hc₁def ▸ C.pow_mem hc₀C _
  have hc₁dvd : orderOf c₁ ∣ m := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hc₁def, ← pow_mul, ← hord, pow_orderOf_eq_one]
  have hc₁odd : Odd (orderOf c₁) := Odd.of_dvd_nat hm hc₁dvd
  have hX1 : ∀ i : ℤ, ∀ x ∈ X, c₁ ^ i * x * (c₁ ^ i)⁻¹ ∈ X := fun i x hx =>
    hCX _ (C.zpow_mem hc₁C i) x hx
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup A, Y = X ⊔ Subgroup.zpowers c₁ := ⟨_, rfl⟩
  have hdec : ∀ y ∈ Y, ∃ x ∈ X, ∃ i : ℤ, y = x * c₁ ^ i := fun y hy =>
    mem_sup_zpowers hX1 (hYdef ▸ hy)
  have hc₁Y : c₁ ∈ Y := hYdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)
  have hXY : X ≤ Y := hYdef ▸ le_sup_left
  have hYC : Y ≤ C := hYdef ▸ sup_le hXC (Subgroup.zpowers_le.mpr hc₁C)
  have hconj : ∀ c ∈ C, c * c₁ * c⁻¹ ∈ Y := by
    intro c hc
    obtain ⟨d, hd, j, rfl⟩ := hcyc' c hc
    have hcomm : c₀ ^ j * c₁ * (c₀ ^ j)⁻¹ = c₁ := by
      rw [mul_inv_eq_iff_eq_mul, hc₁def]
      exact (((Commute.refl c₀).zpow_left j).pow_right (2 ^ a)).eq
    have h1 : d * c₀ ^ j * c₁ * (d * c₀ ^ j)⁻¹ = d * c₁ * d⁻¹ :=
      calc d * c₀ ^ j * c₁ * (d * c₀ ^ j)⁻¹ = d * (c₀ ^ j * c₁ * (c₀ ^ j)⁻¹) * d⁻¹ := by group
        _ = d * c₁ * d⁻¹ := by rw [hcomm]
    have hx : d * c₁ * d⁻¹ * c₁⁻¹ ∈ X := by
      have := X.inv_mem (hK c₁ hc₁C hc₁odd d hd)
      simpa [mul_inv_rev, mul_assoc] using this
    have h2 : d * c₁ * d⁻¹ = (d * c₁ * d⁻¹ * c₁⁻¹) * c₁ := by group
    rw [h1, h2]
    exact Y.mul_mem (hXY hx) hc₁Y
  have hYnorm : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    obtain ⟨x, hx, i, rfl⟩ := hdec y hy
    have : c * (x * c₁ ^ i) * c⁻¹ = (c * x * c⁻¹) * (c * c₁ * c⁻¹) ^ i := by
      rw [conj_zpow]
      group
    rw [this]
    exact Y.mul_mem (hXY (hCX c hc x hx)) (Y.zpow_mem (hconj c hc) i)
  have hDX : ∀ h ∈ D, ∀ m ∈ X, h * m * h⁻¹ ∈ X := fun h hh m hm => hCX h (hDC hh) m hm
  have hDpow : ∀ d ∈ D, d ^ 2 ^ s ∈ X := fun d hd => pow_mem_of_card_eq hXD hDX hs hd
  have key : ∀ c ∈ C, ∃ t : ℕ, c ^ 2 ^ t ∈ Y := by
    intro c hc
    obtain ⟨d, hd, j, rfl⟩ := hcyc' c hc
    obtain ⟨d', hd', h⟩ := pow_mul_zpow_mem hCD hc₀C hd j (2 ^ a)
    have hj : c₀ ^ (j * ((2 ^ a : ℕ) : ℤ)) = c₁ ^ j := by
      rw [hc₁def, mul_comm, zpow_mul, zpow_natCast]
    rw [hj] at h
    obtain ⟨y', hy', h'⟩ := pow_mul_mem (Y := Y) (g := d') (y := c₁ ^ j)
      (fun z hz => by simpa using hYnorm d'⁻¹ (C.inv_mem (hDC hd')) z hz)
      (Y.zpow_mem hc₁Y j) (2 ^ s)
    refine ⟨a + s, ?_⟩
    rw [pow_add, pow_mul, h, h']
    exact Y.mul_mem (hXY (hDpow d' hd')) hy'
  obtain ⟨k, hk⟩ := exists_card_eq_of_forall_exists_pow_mem hYC hYnorm key
  have hodd_in : ∀ c ∈ C, Odd (orderOf c) → c ∈ Y := fun c hc ho =>
    mem_of_odd_orderOf hYC hYnorm (s := k) (by rw [← hk, mul_comm]) hc ho
  have hYD : Y ⊓ D = X := by
    refine le_antisymm ?_ (le_inf hXY hXD)
    rintro y ⟨hy, hyD⟩
    obtain ⟨x, hx, i, rfl⟩ := hdec y hy
    have hg : c₁ ^ i ∈ D := by
      have : c₁ ^ i = x⁻¹ * (x * c₁ ^ i) := by group
      rw [this]
      exact D.mul_mem (D.inv_mem (hXD hx)) hyD
    have hgodd : Odd (orderOf (c₁ ^ i)) :=
      Odd.of_dvd_nat hc₁odd (orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers c₁ i))
    exact X.mul_mem hx (mem_of_odd_orderOf hXD hDX hs hg hgodd)
  obtain ⟨hN, hcycY, hoddY⟩ :=
    quotient_data hXY (fun y hy x hx => hCX y (hYC hy) x hx) hc₁Y hc₁odd hdec hXodd
  exact ⟨Y, hYC, hXY, hYnorm, hoddY, ⟨k, hk⟩, hYD, hodd_in, ⟨c₁, hc₁C, hc₁odd, hYdef⟩, hN, hcycY⟩

end CFSG.GH74.GLS.IVK.Proofs2
