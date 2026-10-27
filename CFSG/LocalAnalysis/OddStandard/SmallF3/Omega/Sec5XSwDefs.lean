module

public import CFSG.Quasithin.H13.GoldschmidtU43ModStage

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Quasithin.H13.U43

@[expose] abbrev SwC : Subgroup X₀ := Subgroup.centralizer ({xElt} : Set X₀)

@[expose] def SwCen (g : X₀) : Set X₀ :=
  {h | h ∈ SwC ∧ ∀ o ∈ SwC, Odd (orderOf o) → h * (o * g * o⁻¹) = o * g * o⁻¹ * h}

@[expose] def SwTables : Prop :=
  ∀ g₁ ∈ SwC, ∀ g₂ ∈ SwC, Odd (orderOf g₁) → Odd (orderOf g₂) → g₁ ≠ 1 → g₂ ≠ 1 →
    g₁ ∈ SwCen g₂ → g₂ ∈ SwCen g₁ →
    (∀ h ∈ SwCen g₁, h ∈ SwCen g₂ → h = 1 ∨ h = xElt) ∧
    ∃ c ∈ SwC,
      (∀ o ∈ SwC, Odd (orderOf o) → o ∈ SwCen g₂ → c⁻¹ * o * c ∈ SwCen g₁) ∧
      (∀ o ∈ SwC, Odd (orderOf o) → o ∈ SwCen g₁ → c * o * c⁻¹ ∈ SwCen g₂)

@[expose] def SwFinite : Prop :=
  ∀ N₁ N₂ : Subgroup X₀, xElt ∈ N₁ → xElt ∈ N₂ → N₁ ≤ SwC → N₂ ≤ SwC →
    N₁ ≤ Subgroup.closure {a | a ∈ N₁ ∧ Odd (orderOf a)} →
    N₂ ≤ Subgroup.closure {a | a ∈ N₂ ∧ Odd (orderOf a)} →
    (∀ u ∈ N₁, ∀ v ∈ N₂, u * v = v * u) →
    (∀ o ∈ SwC, Odd (orderOf o) → o ∈ N₁ ⊔ N₂) →
    ∃ c ∈ SwC, CFSG.conjugate N₁ c = N₂

@[expose] def SwOddCent : Prop :=
  ∀ y ∈ SwC, Odd (orderOf y) → y ≠ 1 → ∀ P : Subgroup X₀, IsPGroup 2 P → P ≤ SwC →
    (∀ p ∈ P, p * y = y * p) → Nat.card P < 16

@[expose] def SwEnum (L : Array (Array ℕ)) (S : Set X₀) : Prop :=
  ∃ f : ℕ → X₀, (∀ i < L.size, Rep 820 L[i]! (psi (f i))) ∧ Set.InjOn f (Set.Iio L.size) ∧
    f '' Set.Iio L.size = S

@[expose] def SwCover (L : Array (Array ℕ)) (S : Set X₀) : Prop :=
  (∀ i < L.size, ∃ s ∈ S, Rep 820 L[i]! (psi s)) ∧ (∀ s ∈ S, ∃ i < L.size, Rep 820 L[i]! (psi s))

theorem SwEnum.cover {L : Array (Array ℕ)} {S : Set X₀} (h : SwEnum L S) : SwCover L S := by
  obtain ⟨f, hrep, _hinj, himg⟩ := h
  refine ⟨?_, ?_⟩
  · intro i hi
    exact ⟨f i, by rw [← himg]; exact ⟨i, Set.mem_Iio.2 hi, rfl⟩, hrep i hi⟩
  · intro s hs
    rw [himg.symm] at hs
    obtain ⟨j, hj, hjs⟩ := hs
    exact ⟨j, Set.mem_Iio.1 hj, hjs ▸ hrep j (Set.mem_Iio.1 hj)⟩

theorem sw_odd_iff_pow9 (hC : Stage2HCard) {s : X₀} (hs : s ∈ SwC) :
    Odd (orderOf s) ↔ s ^ 9 = 1 := by
  have hcard : Nat.card ↥SwC = 1152 := hC
  have hdvd : orderOf s ∣ 2 ^ 7 * 9 := by
    have h := Subgroup.orderOf_dvd_natCard SwC hs
    rw [hcard] at h
    rwa [show (1152 : ℕ) = 2 ^ 7 * 9 by norm_num] at h
  constructor
  · intro hodd
    exact orderOf_dvd_iff_pow_eq_one.1
      ((hodd.coprime_two_right.pow_right 7).dvd_mul_left.1 hdvd)
  · intro h
    exact Odd.of_dvd_nat (by decide : Odd 9) (orderOf_dvd_of_pow_eq_one h)

end CFSG.OddStandard.SmallF3.Omega
