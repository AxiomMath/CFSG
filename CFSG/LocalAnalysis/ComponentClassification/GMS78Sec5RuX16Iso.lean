module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModelFast
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSwap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModelSec

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.GMS78RuS RuSModel

variable {Γ : Type} [Group Γ]

structure IsCodeModel (n : ℕ) (m : ℕ → ℕ → ℕ) (φ : ℕ → Γ) (z : Γ) : Prop where
  mul : ∀ p q, φ (m p q) = φ p * φ q
  lt : ∀ p q, m p q < n
  inj : ∀ p < n, ∀ q < n, φ p = φ q → p = q
  mem : ∀ p < n, φ p * z = z * φ p
  surj : ∀ w : Γ, w * z = z * w → ∃ p < n, φ p = w

namespace IsCodeModel

variable {n : ℕ} {m : ℕ → ℕ → ℕ} {φ : ℕ → Γ} {z : Γ} (hφ : IsCodeModel n m φ z)
include hφ

theorem mem_V {p : ℕ} (hp : p < n) : φ p ∈ centralizer ({z} : Set Γ) :=
  mem_centralizer_singleton_iff.mpr (hφ.mem p hp)

theorem surj_V {w : Γ} (hw : w ∈ centralizer ({z} : Set Γ)) : ∃ p < n, φ p = w :=
  hφ.surj w (mem_centralizer_singleton_iff.mp hw)

theorem mul_eq_iff {p q r s : ℕ} : φ p * φ q = φ r * φ s ↔ m p q = m r s := by
  rw [← hφ.mul, ← hφ.mul]
  exact ⟨fun h => hφ.inj _ (hφ.lt _ _) _ (hφ.lt _ _) h, fun h => by rw [h]⟩

theorem mul_eq_iff' {p q r : ℕ} (hr : r < n) : φ p * φ q = φ r ↔ m p q = r := by
  rw [← hφ.mul]
  exact ⟨fun h => hφ.inj _ (hφ.lt _ _) _ hr h, fun h => by rw [h]⟩

theorem nCV_eq (a : ℕ) :
    nCV (centralizer ({z} : Set Γ)) (φ a) =
      ((List.range n).filter fun p => m p a == m a p).length := by
  rw [← List.countP_eq_length_filter]
  unfold nCV InCV
  refine card_eq_countP_range φ n _ (fun p hp => hφ.mem_V hp) (fun w hw => hφ.surj_V hw) hφ.inj
    (fun w => w * φ a = φ a * w) _ fun p _ => ?_
  rw [hφ.mul_eq_iff, beq_iff_eq]

theorem nRV_eq (a : ℕ) {t : ℕ} (ht : t < n) :
    nRV (centralizer ({z} : Set Γ)) (φ a) (φ t) =
      ((List.range n).filter fun p => m p a == m a p).countP fun p => m p p == t := by
  rw [List.countP_filter]
  unfold nRV InCV
  rw [show (Nat.card {w // (w ∈ centralizer ({z} : Set Γ) ∧ w * φ a = φ a * w) ∧ w * w = φ t}) =
    Nat.card {w // w ∈ centralizer ({z} : Set Γ) ∧ (w * w = φ t ∧ w * φ a = φ a * w)} from
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by tauto)]
  refine card_eq_countP_range φ n _ (fun p hp => hφ.mem_V hp) (fun w hw => hφ.surj_V hw) hφ.inj _
    _ fun p _ => ?_
  rw [hφ.mul_eq_iff' ht, hφ.mul_eq_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

theorem nZV_eq (a t : ℕ) :
    nZV (centralizer ({z} : Set Γ)) (φ a) (φ t) =
      ((List.range n).filter fun p => m p a == m a p).countP fun p =>
        ((List.range n).filter fun p => m p a == m a p).all fun q =>
          m p q == m q p || m p q == m t (m q p) := by
  rw [List.countP_filter]
  unfold nZV InCV
  rw [show (Nat.card {w // (w ∈ centralizer ({z} : Set Γ) ∧ w * φ a = φ a * w) ∧
      ∀ q, (q ∈ centralizer ({z} : Set Γ) ∧ q * φ a = φ a * q) →
        w * q = q * w ∨ w * q = φ t * (q * w)}) =
    Nat.card {w // w ∈ centralizer ({z} : Set Γ) ∧ ((∀ q, (q ∈ centralizer ({z} : Set Γ) ∧
      q * φ a = φ a * q) → w * q = q * w ∨ w * q = φ t * (q * w)) ∧ w * φ a = φ a * w)} from
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by tauto)]
  refine card_eq_countP_range φ n _ (fun p hp => hφ.mem_V hp) (fun w hw => hφ.surj_V hw) hφ.inj _
    _ fun p hp => ?_
  rw [Bool.and_eq_true, hφ.mul_eq_iff, beq_iff_eq, List.all_eq_true]
  refine and_congr ⟨fun h q hq => ?_, fun h q hq => ?_⟩ Iff.rfl
  · simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hq
    have h1 := h (φ q) ⟨hφ.mem_V hq.1, hφ.mul_eq_iff.mpr hq.2⟩
    simp only [Bool.or_eq_true, beq_iff_eq]
    rcases h1 with h1 | h1
    · exact Or.inl (hφ.mul_eq_iff.mp h1)
    · right
      rw [← hφ.mul, ← hφ.mul, ← hφ.mul] at h1
      exact hφ.inj _ (hφ.lt _ _) _ (hφ.lt _ _) h1
  · obtain ⟨hqV, hqa⟩ := hq
    obtain ⟨q', hq', rfl⟩ := hφ.surj_V hqV
    have h1 := h q' (by simp [hq', hφ.mul_eq_iff.mp hqa])
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (hφ.mul_eq_iff.mpr h1)
    · right
      rw [← hφ.mul, ← hφ.mul, ← hφ.mul, h1]

theorem eq_one {p₀ : ℕ} (h : m p₀ p₀ = p₀) : φ p₀ = 1 := by
  have := hφ.mul p₀ p₀
  rw [h] at this
  exact (mul_eq_left.mp this.symm)

end IsCodeModel

theorem mul16_zero : ∀ ε : Bool, mul16 ε 0 0 = 0 := by
  intro ε
  rw [mul16_eq]
  cases ε <;> decide

theorem mul16_256 : ∀ ε : Bool, mul16 ε 256 256 = 0 := by
  intro ε
  rw [mul16_eq]
  cases ε <;> decide

theorem mem_inv16 {ε : Bool} {u : ℕ} :
    u ∈ inv16 ε ↔ u < 2048 ∧ mul16 ε u u = 0 ∧ u ≠ 0 ∧ u ≠ 256 := by
  simp [inv16, and_assoc]

section Sixteen

variable {ε : Bool} {φ : ℕ → Γ} {z : Γ} (hφ : IsCodeModel 2048 (mul16 ε) φ z) (hz : φ 256 = z)
include hφ hz

theorem mem_inv16_of_conj {g : Γ} {a : ℕ} (ha : a < 2048) (hga : φ a = g * z * g⁻¹)
    (hne : g * z * g⁻¹ ≠ z) : a ∈ inv16 ε := by
  have h1 : φ 0 = 1 := hφ.eq_one (mul16_zero ε)
  have hzz : z * z = 1 := by rw [← hz, ← hφ.mul, mul16_256, h1]
  refine mem_inv16.mpr ⟨ha, ?_, fun h => ?_, fun h => hne ?_⟩
  · refine hφ.inj _ (hφ.lt _ _) _ (by norm_num) ?_
    rw [hφ.mul, hga, h1, show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz]
    group
  · have hz1 : z = 1 := by
      have : g * z * g⁻¹ = 1 := by rw [← hga, h, h1]
      simpa using this
    have := hφ.inj 256 (by norm_num) 0 (by norm_num) (by rw [hz, h1, hz1])
    norm_num at this
  · rw [← hga, h, hz]

theorem conj_eq_of_check16_of_div (hchk : check16 ε = true) {g : Γ}
    (hg : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) {a : ℕ} (ha : a < 2048) (hga : φ a = g * z * g⁻¹)
    (ha0 : a / 512 = 0) : g * z * g⁻¹ = z := by
  obtain ⟨hC1, -, -, hC4, -⟩ := check16_spec hchk
  by_contra hne
  set V := centralizer ({z} : Set Γ) with hVdef
  have hV : ∀ w, w ∈ V ↔ w * z = z * w := fun w => mem_centralizer_singleton_iff (g := z) (k := w)
  have hyV : g⁻¹ * z * g ∈ V := swap_mem hV ((hV _).mpr hg)
  obtain ⟨b, hb, hgb⟩ := hφ.surj _ ((hV _).mp hyV)
  have hyne : g⁻¹ * z * g ≠ z := fun h => hne (by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h]
      _ = z := by group)
  have hau := mem_inv16_of_conj hφ hz ha hga hne
  have hbu := mem_inv16_of_conj hφ hz (g := g⁻¹) hb (by rw [hgb]; group) (by simpa using hyne)
  have e1 := nCV_swap (g := g) hV
  have e2 := nRV_swap (g := g) hV (g * z * g⁻¹)
  have e3 := nRV_swap (g := g) hV z
  rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at e2
  rw [← hga, ← hgb, hφ.nCV_eq a, hφ.nCV_eq b] at e1
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a ha, hφ.nRV_eq b (by norm_num)] at e2
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a (by norm_num), hφ.nRV_eq b hb] at e3
  exact hC4 a hau ha0 (hC1 a hau b hbu e1 e2 e3)

theorem isolated_of_check16 (hchk : check16 ε = true) {g : Γ}
    (hg : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) : g * z * g⁻¹ = z := by
  obtain ⟨hC1, hC2, hC3, -, -⟩ := check16_spec hchk
  by_contra hne
  set V := centralizer ({z} : Set Γ) with hVdef
  have hV : ∀ w, w ∈ V ↔ w * z = z * w := fun w => mem_centralizer_singleton_iff (g := z) (k := w)
  have h1 : φ 0 = 1 := hφ.eq_one (mul16_zero ε)
  obtain ⟨a, ha, hga⟩ := hφ.surj _ hg
  have hyV : g⁻¹ * z * g ∈ V := swap_mem hV ((hV _).mpr hg)
  obtain ⟨b, hb, hgb⟩ := hφ.surj _ ((hV _).mp hyV)
  have hyne : g⁻¹ * z * g ≠ z := fun h => hne (by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h]
      _ = z := by group)
  have hau := mem_inv16_of_conj hφ hz ha hga hne
  have hbu := mem_inv16_of_conj hφ hz (g := g⁻¹) hb (by rw [hgb]; group) (by simpa using hyne)
  have e1 := nCV_swap (g := g) hV
  have e2 := nRV_swap (g := g) hV (g * z * g⁻¹)
  have e3 := nRV_swap (g := g) hV z
  rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at e2
  rw [← hga, ← hgb, hφ.nCV_eq a, hφ.nCV_eq b] at e1
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a ha, hφ.nRV_eq b (by norm_num)] at e2
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a (by norm_num), hφ.nRV_eq b hb] at e3
  have h128 := hC1 a hau b hbu e1 e2 e3
  have hsq := hC2 a hau h128
  simp only [conjSq16, List.any_eq_true, List.mem_filter, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, cent16] at hsq
  obtain ⟨p, ⟨hp, hpa⟩, hp1, w, hw, hwa⟩ := hsq
  have hpx : φ p * φ a = φ a * φ p := hφ.mul_eq_iff.mpr hpa
  have hs1 : φ p * φ p ≠ 1 := by
    rw [← h1, Ne, hφ.mul_eq_iff' (r := 0) (by norm_num)]
    exact hp1
  have hwx : φ w * φ a = φ a * (φ p * φ p) * φ w := by
    have := congrArg φ hwa
    rwa [hφ.mul, hφ.mul, hφ.mul, hφ.mul] at this
  have hq' : InCV V (g⁻¹ * z * g) (g⁻¹ * φ p * g) :=
    (inCV_swap hV (φ p)).mp ⟨(hV _).mpr (hφ.mem p hp), by rw [← hga]; exact hpx⟩
  obtain ⟨b', hb', hgb'⟩ := hφ.surj _ ((hV _).mp hq'.1)
  set g₂ := g⁻¹ * φ w * g with hg₂
  have hu : g₂ * z * g₂⁻¹ = φ (mul16 ε 256 (mul16 ε b' b')) := by
    rw [hφ.mul, hφ.mul, hz, hgb', hg₂]
    have hx : φ w * φ a * (φ w)⁻¹ = φ a * (φ p * φ p) := by rw [hwx]; group
    calc g⁻¹ * φ w * g * z * (g⁻¹ * φ w * g)⁻¹ = g⁻¹ * (φ w * (g * z * g⁻¹) * (φ w)⁻¹) * g := by
          group
      _ = g⁻¹ * (φ a * (φ p * φ p)) * g := by rw [← hga, hx]
      _ = g⁻¹ * (g * z * g⁻¹) * g * (g⁻¹ * φ p * g * (g⁻¹ * φ p * g)) := by rw [hga]; group
      _ = z * (g⁻¹ * φ p * g * (g⁻¹ * φ p * g)) := by group
  have hu1 : g₂ * z * g₂⁻¹ = z := by
    refine conj_eq_of_check16_of_div hφ hz hchk ?_ (hφ.lt _ _) hu.symm (hC3 b' hb')
    rw [hu]
    exact hφ.mem _ (hφ.lt _ _)
  apply hs1
  have h3 : z * (g⁻¹ * φ p * g * (g⁻¹ * φ p * g)) = z := by
    have := hu.symm.trans hu1
    rwa [hφ.mul, hφ.mul, hz, hgb'] at this
  have h2 : g⁻¹ * (φ p * φ p) * g = 1 := by
    rw [show g⁻¹ * (φ p * φ p) * g = g⁻¹ * φ p * g * (g⁻¹ * φ p * g) by group]
    simpa using h3
  calc φ p * φ p = g * (g⁻¹ * (φ p * φ p) * g) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

end Sixteen

variable [Finite Γ]

theorem commute_of_isolated_of_isPGroup {z : Γ} (hO : CFSG.oddCore Γ = ⊥)
    (hz2 : orderOf z = 2) (hp : IsPGroup 2 (centralizer ({z} : Set Γ)))
    (hiso : ∀ g : Γ, g * z * g⁻¹ ∈ centralizer ({z} : Set Γ) → g * z * g⁻¹ = z) (g : Γ) :
    g * z = z * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hCP⟩ := hp.exists_le_sylow
  have hzC : z ∈ centralizer ({z} : Set Γ) := mem_centralizer_singleton_iff.mpr rfl
  have hPC : (P : Subgroup Γ) ≤ centralizer ({z} : Set Γ) := by
    set H := (centralizer ({z} : Set Γ)).subgroupOf (P : Subgroup Γ) with hH
    have : Group.IsNilpotent (P : Subgroup Γ) := P.isPGroup'.isNilpotent
    by_contra hle
    have hlt : H < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hle fun x hx => ?_
      have : (⟨x, hx⟩ : P) ∈ H := by rw [htop]; exact mem_top _
      exact this
    obtain ⟨h, hhN, hhH⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hlt)
    have hzH : (⟨z, hCP hzC⟩ : P) ∈ H := hzC
    have h1 : h * ⟨z, hCP hzC⟩ * h⁻¹ ∈ H := (mem_normalizer_iff.mp hhN _).mp hzH
    have h2 : (h : Γ) * z * (h : Γ)⁻¹ = z := hiso h h1
    refine hhH (mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr ?_))
    calc (h : Γ) * z = (h : Γ) * z * (h : Γ)⁻¹ * h := by group
      _ = z * h := by rw [h2]
  have hPeq : (P : Subgroup Γ) = centralizer ({z} : Set Γ) := le_antisymm hPC hCP
  refine commute_of_isolated hO P (hCP hzC) (fun s hs => ?_) hz2 (fun x hx => ?_) g
  · exact (mem_centralizer_singleton_iff.mp (hPC hs))
  · rw [hPeq] at hx
    have := hiso x⁻¹ (by simpa using hx)
    simpa using this

end CFSG.ComponentClassification.GMS78
