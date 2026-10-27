module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseTrick
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] def rootGroup (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) : Subgroup G :=
  corr (X := G) e (altSub S)

@[expose] def IsNear (e : L ≃* alternatingGroup (Fin n)) (y : G) : Prop :=
  ∃ hy : y ∈ L, 4 ≤ Nat.card (Function.fixedPoints
    ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))

@[expose] def NearGivesRoot (k : ℕ) (N : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) (Q : Subgroup G) (z : G),
    Setting G L n → Cyc L Q z → Nat.card Q = 2 → centralizer ({z} : Set G) ≤ L ⊔ Q → N n →
    ∀ e : L ≃* alternatingGroup (Fin n), (∃ y ∈ FusionSet L z, IsNear e y) →
      ∃ S : Finset (Fin n), S.card = k ∧ ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) →
        orderOf b = 2 → ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b

@[expose] def FarOnlyFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) (Q : Subgroup G) (z : G),
    Setting G L n → Cyc L Q z → Nat.card Q = 2 → centralizer ({z} : Set G) ≤ L ⊔ Q → 12 ≤ n →
    ∀ e : L ≃* alternatingGroup (Fin n), (∀ y ∈ FusionSet L z, ¬ IsNear e y) → False

@[expose] def RootCover : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G) (n : ℕ), 13 ≤ n →
    ∀ (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)), S.card = 4 →
      ∃ e₀ ∈ rootGroup e S, orderOf e₀ = 2 ∧ e₀ ∈ L ∧
        (∃ l ∈ L, l * e₀ * l⁻¹ ∈ centralizer (rootGroup e S : Set G)) ∧
        ∀ y ∈ L, orderOf y = 2 → ∃ l ∈ L, (l * y * l⁻¹ ∈ centralizer (rootGroup e S : Set G) ∨
          ∃ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) ∧ orderOf b = 2 ∧ b * e₀ ≠ 1 ∧
            l * y * l⁻¹ = b * e₀)

@[expose] def NearCover (k : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G) (n : ℕ), 12 ≤ n →
    ∀ (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)), S.card = k → k ≤ 4 →
      ∀ y ∈ L, orderOf y = 2 → IsNear e y →
        ∃ l ∈ L, l * y * l⁻¹ ∈ centralizer (rootGroup e S : Set G)

@[expose] def FarClass : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G) (n : ℕ) (e : L ≃* alternatingGroup (Fin n)),
    ∀ y ∈ L, ∀ y' ∈ L, orderOf y = 2 → orderOf y' = 2 → ¬ IsNear e y → ¬ IsNear e y' →
      ∃ l ∈ L, l * y * l⁻¹ = y'

@[expose] def NearOnlyFalse12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) (Q : Subgroup G) (z : G),
    Setting G L n → Cyc L Q z → Nat.card Q = 2 → centralizer ({z} : Set G) ≤ L ⊔ Q → n = 12 →
    ∀ e : L ≃* alternatingGroup (Fin n),
      (∀ y ∈ L, orderOf y = 2 → IsNear e y → y ∈ FusionSet L z) →
      (∀ y ∈ FusionSet L z, IsNear e y) → False

theorem fusionAll_of_shape_one_ge13 (hN : NearGivesRoot 4 (13 ≤ ·)) (hF : FarOnlyFalse)
    (hC : RootCover) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : 13 ≤ n) : FusionAll L z := by
  obtain ⟨e⟩ := h.iso
  by_cases hnear : ∃ y ∈ FusionSet L z, IsNear e y
  · obtain ⟨S, hS, hsec⟩ := hN G L n Q z h d hQ2 hE hn e hnear
    obtain ⟨e₀, he₀R, he₀2, he₀L, he₀cov, hcov⟩ := hC G L n hn e S hS
    exact fusionAll_of_section_fusion h d he₀R he₀2 he₀L hsec hcov he₀cov
  · push Not at hnear
    exact (hF G L n Q z h d hQ2 hE (by omega) e hnear).elim

theorem fusionAll_of_shape_one_twelve (hN : NearGivesRoot 3 (· = 12)) (hF : FarOnlyFalse)
    (hCov : NearCover 3) (hFC : FarClass) (hNO : NearOnlyFalse12)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : n = 12) : FusionAll L z := by
  obtain ⟨e⟩ := h.iso
  by_cases hnear : ∃ y ∈ FusionSet L z, IsNear e y
  · obtain ⟨S, hS, hsec⟩ := hN G L n Q z h d hQ2 hE hn e hnear
    have hnearY : ∀ y ∈ L, orderOf y = 2 → IsNear e y → y ∈ FusionSet L z := by
      intro y hy hy2 hyn
      obtain ⟨l, hl, hlC⟩ := hCov G L n (by omega) e S hS (by omega) y hy hy2 hyn
      have hl2 : orderOf (l * y * l⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hy2
      obtain ⟨h', -, hh'⟩ := hsec _ (mul_mem (mul_mem hl hy) (inv_mem hl)) hlC hl2
      have hY : l * y * l⁻¹ ∈ FusionSet L z :=
        ⟨mul_mem (mul_mem hl hy) (inv_mem hl), hl2, h', hh'⟩
      have := FusionSet.conj h d hY (inv_mem hl)
      simpa [mul_assoc] using this
    rw [fusionAll_iff]
    intro y hy hy2
    by_cases hyn : IsNear e y
    · exact hnearY y hy hy2 hyn
    · by_cases hfar : ∃ y₀ ∈ FusionSet L z, ¬ IsNear e y₀
      · obtain ⟨y₀, hy₀, hy₀n⟩ := hfar
        obtain ⟨l, hl, hly⟩ := hFC G L n e y hy y₀ hy₀.1 hy2 hy₀.2.1 hyn hy₀n
        have := FusionSet.conj h d hy₀ (inv_mem hl)
        rw [← hly] at this
        simpa [mul_assoc] using this
      · push Not at hfar
        exact (hNO G L n Q z h d hQ2 hE hn e hnearY hfar).elim
  · push Not at hnear
    exact (hF G L n Q z h d hQ2 hE (by omega) e hnear).elim

theorem fusionAll_of_shape_one_of_props (hN4 : NearGivesRoot 4 (13 ≤ ·))
    (hN3 : NearGivesRoot 3 (· = 12)) (hF : FarOnlyFalse) (hC : RootCover) (hCov : NearCover 3)
    (hFC : FarClass) (hNO : NearOnlyFalse12) (h : Setting G L n) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : 12 ≤ n) :
    FusionAll L z := by
  rcases Nat.lt_or_ge n 13 with h13 | h13
  · exact fusionAll_of_shape_one_twelve hN3 hF hCov hFC hNO h d hQ2 hE (by omega)
  · exact fusionAll_of_shape_one_ge13 hN4 hF hC h d hQ2 hE h13

end CFSG.OddStandard.AltStdSec
