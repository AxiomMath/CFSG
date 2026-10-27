module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionP
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionQ

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] {σ : Setting G} {a : G}

theorem conjSub_pow_T (haN : a ∈ Subgroup.normalizer (σ.T : Set G)) (n : ℕ) :
    conjSub (a ^ n) σ.T = σ.T :=
  conjSub_eq_self_of_mem (pow_mem haN n)

theorem conjSub_pow_C (haN : a ∈ Subgroup.normalizer (σ.T : Set G)) (n : ℕ) :
    conjSub (a ^ n) σ.C = σ.C :=
  conjSub_eq_self_of_mem (normalizer_T_le_M (pow_mem haN n))

theorem conjSub_pow_inv_C (haN : a ∈ Subgroup.normalizer (σ.T : Set G)) (n : ℕ) :
    conjSub (a ^ n)⁻¹ σ.C = σ.C :=
  conjSub_eq_self_of_mem (normalizer_T_le_M (inv_mem (pow_mem haN n)))

theorem xs_inverts_Ps_zero {r : ℕ}
    (hinv : ∀ u ∈ σ.Ps r 0, σ.x₂ * u * σ.x₂⁻¹ = u⁻¹) {k : Fin 3} (hk : k ≠ 0) {v : G}
    (hv : v ∈ σ.Ps r 0) : σ.xs k * v * (σ.xs k)⁻¹ = v⁻¹ := by
  fin_cases k
  · exact absurd rfl hk
  · exact hinv v hv
  · show σ.x₃ * v * σ.x₃⁻¹ = v⁻¹
    have hvN : v⁻¹ ∈ σ.N := σ.N.inv_mem (pCoreIn_le r _ hv)
    rw [x₃_def, show σ.x * σ.x₂ * v * (σ.x * σ.x₂)⁻¹ = σ.x * (σ.x₂ * v * σ.x₂⁻¹) * σ.x⁻¹ by
      group, hinv v hv, ← (σ.mem_N_iff _).mp hvN, mul_inv_cancel_right]

section Cycle

variable (hcyc : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1))
include hcyc

theorem conjSub_pow_N (i : Fin 3) : conjSub (a ^ (i : ℕ)) σ.N = σ.Ns i := by
  rw [Setting.N, conjSub_centralizer_singleton, show σ.x = σ.xs 0 from rfl, pow_conj_xs hcyc,
    zero_add]
  rfl

theorem conjSub_Ns (i : Fin 3) : conjSub a (σ.Ns i) = σ.Ns (i + 1) := by
  rw [Setting.Ns, conjSub_centralizer_singleton, hcyc]
  rfl

theorem conjSub_pow_Ps (r : ℕ) (i : Fin 3) : conjSub (a ^ (i : ℕ)) (σ.Ps r 0) = σ.Ps r i := by
  rw [Ps_zero_eq, conjSub_pCoreIn, conjSub_pow_N hcyc]
  rfl

theorem conjSub_Ps (r : ℕ) (i : Fin 3) : conjSub a (σ.Ps r i) = σ.Ps r (i + 1) := by
  rw [Setting.Ps, conjSub_pCoreIn, conjSub_Ns hcyc]
  rfl

theorem conjSub_conjSub_pow {X : Subgroup G} (hCX : σ.C ≤ Subgroup.normalizer (X : Set G))
    (i : Fin 3) : conjSub a (conjSub (a ^ (i : ℕ)) X) = conjSub (a ^ ((i + 1 : Fin 3) : ℕ)) X := by
  rw [conjSub_conjSub, ← pow_succ']
  fin_cases i
  · rfl
  · rfl
  · show conjSub (a ^ 3) X = conjSub (a ^ 0) X
    rw [pow_zero, conjSub_one, conjSub_eq_self_of_mem (hCX (pow_three_mem_C hcyc))]

theorem Ps_abelian {r : ℕ} (hab : ∀ u ∈ σ.Ps r 0, ∀ v ∈ σ.Ps r 0, u * v = v * u) (i : Fin 3) :
    ∀ u ∈ σ.Ps r i, ∀ v ∈ σ.Ps r i, u * v = v * u := by
  intro u hu v hv
  rw [← conjSub_pow_Ps hcyc r i, mem_conjSub_iff] at hu hv
  have h := hab _ hu _ hv
  calc u * v = a ^ (i : ℕ) * ((a ^ (i : ℕ))⁻¹ * u * a ^ (i : ℕ) *
        ((a ^ (i : ℕ))⁻¹ * v * a ^ (i : ℕ))) * (a ^ (i : ℕ))⁻¹ := by group
    _ = a ^ (i : ℕ) * ((a ^ (i : ℕ))⁻¹ * v * a ^ (i : ℕ) *
        ((a ^ (i : ℕ))⁻¹ * u * a ^ (i : ℕ))) * (a ^ (i : ℕ))⁻¹ := by rw [h]
    _ = v * u := by group

theorem Ps_inverted {r : ℕ}
    (hinv : ∀ u ∈ σ.Ps r 0, σ.x₂ * u * σ.x₂⁻¹ = u⁻¹) (i j : Fin 3) (hji : j ≠ i) {u : G}
    (hu : u ∈ σ.Ps r i) : σ.xs j * u * (σ.xs j)⁻¹ = u⁻¹ := by
  rw [← conjSub_pow_Ps hcyc r i, mem_conjSub_iff] at hu
  have hj : σ.xs j = a ^ (i : ℕ) * σ.xs (j - i) * (a ^ (i : ℕ))⁻¹ := by
    rw [pow_conj_xs hcyc, sub_add_cancel]
  have h := xs_inverts_Ps_zero hinv (sub_ne_zero.mpr hji) hu
  rw [hj]
  calc a ^ (i : ℕ) * σ.xs (j - i) * (a ^ (i : ℕ))⁻¹ * u *
        (a ^ (i : ℕ) * σ.xs (j - i) * (a ^ (i : ℕ))⁻¹)⁻¹ =
      a ^ (i : ℕ) * (σ.xs (j - i) * ((a ^ (i : ℕ))⁻¹ * u * a ^ (i : ℕ)) * (σ.xs (j - i))⁻¹) *
        (a ^ (i : ℕ))⁻¹ := by group
    _ = u⁻¹ := by rw [h]; group

end Cycle

theorem QPair.conj_cases {r : ℕ} {J Q Qs : Subgroup G} (hQ : QPair σ r J Q Qs)
    (hJ : σ.IsLayerComplement J) (hP₀ : σ.Ps r 0 ≤ σ.ON) (hc : σ.DeltaEpsMinus ∧ r ∣ σ.q)
    {g : G} (hgC : conjSub g σ.C = σ.C) :
    conjSub g Q ≠ conjSub g Qs ∧ Nat.card (conjSub g Q) = σ.q ∧
      Nat.card (conjSub g Qs) = σ.q ∧ conjSub g J = conjSub g Q ⊔ conjSub g Qs ∧
      (∃ z ∈ conjSub g σ.D, conjSub z (conjSub g Q) = conjSub g Qs) ∧
      (∀ X : Subgroup G, X ≤ conjSub g J → IsPGroup r X →
        σ.C ≤ Subgroup.normalizer (X : Set G) → X ≤ conjSub g Q ∨ X ≤ conjSub g Qs) ∧
      (∀ X : Subgroup G, X ≤ conjSub g Q → σ.C ≤ Subgroup.normalizer (X : Set G) →
        X = ⊥ ∨ X = conjSub g Q) ∧
      (∀ X : Subgroup G, X ≤ conjSub g Qs → σ.C ≤ Subgroup.normalizer (X : Set G) →
        X = ⊥ ∨ X = conjSub g Qs) ∧
      conjSub g Q ≤ Subgroup.centralizer (conjSub g (σ.Ps r 0) : Set G) ∧
      conjSub g Qs ≤ Subgroup.centralizer (conjSub g (σ.Ps r 0) : Set G) := by
  obtain ⟨hne, hcQ, hcQs, hJeq, ⟨z, hzD, hz⟩, hirr, hirrs⟩ := hQ.cases hc
  have hginv : conjSub g⁻¹ σ.C = σ.C := by
    calc conjSub g⁻¹ σ.C = conjSub g⁻¹ (conjSub g σ.C) := by rw [hgC]
      _ = σ.C := conjSub_inv_conjSub g σ.C
  have hJP : J ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) :=
    hJ.centralizes.trans (Subgroup.centralizer_le hP₀)
  have hirr' : ∀ {Y : Subgroup G}, (∀ X : Subgroup G, X ≤ Y →
      σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Y) → ∀ X : Subgroup G,
        X ≤ conjSub g Y → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = conjSub g Y := by
    intro Y hY X hXY hCX
    rcases hY (conjSub g⁻¹ X) (le_conjSub_iff.mp hXY) (le_normalizer_conjSub_of_eq hginv hCX)
      with h | h
    · left
      rw [← conjSub_conjSub_inv g X, h, conjSub_bot]
    · right
      rw [← conjSub_conjSub_inv g X, h]
  refine ⟨(conjSub_injective g).ne hne, by rw [card_conjSub, hcQ], by rw [card_conjSub, hcQs],
    by rw [hJeq, conjSub_sup], ⟨g * z * g⁻¹, conj_mem_conjSub hzD, ?_⟩, ?_, hirr' hirr,
    hirr' hirrs, ?_, ?_⟩
  · rw [conjSub_conjSub, show g * z * g⁻¹ * g = g * z by group, ← conjSub_conjSub, hz]
  · intro X hXJ hX hCX
    rcases hQ.cover (conjSub g⁻¹ X) (le_conjSub_iff.mp hXJ) (isPGroup_conjSub hX _)
      (le_normalizer_conjSub_of_eq hginv hCX) with h | h
    · exact Or.inl (le_conjSub_iff.mpr h)
    · exact Or.inr (le_conjSub_iff.mpr h)
  · rw [← conjSub_centralizer]
    exact conjSub_mono (hQ.le.trans hJP)
  · rw [← conjSub_centralizer]
    exact conjSub_mono (hQ.le_s.trans hJP)

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
