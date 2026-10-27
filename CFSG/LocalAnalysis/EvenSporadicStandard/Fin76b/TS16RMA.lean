module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem s16Gen_of_gen {G : Type} [Group G] [Finite G] {S : Subgroup G} {s z t : G} (hs : s ∈ S)
    (hzS : z ∈ S) (hord : orderOf s = 8) (hzs : z * s * z⁻¹ = s⁻¹) (hs4 : s ^ 4 = t)
    (hz2 : z * z = 1) (hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j) (hcard : Nat.card ↥S = 16) :
    S16Gen S s z t := by
  have hs8 : s ^ 8 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one s
  have hzns : z ∉ zpowers s := by
    intro hz
    have hle : S ≤ zpowers s := by
      intro y hy
      obtain ⟨i, j, rfl⟩ := hgen y hy
      exact mul_mem (pow_mem (mem_zpowers s) i) (pow_mem hz j)
    have h1 : Nat.card ↥S ≤ Nat.card ↥(zpowers s) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord, hcard] at h1
    omega
  exact ⟨hs, hzS, hs8, hs4, hz2, hzs, hord, hzns, hgen⟩

theorem mem_normalizer_sup_of_inv {G : Type} [Group G] {D E : Subgroup G} {n : G}
    (hn : n * n = 1) (hD : ∀ d ∈ D, n * d * n⁻¹ ∈ D) (hE : ∀ e ∈ E, n * e * n⁻¹ ∈ E) :
    n ∈ normalizer ((D ⊔ E : Subgroup G) : Set G) := by
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  have key : ∀ w ∈ D ⊔ E, n * w * n⁻¹ ∈ D ⊔ E := by
    have hle : D ⊔ E ≤ (D ⊔ E).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun d hd => ?_) (fun e he => ?_)
      · show (MulAut.conj n).toMonoidHom d ∈ D ⊔ E
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left (hD d hd)
      · show (MulAut.conj n).toMonoidHom e ∈ D ⊔ E
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right (hE e he)
    intro w hw
    have := hle hw
    simpa [MulAut.conj_apply] using this
  rw [mem_normalizer_iff]
  intro w
  constructor
  · exact key w
  · intro hw
    have := key _ hw
    have h2 : n * (n * w * n⁻¹) * n⁻¹ = w := by
      calc n * (n * w * n⁻¹) * n⁻¹ = (n * n) * w * (n⁻¹ * n⁻¹) := by group
        _ = w := by rw [hn, hni, hn]; group
    rwa [h2] at this

theorem exists_sigma_five {G : Type} [Group G] {L : Subgroup G} {z t β : G} {E S : Subgroup G}
    {s : G} (hS : S16Gen S s z t) {σ₀ v ξ : G} (hD0 : S16LData G L z t β E σ₀ v ξ)
    (hD1 : S16LData G L z t β E (σ₀ * z) v ξ)
    (h35 : σ₀ * s * σ₀⁻¹ = s ^ 3 ∨ σ₀ * s * σ₀⁻¹ = s ^ 5) :
    ∃ σ : G, S16LData G L z t β E σ v ξ ∧ σ * s * σ⁻¹ = s ^ 5 := by
  rcases h35 with h | h
  · refine ⟨σ₀ * z, hD1, ?_⟩
    have h1 : σ₀ * z * s * (σ₀ * z)⁻¹ = (σ₀ * s * σ₀⁻¹)⁻¹ := by
      calc σ₀ * z * s * (σ₀ * z)⁻¹ = σ₀ * (z * s * z⁻¹) * σ₀⁻¹ := by group
        _ = σ₀ * s⁻¹ * σ₀⁻¹ := by rw [hS.hzs]
        _ = (σ₀ * s * σ₀⁻¹)⁻¹ := by group
    rw [h1, h]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact hS.hs8
  · exact ⟨σ₀, hD0, h⟩

theorem S16LData.exists_fixed_invol {G : Type} [Group G] {L : Subgroup G} {z t β : G}
    {E : Subgroup G} {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ) (ht1 : t ≠ 1) :
    ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ := by
  have hmem : v * ξ ∈ E ⊓ centralizer ({σ} : Set G) := by
    rw [← hD.CE_eq]
    exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hD.ξ_sq
  have hξv : ξ * v * ξ = v⁻¹ := by
    have := hD.ξ_v
    rwa [hξi] at this
  have hsq : v * ξ * (v * ξ) = 1 := by
    calc v * ξ * (v * ξ) = v * (ξ * v * ξ) := by group
      _ = 1 := by rw [hξv]; group
  refine ⟨v * ξ, hmem.1, ?_, ?_, hsq, (mem_centralizer_singleton_iff.1 hmem.2).symm⟩
  · intro h1
    apply ht1
    have hvξ : v = ξ := by
      have : v = ξ⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, hξi]
    rw [← hD.v4, hvξ]
    calc ξ ^ 4 = (ξ * ξ) * (ξ * ξ) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hD.ξ_sq, one_mul]
  · intro h1
    apply ht1
    have hξ3 : ξ = v ^ 3 := by
      have h2 : ξ = v⁻¹ * t := by
        calc ξ = v⁻¹ * (v * ξ) := by group
          _ = v⁻¹ * t := by rw [h1]
      rw [h2, ← hD.v4]
      group
    have hv6 : v ^ 6 = 1 := by
      calc v ^ 6 = v ^ 3 * v ^ 3 := by group
        _ = ξ * ξ := by rw [← hξ3]
        _ = 1 := hD.ξ_sq
    have hv2 : v ^ 2 = 1 := by
      calc v ^ 2 = v ^ 8 * (v ^ 6)⁻¹ := by group
        _ = 1 := by rw [hD.v8, hv6]; group
    rw [← hD.v4]
    calc v ^ 4 = (v ^ 2) * (v ^ 2) := by group
      _ = 1 := by rw [hv2]; group

theorem sigma_act_a {G : Type} [Group G] {s σ : G} (hs8 : s ^ 8 = 1)
    (hσs : σ * s * σ⁻¹ = s ^ 5) : σ * (s * s) * σ⁻¹ = s * s := by
  calc σ * (s * s) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * s * σ⁻¹) := by group
    _ = s ^ 5 * s ^ 5 := by rw [hσs]
    _ = s ^ 8 * (s * s) := by group
    _ = s * s := by rw [hs8, one_mul]

theorem sigma_act_b {G : Type} [Group G] {s z σ : G} (hσz : σ * z = z * σ)
    (hσs : σ * s * σ⁻¹ = s ^ 5) : σ * (s * z) * σ⁻¹ = s ^ 4 * (s * z) := by
  have hσz' : σ * z * σ⁻¹ = z := by
    calc σ * z * σ⁻¹ = (z * σ) * σ⁻¹ := by rw [hσz]
      _ = z := by group
  calc σ * (s * z) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * z * σ⁻¹) := by group
    _ = s ^ 5 * z := by rw [hσs, hσz']
    _ = s ^ 4 * (s * z) := by group

end CFSG.EvenSporadicStandard.Fin76b
