module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.Burgoyne CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Pointwise

section Crit2

variable {Γ : Type} [Group Γ]

theorem oddCoreCyclic_of_outCyc_fix [Finite Γ] (hZ : Subgroup.center Γ = ⊥)
    (hcyc : IsCyclic (Outer Γ))
    (hC : ∀ α : MulAut Γ, α * α = 1 → α ≠ 1 → ∀ N : Subgroup Γ, N ≤ fixSub α →
      (∀ g ∈ fixSub α, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → Odd (Nat.card ↥N) → N = ⊥) :
    OddCoreCyclic Γ := by
  intro B hB t htB ht
  have hinj := conj_injective_of_center_eq_bot hZ
  have htt : t * t = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ht])
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; omega
  set W : Subgroup (MulAut Γ) := oddCoreIn B t with hW
  set C : Subgroup (MulAut Γ) := B ⊓ centralizer ({t} : Set (MulAut Γ)) with hCdef
  have hWodd : Nat.Coprime 2 (Nat.card W) := by
    rw [hW]
    unfold oddCoreIn
    rw [Subgroup.card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have hWnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have := (pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem x hx ⟨c, hc⟩
    exact ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, this, rfl⟩
  have hker : W ⊓ OuterAutomorphisms.inner Γ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwW, g, rfl⟩
    set N : Subgroup Γ := W.comap (MulAut.conj : Γ →* MulAut Γ) with hN
    have hfixmem : ∀ k : Γ, MulAut.conj k * t = t * MulAut.conj k → k ∈ fixSub t := by
      intro k hc
      have h1 : t * MulAut.conj k * t⁻¹ = MulAut.conj k := by
        rw [← hc]; group
      show t k = k
      apply hinj
      have h2 : t * MulAut.conj k * t⁻¹ = MulAut.conj (t k) := by
        ext y; simp [MulAut.conj_apply]
      rw [← h2, h1]
    have hNs : N ≤ fixSub t := fun n hn => hfixmem n (commute_of_mem_oddCoreIn hn)
    have hNnorm : ∀ d ∈ fixSub t, ∀ n ∈ N, d * n * d⁻¹ ∈ N := by
      intro d hd n hn
      have hdt : t * MulAut.conj d * t⁻¹ = MulAut.conj d := by
        have h2 : t * MulAut.conj d * t⁻¹ = MulAut.conj (t d) := by
          ext y; simp [MulAut.conj_apply]
        rw [h2]
        congr 1
      have hdcen : MulAut.conj d ∈ centralizer ({t} : Set (MulAut Γ)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc MulAut.conj d * t = (t * MulAut.conj d * t⁻¹) * t := by rw [hdt]
          _ = t * MulAut.conj d := by group
      have hdc : (MulAut.conj d) ∈ C := ⟨hB ⟨d, rfl⟩, hdcen⟩
      have := hWnorm _ hdc _ hn
      show MulAut.conj (d * n * d⁻¹) ∈ W
      simpa [map_mul, map_inv] using this
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card W := by
        have hmap : Nat.card (N.map (MulAut.conj : Γ →* MulAut Γ)) = Nat.card N :=
          Subgroup.card_map_of_injective hinj
        rw [← hmap]
        exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 hWodd)
    have hNbot := hC t htt ht1 N hNs hNnorm hNodd
    have hg : g ∈ N := hwW
    rw [hNbot, Subgroup.mem_bot] at hg
    rw [hg, map_one]
    exact Subgroup.one_mem _
  have := hcyc
  refine isCyclic_of_injective
    ((QuotientGroup.mk' (OuterAutomorphisms.inner Γ)).comp W.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : (w : MulAut Γ) ∈ OuterAutomorphisms.inner Γ := (QuotientGroup.eq_one_iff _).mp hw
  have : (w : MulAut Γ) ∈ W ⊓ OuterAutomorphisms.inner Γ := ⟨w.2, hw'⟩
  rw [hker, Subgroup.mem_bot] at this
  exact Subtype.ext this

end Crit2

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
