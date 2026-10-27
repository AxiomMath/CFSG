module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Inner

variable {X : Type} [Group X]

theorem psu_conj_range_normal : ((MulAut.conj : X →* MulAut X).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, ?_⟩
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul]

theorem psu_center_bot_of_simple_of_nonab [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

variable (hc : Subgroup.center X = ⊥)

include hc in
theorem psu_conj_injective : Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro g g' h
  have h2 : g'⁻¹ * g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have e := DFunLike.congr_fun h y
    simp only [MulAut.conj_apply] at e
    calc y * (g'⁻¹ * g) = g'⁻¹ * (g' * y * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * y * g⁻¹) * g := by rw [← e]
      _ = g'⁻¹ * g * y := by group
  rw [hc, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.mp h2).symm

include hc in
theorem psu_fixed_of_commute (α : MulAut X) (g : X)
    (h : MulAut.conj g * α = α * MulAut.conj g) : α g = g := by
  have h1 : ∀ y : X, g * y * g⁻¹ = α g * y * (α g)⁻¹ := by
    intro y
    have e := DFunLike.congr_fun h (α.symm y)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at e
    exact e
  have h2 : (α g)⁻¹ * g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have e := h1 y
    calc y * ((α g)⁻¹ * g) = (α g)⁻¹ * (α g * y * (α g)⁻¹) * g := by group
      _ = (α g)⁻¹ * (g * y * g⁻¹) * g := by rw [← e]
      _ = (α g)⁻¹ * g * y := by group
  rw [hc, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

include hc in
theorem psu_centralizer_conj_range :
    Subgroup.centralizer ((MulAut.conj : X →* MulAut X).range : Set (MulAut X)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  ext g
  have h : MulAut.conj g * α = α * MulAut.conj g :=
    Subgroup.mem_centralizer_iff.mp hα (MulAut.conj g) ⟨g, rfl⟩
  have := psu_fixed_of_commute hc α g h
  simpa using this

include hc in
theorem psu_card_fixed_eq_card_inf (σ : MulAut X) :
    Nat.card ↥(fixedSubgroup σ) = Nat.card ↥((MulAut.conj : X →* MulAut X).range ⊓
      Subgroup.centralizer ({σ} : Set (MulAut X))) := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun g => ⟨MulAut.conj (g : X), ?_⟩) ⟨?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    ext x
    have hg : σ (g : X) = g := g.2
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, hg]
  · intro g g' h
    apply Subtype.ext
    exact psu_conj_injective hc (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    obtain ⟨⟨g, rfl⟩, hσ⟩ := Subgroup.mem_inf.mp ha
    have h' := Subgroup.mem_centralizer_singleton_iff.mp hσ
    exact ⟨⟨g, psu_fixed_of_commute hc σ g h'⟩, rfl⟩

end Inner

theorem psu_A6_pow_eight (g : alternatingGroup (Fin 6)) (h : g ^ 8 = 1) : g ^ 4 = 1 := by
  have h1 : (g : Equiv.Perm (Fin 6)) ^ 8 = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : orderOf (g : Equiv.Perm (Fin 6)) ∣ 8 := orderOf_dvd_of_pow_eq_one h1
  rw [← Equiv.Perm.lcm_cycleType] at h2
  have h3 : (g : Equiv.Perm (Fin 6)).cycleType.lcm ∣ 4 := by
    rw [Multiset.lcm_dvd]
    intro b hb
    have hb8 : b ∣ 8 := (Multiset.dvd_lcm hb).trans h2
    have hb6 : b ≤ 6 := by
      have := (Multiset.le_sum_of_mem hb).trans
        (Equiv.Perm.sum_cycleType_le (g : Equiv.Perm (Fin 6)))
      simpa using this
    interval_cases b <;> revert hb8 <;> decide
  rw [Equiv.Perm.lcm_cycleType] at h3
  apply Subtype.ext
  simpa using orderOf_dvd_iff_pow_eq_one.mp h3

section Hyp

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.psu_pow_four (h : A6Hyp σ D) (x : ↥(fixedSubgroup σ)) (hx : x ∈ D)
    (h8 : x ^ 8 = 1) : x ^ 4 = 1 := by
  obtain ⟨-, ⟨eA⟩, -⟩ := h
  have h1 : eA ⟨x, hx⟩ ^ 8 = 1 := by rw [← map_pow]; simp [← Subtype.coe_inj, h8]
  have h2 := psu_A6_pow_eight _ h1
  have h3 : eA ((⟨x, hx⟩ : D) ^ 4) = eA 1 := by rw [map_pow, h2, map_one]
  have h4 := eA.injective h3
  exact congrArg Subtype.val h4

theorem A6Hyp.psu_not_comm (h : A6Hyp σ D) : ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨-, ⟨eA⟩, -⟩ := h
  obtain ⟨a, b, hab⟩ := a6sq_nonab
  refine ⟨(eA.symm a : ↥(fixedSubgroup σ)), (eA.symm b : ↥(fixedSubgroup σ)), fun hc => hab ?_⟩
  apply eA.symm.injective
  apply Subtype.ext
  apply Subtype.ext
  simpa using hc

end Hyp

end CFSG.ComponentClassification.CatFC
