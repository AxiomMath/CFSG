module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Three

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Equiv Equiv.Perm Finset Subgroup

namespace AltConj

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isConj_alternatingGroup_of_odd_commute {σ τ : alternatingGroup α}
    (hc : (σ : Perm α).cycleType = (τ : Perm α).cycleType) {ρ : Perm α}
    (hρ : Perm.sign ρ = -1) (hρσ : Commute ρ (σ : Perm α)) : IsConj σ τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hc)
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · exact isConj_iff.mpr ⟨⟨π, Perm.mem_alternatingGroup.mpr h⟩, Subtype.ext (by simpa using hπ)⟩
  · refine isConj_iff.mpr ⟨⟨π * ρ, Perm.mem_alternatingGroup.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [map_mul, h, hρ, Int.units_mul_self]
    · show π * ρ * (σ : Perm α) * (π * ρ)⁻¹ = τ
      rw [← hπ, mul_inv_rev, mul_assoc π ρ, hρσ.eq, ← mul_assoc π, mul_assoc _ ρ,
        mul_inv_cancel_left]

theorem exists_odd_commute_of_sq_eq_one {σ : Perm α} (h : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ ρ : Perm α, Perm.sign ρ = -1 ∧ Commute ρ σ := by
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  have hσσ : σ (σ a) = a := by
    have := congrArg (fun f : Perm α => f a) h
    simpa [pow_two] using this
  refine ⟨swap a (σ a), Perm.sign_swap (Ne.symm ha), ?_⟩
  have key : σ * swap a (σ a) * σ⁻¹ = swap a (σ a) := by
    rw [← Equiv.swap_apply_apply, hσσ, Equiv.swap_comm]
  show swap a (σ a) * σ = σ * swap a (σ a)
  calc swap a (σ a) * σ = (σ * swap a (σ a) * σ⁻¹) * σ := by rw [key]
    _ = σ * swap a (σ a) := by group

theorem exists_odd_commute_of_pow_three_eq_one {σ : Perm α} (h3 : σ ^ 3 = 1) {a d : α}
    (ha : σ a ≠ a) (hd : σ d ≠ d) (had : ¬ σ.SameCycle a d) :
    ∃ ρ : Perm α, Perm.sign ρ = -1 ∧ Commute ρ σ := by
  have had' : a ≠ d := fun h => had (h ▸ SameCycle.refl σ a)
  have had1 : σ a ≠ d := fun h => had ⟨1, by simpa using h⟩
  have had2 : σ d ≠ a := fun h => had (SameCycle.symm ⟨1, by simpa using h⟩)
  set u : Perm α := swap a d with hu
  set v : Perm α := σ * u * σ⁻¹ with hv
  set w : Perm α := σ * v * σ⁻¹ with hw
  have hσu : σ * u * σ⁻¹ = v := rfl
  have hσv : σ * v * σ⁻¹ = w := rfl
  have hσw : σ * w * σ⁻¹ = u := by
    have h3' : σ * σ * σ = 1 := by simpa [pow_succ] using h3
    calc σ * w * σ⁻¹ = (σ * σ * σ) * u * (σ * σ * σ)⁻¹ := by rw [hw, hv]; group
      _ = u := by rw [h3']; group
  have huv : Commute u v := by
    have h4 : [a, d, σ a, σ d].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      refine ⟨⟨had', Ne.symm ha, Ne.symm had2⟩, ⟨Ne.symm had1, Ne.symm hd⟩,
        fun h => had' (σ.injective h)⟩
    have := (disjoint_swap_swap h4).commute
    rw [hv, hu, ← Equiv.swap_apply_apply]
    exact this
  have hvw : Commute v w := (Commute.conj_iff σ).mpr huv
  have hwu : Commute w u := by
    rw [← Commute.conj_iff σ, hσw, hσu]
    exact huv
  have huw : Commute u w := hwu.symm
  have key : σ * (u * v * w) * σ⁻¹ = u * v * w := by
    calc σ * (u * v * w) * σ⁻¹ = (σ * u * σ⁻¹) * (σ * v * σ⁻¹) * (σ * w * σ⁻¹) := by group
      _ = v * w * u := by rw [hσu, hσv, hσw]
      _ = u * (v * w) := (huv.mul_right huw).eq.symm
      _ = u * v * w := (mul_assoc u v w).symm
  have hsign : ∀ x : Perm α, Perm.sign (σ * x * σ⁻¹) = Perm.sign x := fun x => by
    rw [map_mul, map_mul, Perm.sign_inv, mul_comm (Perm.sign σ * Perm.sign x), ← mul_assoc,
      Int.units_mul_self, one_mul]
  refine ⟨u * v * w, ?_, ?_⟩
  · have hsu : Perm.sign u = -1 := Perm.sign_swap had'
    have hsv : Perm.sign v = Perm.sign u := hsign u
    have hsw : Perm.sign w = Perm.sign v := hsign v
    rw [map_mul, map_mul, hsw, hsv, hsu]
    decide
  · show u * v * w * σ = σ * (u * v * w)
    calc u * v * w * σ = (σ * (u * v * w) * σ⁻¹) * σ := by rw [key]
      _ = σ * (u * v * w) := by group

theorem exists_not_sameCycle_of_two_le_card_cycleType {σ : Perm α}
    (h : 2 ≤ Multiset.card σ.cycleType) :
    ∃ a d, σ a ≠ a ∧ σ d ≠ d ∧ ¬ σ.SameCycle a d := by
  by_contra hcon
  push Not at hcon
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1] at h
    simp at h
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hh
    push Not at hh
    exact hσ1 (Equiv.ext hh)
  have hcyc : σ.IsCycle := by
    rw [isCycle_iff_sameCycle ha]
    intro y
    constructor
    · intro hy hy'
      exact ha ((hy.apply_eq_self_iff).mpr hy')
    · intro hy
      exact hcon a y ha hy
  have := Perm.card_cycleType_eq_one.mpr hcyc
  omega

theorem exists_odd_commute_of_cycleType_eq_three (hα : 5 ≤ Fintype.card α) {σ : Perm α}
    (hσ : σ.cycleType = {3}) : ∃ ρ : Perm α, Perm.sign ρ = -1 ∧ Commute ρ σ := by
  have hsupp : #σ.support = 3 := by
    rw [← Perm.sum_cycleType, hσ]
    simp
  have hcard : 1 < #(σ.supportᶜ) := by
    rw [Finset.card_compl, hsupp]
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
  have hsa : σ a = a := by simpa using ha
  have hsb : σ b = b := by simpa using hb
  refine ⟨swap a b, Perm.sign_swap hab, ?_⟩
  have hdisj : Disjoint (swap a b) σ := by
    intro x
    by_cases hx : σ x = x
    · exact Or.inr hx
    · left
      refine swap_apply_of_ne_of_ne ?_ ?_
      · rintro rfl
        exact hx hsa
      · rintro rfl
        exact hx hsb
  exact hdisj.commute

end AltConj

section Alternating

variable {n : ℕ}

theorem isConj_alternatingGroup_of_cycleType_eq_three (hn : 5 ≤ n)
    {σ τ : alternatingGroup (Fin n)} (hσ : (σ : Perm (Fin n)).cycleType = {3})
    (hτ : (τ : Perm (Fin n)).cycleType = {3}) : IsConj σ τ := by
  obtain ⟨ρ, hρ, hc⟩ := AltConj.exists_odd_commute_of_cycleType_eq_three
    (by rwa [Fintype.card_fin]) hσ
  exact AltConj.isConj_alternatingGroup_of_odd_commute (hσ.trans hτ.symm) hρ hc

theorem isConj_alternatingGroup_of_cycleType_eq_three_three {σ τ : alternatingGroup (Fin n)}
    (hσ : (σ : Perm (Fin n)).cycleType = {3, 3}) (hτ : (τ : Perm (Fin n)).cycleType = {3, 3}) :
    IsConj σ τ := by
  have h3 : (σ : Perm (Fin n)) ^ 3 = 1 := Perm.pow_prime_eq_one_iff.mpr (fun c hc => by
    rw [hσ] at hc
    simpa using hc)
  obtain ⟨a, d, ha, hd, had⟩ := AltConj.exists_not_sameCycle_of_two_le_card_cycleType
    (σ := (σ : Perm (Fin n))) (by rw [hσ]; simp)
  obtain ⟨ρ, hρ, hc⟩ := AltConj.exists_odd_commute_of_pow_three_eq_one h3 ha hd had
  exact AltConj.isConj_alternatingGroup_of_odd_commute (hσ.trans hτ.symm) hρ hc

theorem isConj_alternatingGroup_of_cycleType_eq_three_three_three {σ τ : alternatingGroup (Fin n)}
    (hσ : (σ : Perm (Fin n)).cycleType = {3, 3, 3})
    (hτ : (τ : Perm (Fin n)).cycleType = {3, 3, 3}) : IsConj σ τ := by
  have h3 : (σ : Perm (Fin n)) ^ 3 = 1 := Perm.pow_prime_eq_one_iff.mpr (fun c hc => by
    rw [hσ] at hc
    simpa using hc)
  obtain ⟨a, d, ha, hd, had⟩ := AltConj.exists_not_sameCycle_of_two_le_card_cycleType
    (σ := (σ : Perm (Fin n))) (by rw [hσ]; simp)
  obtain ⟨ρ, hρ, hc⟩ := AltConj.exists_odd_commute_of_pow_three_eq_one h3 ha hd had
  exact AltConj.isConj_alternatingGroup_of_odd_commute (hσ.trans hτ.symm) hρ hc

theorem isConj_alternatingGroup_of_cycleType_eq_two_two {σ τ : alternatingGroup (Fin n)}
    (hσ : (σ : Perm (Fin n)).cycleType = {2, 2}) (hτ : (τ : Perm (Fin n)).cycleType = {2, 2}) :
    IsConj σ τ := by
  have hsq : (σ : Perm (Fin n)) ^ 2 = 1 := Perm.pow_prime_eq_one_iff.mpr (fun c hc => by
    rw [hσ] at hc
    simpa using hc)
  have hne : (σ : Perm (Fin n)) ≠ 1 := by
    intro h
    rw [h, Perm.cycleType_one] at hσ
    simp at hσ
  obtain ⟨ρ, hρ, hc⟩ := AltConj.exists_odd_commute_of_sq_eq_one hsq hne
  exact AltConj.isConj_alternatingGroup_of_odd_commute (hσ.trans hτ.symm) hρ hc

theorem isConj_alternatingGroup_of_cycleType_eq_two_two_two_two {σ τ : alternatingGroup (Fin n)}
    (hσ : (σ : Perm (Fin n)).cycleType = {2, 2, 2, 2})
    (hτ : (τ : Perm (Fin n)).cycleType = {2, 2, 2, 2}) : IsConj σ τ := by
  have hsq : (σ : Perm (Fin n)) ^ 2 = 1 := Perm.pow_prime_eq_one_iff.mpr (fun c hc => by
    rw [hσ] at hc
    simpa using hc)
  have hne : (σ : Perm (Fin n)) ≠ 1 := by
    intro h
    rw [h, Perm.cycleType_one] at hσ
    simp at hσ
  obtain ⟨ρ, hρ, hc⟩ := AltConj.exists_odd_commute_of_sq_eq_one hsq hne
  exact AltConj.isConj_alternatingGroup_of_odd_commute (hσ.trans hτ.symm) hρ hc

theorem isConj_alternatingGroup_of_cycleType_eq (hn : 5 ≤ n) {σ τ : alternatingGroup (Fin n)}
    {c : Multiset ℕ} (hc : c = {3} ∨ c = {3, 3} ∨ c = {3, 3, 3} ∨ c = {2, 2} ∨ c = {2, 2, 2, 2})
    (hσ : (σ : Perm (Fin n)).cycleType = c) (hτ : (τ : Perm (Fin n)).cycleType = c) :
    IsConj σ τ := by
  subst hσ
  rcases hc with hc | hc | hc | hc | hc
  · exact isConj_alternatingGroup_of_cycleType_eq_three hn hc (hτ.trans hc)
  · exact isConj_alternatingGroup_of_cycleType_eq_three_three hc (hτ.trans hc)
  · exact isConj_alternatingGroup_of_cycleType_eq_three_three_three hc (hτ.trans hc)
  · exact isConj_alternatingGroup_of_cycleType_eq_two_two hc (hτ.trans hc)
  · exact isConj_alternatingGroup_of_cycleType_eq_two_two_two_two hc (hτ.trans hc)

end Alternating

theorem commute_iff_sq_mul_eq_one {G : Type*} [Group G] {u v : G} (hu : u ^ 2 = 1)
    (hv : v ^ 2 = 1) : Commute u v ↔ (u * v) ^ 2 = 1 := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq, hu])
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq, hv])
  have hc : u * v * u⁻¹ * v⁻¹ = (u * v) ^ 2 := by rw [hui, hvi, sq]; group
  rw [← hc]
  constructor
  · intro h
    rw [h.eq]
    group
  · intro h
    have h1 : u * v * u⁻¹ = v := mul_inv_eq_one.mp h
    exact mul_inv_eq_iff_eq_mul.mp h1

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

namespace TwoCover

theorem exists_conj_mul_ker_of_isConj (hπ : TwoCover π) {u v : H}
    (h : IsConj (π u) (π v)) : ∃ g : H, ∃ k ∈ π.ker, g * u * g⁻¹ = v * k := by
  obtain ⟨h', hh⟩ := isConj_iff.mp h
  obtain ⟨g, rfl⟩ := hπ.surj h'
  refine ⟨g, v⁻¹ * (g * u * g⁻¹), ?_, (mul_inv_cancel_left v _).symm⟩
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hh, inv_mul_cancel]

theorem sq_eq_of_isConj (hπ : TwoCover π) {u v : H} (h : IsConj (π u) (π v))
    (hv : v ^ 2 ∈ π.ker) : u ^ 2 = v ^ 2 := by
  obtain ⟨g, k, hk, hg⟩ := hπ.exists_conj_mul_ker_of_isConj h
  have hkc : Commute v k := Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) v
  have h2 : g * u ^ 2 * g⁻¹ = v ^ 2 := by
    rw [← conj_pow, hg, hkc.mul_pow, hπ.sq_eq_one_of_mem_ker' hk, mul_one]
  calc u ^ 2 = g⁻¹ * (g * u ^ 2 * g⁻¹) * g := by group
    _ = g⁻¹ * v ^ 2 * g := by rw [h2]
    _ = v ^ 2 := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp (hπ.ker_le_center hv) g, inv_mul_cancel_left]

theorem exists_conj_mul_ker_of_cycleType_eq (hπ : TwoCover π) (hn : 5 ≤ n) {c : Multiset ℕ}
    (hc : c = {3} ∨ c = {3, 3} ∨ c = {3, 3, 3} ∨ c = {2, 2} ∨ c = {2, 2, 2, 2}) {u v : H}
    (hu : ((π u : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = c)
    (hv : ((π v : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = c) :
    ∃ g : H, ∃ k ∈ π.ker, g * u * g⁻¹ = v * k :=
  hπ.exists_conj_mul_ker_of_isConj (isConj_alternatingGroup_of_cycleType_eq hn hc hu hv)

theorem commute_iff_sq_mul_eq_one (_hπ : TwoCover π) {u v : H} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (_h : Commute (π u) (π v)) : Commute u v ↔ (u * v) ^ 2 = 1 :=
  CFSG.GH74.Uniqueness.SU.SU13.TA.commute_iff_sq_mul_eq_one hu hv

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
