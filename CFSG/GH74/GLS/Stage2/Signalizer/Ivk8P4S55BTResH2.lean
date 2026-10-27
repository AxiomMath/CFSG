module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltHH

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem eq_zpowers_of_pgroup {p : ℕ} (hp : p = 5 ∨ p = 7) {X : Subgroup (Perm (Fin 7))}
    (hX : IsPGroup p ↥X) {σ : Perm (Fin 7)} (hσX : σ ∈ X) (hσ1 : σ ≠ 1) :
    orderOf σ = p ∧ X = zpowers σ := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hX
  have hdvd : p ^ k ∣ 5040 := by
    have h7 : Nat.card (Perm (Fin 7)) = 5040 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [← hk, ← h7]
    exact Subgroup.card_subgroup_dvd_card X
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have : p ^ 2 ∣ 5040 := (pow_dvd_pow p hk2).trans hdvd
    rcases hp with rfl | rfl <;> norm_num at this
  have hσo : orderOf σ ∣ p ^ k := hk ▸ Subgroup.orderOf_dvd_natCard X hσX
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.dvd_one, orderOf_eq_one_iff] at hσo
    exact hσ1 hσo
  obtain rfl : k = 1 := by omega
  rw [pow_one] at hσo hk
  have hσp : orderOf σ = p := by
    rcases (Nat.dvd_prime hpp).mp hσo with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ1
    · exact h
  refine ⟨hσp, (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hσX) ?_).symm⟩
  rw [hk, Nat.card_zpowers, hσp]

theorem exists_commute_perm {p : ℕ} (hp : p = 5 ∨ p = 7) {X : Subgroup (Perm (Fin 7))}
    (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) {D : Subgroup (Perm (Fin 7))} (hD2 : ∀ d ∈ D, d * d = 1)
    (hD4 : Nat.card D = 4) (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) :
    ∃ σ : Perm (Fin 7), orderOf σ = p ∧ ∃ d ∈ D, d ≠ 1 ∧ Commute d σ := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨⟨σ, hσX⟩, hσ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  obtain ⟨hσp, hXσ⟩ := eq_zpowers_of_pgroup hp hX hσX hσ1'
  obtain ⟨d, hd, hd1, hdc⟩ := exists_commute_of_four hpp (by rcases hp with rfl | rfl <;> decide)
    hσp hD2 hD4 (fun d hd => hXσ ▸ hDX d hd σ hσX)
  exact ⟨σ, hσp, d, hd, hd1, hdc⟩

theorem not_isSolvable_alternatingGroup_of_card {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : 5 ≤ Fintype.card α) : ¬ Group.IsSolvable (alternatingGroup α) := by
  intro h
  refine Equiv.Perm.not_isSolvable α ?_ (Group.isSolvable_of_ker_le_range
    (alternatingGroup α).subtype (Equiv.Perm.sign (α := α)) fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩)
  rw [Cardinal.mk_fintype]
  exact_mod_cast h5

variable {Y : Type} [Group Y]

theorem false_of_four_seven (e : Y ≃* alternatingGroup (Fin 7)) {X : Subgroup (MulAut Y)}
    (hX : IsPGroup 7 ↥X) (hX1 : X ≠ ⊥) {D : Subgroup (MulAut Y)} (hD2 : ∀ d ∈ D, d * d = 1)
    (hD4 : Nat.card D = 4) (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) : False := by
  set τ := autTransport (by norm_num : 5 ≤ 7) (by norm_num) e with hτ
  obtain ⟨σ, hσ, _, ⟨d, hd, rfl⟩, hd1, hdc⟩ := exists_commute_perm (Or.inr rfl)
    (X := X.map τ.toMonoidHom) (hX.map _)
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ τ.injective])
    (D := D.map τ.toMonoidHom)
    (by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, hD2 d hd, map_one])
    (by rw [Subgroup.card_map_of_injective τ.injective, hD4])
    (by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨x, hx, rfl⟩
      exact ⟨d * x * d⁻¹, hDX d hd x hx, by simp⟩)
  have hd2 : τ.toMonoidHom d * τ.toMonoidHom d = 1 := by rw [← map_mul, hD2 d hd, map_one]
  exact hd1 (eq_one_of_commute_seven hσ hd2 hdc)

theorem exists_swap_of_four_five (e : Y ≃* alternatingGroup (Fin 7)) {X : Subgroup (MulAut Y)}
    (hX : IsPGroup 5 ↥X) (hX1 : X ≠ ⊥) {D : Subgroup (MulAut Y)} (hD2 : ∀ d ∈ D, d * d = 1)
    (hD4 : Nat.card D = 4) (hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) :
    ∃ d ∈ D, d ≠ 1 ∧ (autTransport (by norm_num : 5 ≤ 7) (by norm_num) e d).IsSwap := by
  set τ := autTransport (by norm_num : 5 ≤ 7) (by norm_num) e with hτ
  obtain ⟨σ, hσ, _, ⟨d, hd, rfl⟩, hd1, hdc⟩ := exists_commute_perm (Or.inl rfl)
    (X := X.map τ.toMonoidHom) (hX.map _)
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ τ.injective])
    (D := D.map τ.toMonoidHom)
    (by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, hD2 d hd, map_one])
    (by rw [Subgroup.card_map_of_injective τ.injective, hD4])
    (by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨x, hx, rfl⟩
      exact ⟨d * x * d⁻¹, hDX d hd x hx, by simp⟩)
  have hd2 : τ.toMonoidHom d * τ.toMonoidHom d = 1 := by rw [← map_mul, hD2 d hd, map_one]
  refine ⟨d, hd, fun h => hd1 (by rw [h, map_one]), isSwap_of_commute_five hσ hd2 hd1 hdc⟩

theorem not_isSolvable_fixed_of_isSwap (e : Y ≃* alternatingGroup (Fin 7)) {d : MulAut Y}
    (hd : (autTransport (by norm_num : 5 ≤ 7) (by norm_num) e d).IsSwap) :
    ¬ Group.IsSolvable ↥(fixedSubgroup Y d) := by
  classical
  obtain ⟨u, v, huv, hτ⟩ := hd
  set s : Finset (Fin 7) := {u, v} with hs
  let ι : Perm {x // x ∈ sᶜ} →* Perm (Fin 7) := ofSubtype
  have hfix : ∀ π : Perm {x // x ∈ sᶜ}, ι π u = u ∧ ι π v = v := fun π =>
    ⟨ofSubtype_apply_of_not_mem π (by simp [hs]), ofSubtype_apply_of_not_mem π (by simp [hs])⟩
  have hcomm : ∀ π, swap u v * ι π * (swap u v)⁻¹ = ι π := by
    intro π
    have h1 : ι π * swap u v = swap u v * ι π := by
      rw [mul_swap_eq_swap_mul, (hfix π).1, (hfix π).2]
    rw [swap_inv, ← h1, mul_assoc, swap_mul_self, mul_one]
  have halt : ∀ π ∈ alternatingGroup {x // x ∈ sᶜ}, ι π ∈ alternatingGroup (Fin 7) := by
    intro π hπ
    rw [Perm.mem_alternatingGroup, sign_ofSubtype]
    exact hπ
  let φ : alternatingGroup {x // x ∈ sᶜ} →* ↥(fixedSubgroup Y d) :=
    { toFun := fun π => ⟨e.symm ⟨ι π, halt π π.2⟩, by
        show d (e.symm _) = e.symm _
        apply e.injective
        apply Subtype.ext
        rw [autTransport_apply (by norm_num) (by norm_num) e d, MulEquiv.apply_symm_apply, hτ]
        exact hcomm π⟩
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul, map_mul]
        rw [← map_mul e.symm]
        rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun y : ↥(fixedSubgroup Y d) => ((e (y : Y) : alternatingGroup (Fin 7)) :
      Perm (Fin 7))) hab
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.apply_symm_apply] at h1
    exact Subtype.ext (ofSubtype_injective h1)
  intro hsol
  apply not_isSolvable_alternatingGroup_of_card (α := {x // x ∈ sᶜ}) _
    (Group.isSolvable_of_isSolvable_injective hφ)
  rw [Fintype.card_coe, Finset.card_compl, Finset.card_pair huv, Fintype.card_fin]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResA7
