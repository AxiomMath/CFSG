module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution

public section

open scoped Pointwise commutatorElement

namespace CFSG.Wreathed

open CFSG.Semidihedral.Principal.PrimewiseScalar CFSG.OddInversion

variable {K : Type*} [Group K] [Finite K]

theorem commuting_normal_factors_control_odd_inverted_subgroups (J R : Subgroup K) [J.Normal]
    [hR : R.Normal] (hJR : ⁅J, R⁆ = ⊥) (hRsolv : Group.IsSolvable R) (hRodd : Odd (Nat.card R))
    (hidx : ∃ k : ℕ, (J ⊔ R).index = 2 ^ k) (a : K) (ha : orderOf a = 2)
    (hsyl : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card R → ∃ P : Subgroup K, IsSylowOf R ℓ P ∧
      (∀ x ∈ P, a * x * a⁻¹ ∈ P) ∧ ((∀ x ∈ P, a * x * a⁻¹ = x) ∨ (∀ x ∈ P, a * x * a⁻¹ = x⁻¹))) :
    ∃ B : Subgroup K, (B : Set K) = invertedSet R a ∧ B ≤ R ∧ IsMulCommutative B ∧
      (B.subgroupOf R).Characteristic ∧ Nat.Coprime (Nat.card B) (B.relIndex R) ∧
      (B.subgroupOf R).Normal ∧ B ⊔ (R ⊓ Subgroup.centralizer ({a} : Set K)) = R ∧
      B ⊓ (R ⊓ Subgroup.centralizer ({a} : Set K)) = ⊥ ∧ B.Normal ∧
      ∀ E : Subgroup K, Odd (Nat.card E) → (∀ x ∈ E, a * x * a⁻¹ = x⁻¹) →
        E ≤ J ⊔ B ∧ B ≤ Subgroup.centralizer (E : Set K) := by
  classical
  have haN : a ∈ Subgroup.normalizer (R : Set K) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨⟨hi, -⟩, ⟨hii, -⟩, -⟩ :=
    solvable_odd_primewise_scalar_involution_has_characteristic_inverted_complement R hRsolv
      hRodd a haN ha
  obtain ⟨V, hVU, -, hVR, hcomm, hchar, hVhall, hVn, hVA, hVA', -⟩ := hii (hi hsyl)
  have hVnK : V.Normal := ⟨fun b hb g => by
    have hmem : (⟨b, hVR hb⟩ : R) ∈ V.subgroupOf R := hb
    have := (Subgroup.characteristic_iff_map_le.mp hchar) (MulAut.conjNormal g) ⟨_, hmem, rfl⟩
    simpa [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply] using this⟩
  have hVinv : ∀ b ∈ V, a * b * a⁻¹ = b⁻¹ := fun b hb => by
    have : b ∈ invertedSet R a := hVU ▸ hb
    exact this.2
  have hAfix : ∀ c ∈ R ⊓ Subgroup.centralizer ({a} : Set K), a * c * a⁻¹ = c := fun c hc => by
    have : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    rw [← this, mul_inv_cancel_right]
  have hRV : ∀ r ∈ R, r⁻¹ * (a * r * a⁻¹) ∈ V := by
    intro r hr
    have hr' : r ∈ ((R ⊓ Subgroup.centralizer ({a} : Set K) ⊔ V : Subgroup K) : Set K) := by
      rw [sup_comm, hVA]
      exact hr
    rw [Subgroup.mul_normal] at hr'
    obtain ⟨c, hc, b, hb, rfl⟩ := hr'
    have e1 : (c * b)⁻¹ * (a * (c * b) * a⁻¹) =
        b⁻¹ * c⁻¹ * ((a * c * a⁻¹) * (a * b * a⁻¹)) := by group
    rw [e1, hAfix c hc, hVinv b hb]
    have e2 : b⁻¹ * c⁻¹ * (c * b⁻¹) = b⁻¹ * b⁻¹ := by group
    rw [e2]
    exact V.mul_mem (V.inv_mem hb) (V.inv_mem hb)
  refine ⟨V, hVU, hVR, hcomm, hchar, hVhall, hVn, hVA, hVA', hVnK, fun E hEodd hEinv => ?_⟩
  have hEJR : ∀ x ∈ E, x ∈ J ⊔ R := by
    intro x hx
    obtain ⟨k, hk⟩ := hidx
    rw [← QuotientGroup.eq_one_iff]
    have h1 : orderOf (x : K ⧸ (J ⊔ R)) ∣ 2 ^ k := by
      rw [← hk, Subgroup.index]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (x : K ⧸ (J ⊔ R)) ∣ Nat.card E :=
      (orderOf_map_dvd (QuotientGroup.mk' (J ⊔ R)) x).trans (E.orderOf_dvd_natCard hx)
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases i with _ | i
    · rwa [pow_zero, orderOf_eq_one_iff] at hi'
    · exfalso
      have hodd : Odd (orderOf (x : K ⧸ (J ⊔ R))) := Odd.of_dvd_nat hEodd h2
      rw [hi', pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) ⟨2 ^ i, by ring⟩
  have hEJV : E ≤ J ⊔ V := by
    intro x hx
    have hxJR : x ∈ ((J ⊔ R : Subgroup K) : Set K) := hEJR x hx
    rw [Subgroup.normal_mul] at hxJR
    obtain ⟨j, hj, r, hr, rfl⟩ := hxJR
    rw [← QuotientGroup.eq_one_iff]
    have hjQ : ((j : K) : K ⧸ (J ⊔ V)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left hj)
    have hajQ : ((a * j * a⁻¹ : K) : K ⧸ (J ⊔ V)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem ‹_› j hj a))
    have harQ : ((a * r * a⁻¹ : K) : K ⧸ (J ⊔ V)) = (r : K ⧸ (J ⊔ V)) := by
      rw [eq_comm, QuotientGroup.eq]
      exact Subgroup.mem_sup_right (hRV r hr)
    have hxQ : ((j * r : K) : K ⧸ (J ⊔ V)) = (r : K ⧸ (J ⊔ V)) := by
      rw [QuotientGroup.mk_mul, hjQ, one_mul]
    have hinvQ : ((j * r : K) : K ⧸ (J ⊔ V))⁻¹ = ((j * r : K) : K ⧸ (J ⊔ V)) := by
      rw [← QuotientGroup.mk_inv, ← hEinv _ hx,
        show a * (j * r) * a⁻¹ = (a * j * a⁻¹) * (a * r * a⁻¹) by group, QuotientGroup.mk_mul,
        hajQ, one_mul, harQ, hxQ]
    have hsq : ((j * r : K) : K ⧸ (J ⊔ V)) ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← hinvQ]
      exact inv_mul_cancel _
    have h1 : orderOf ((j * r : K) : K ⧸ (J ⊔ V)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h2 : orderOf ((j * r : K) : K ⧸ (J ⊔ V)) ∣ Nat.card E :=
      (orderOf_map_dvd (QuotientGroup.mk' (J ⊔ V)) (j * r)).trans (E.orderOf_dvd_natCard hx)
    have hodd : Odd (orderOf ((j * r : K) : K ⧸ (J ⊔ V))) := Odd.of_dvd_nat hEodd h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · rwa [orderOf_eq_one_iff] at h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  refine ⟨hEJV, fun b hb => Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  have heJV : e ∈ ((J ⊔ V : Subgroup K) : Set K) := hEJV he
  rw [Subgroup.normal_mul] at heJV
  obtain ⟨j, hj, b', hb', rfl⟩ := heJV
  have hjb : b * j = j * b :=
    Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJR) hj)
      b (hVR hb)
  have hbb' : b * b' = b' * b := by
    have := (hcomm.is_comm).comm ⟨b, hb⟩ ⟨b', hb'⟩
    exact congrArg Subtype.val this
  rw [mul_assoc, ← hbb', ← mul_assoc, ← hjb, mul_assoc]

end CFSG.Wreathed
