module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator

theorem twentySeven_dvd_ordTwistedE6 (q : ℕ) (hq : 1 ≤ q) : 27 ∣ CFSG.Open.ordTwistedE6 q := by
  have h81 : 81 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    generalize (q : ZMod 81) = x
    revert x
    decide +kernel
  have hnum : 81 ∣ CFSG.Open.ordTwistedE6 q * Nat.gcd 3 (q + 1) := by
    rw [CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd]
    exact h81
  have h3 : 81 ∣ CFSG.Open.ordTwistedE6 q * 3 :=
    hnum.trans (mul_dvd_mul_left _ (Nat.gcd_dvd_left 3 _))
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3)
    (by rwa [show (27 : ℕ) * 3 = 81 by norm_num])

theorem exists_pow_ne_self {ℓ n N : ℕ} (hℓ : ℓ.Prime) (hn0 : 0 < n) (hn : n < N) (K : Type)
    [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ N) : ∃ c : K, c ^ ℓ ^ n ≠ c := by
  classical
  by_contra hall
  push Not at hall
  have hN1 : 1 < ℓ ^ n := Nat.one_lt_pow hn0.ne' hℓ.one_lt
  set P : Polynomial K := Polynomial.X ^ ℓ ^ n - Polynomial.X with hPdef
  have hdeg : P.natDegree = ℓ ^ n := by
    rw [hPdef, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [hN1]
  have hP0 : P ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have : Fintype K := Fintype.ofFinite K
  have hroots : (Finset.univ : Finset K).val ≤ P.roots :=
    (Multiset.le_iff_subset Finset.univ.nodup).2 fun c _ => by
      rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, hPdef]
      simp [hall c]
  have hle : Nat.card K ≤ ℓ ^ n := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
    exact (Multiset.card_le_card hroots).trans (Polynomial.card_roots' P)
  rw [hK] at hle
  exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hℓ.one_lt hn))

theorem twentySeven_dvd_card_fixedSubgroup_fieldActor {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * (d * p))) (σ ε : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p))
    (hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1))) :
    27 ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2dp : 1 ≤ 2 * (d * p) := by have := Nat.mul_pos hd hp.pos; omega
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ h2dp hK
  obtain ⟨S, hS⟩ := exists_subfield_card_of_card_eq hℓ hd hp.pos K hK
  have : Finite S := Subtype.finite
  have : CharP S ℓ := inferInstance
  have hS2 : Nat.card S = (ℓ ^ d) ^ 2 := by rw [hS, ← pow_mul, mul_comm]
  have hpowS : ∀ c : S, ∀ k : ℕ, (c : K) ^ ((ℓ ^ (2 * d)) ^ k) = c := by
    intro c k
    have : Fintype S := Fintype.ofFinite S
    have h1 : c ^ (ℓ ^ (2 * d)) = c := by
      have h := FiniteField.pow_card c
      rwa [← Nat.card_eq_fintype_card, hS] at h
    induction k with
    | zero => simp
    | succ k ih =>
      have h2 : (c : K) ^ (ℓ ^ (2 * d)) = c := congrArg Subtype.val h1
      rw [pow_succ, pow_mul, ih, h2]
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hεS : ∀ c : S, ε c = c := fun c => by
    rw [hε, show d * (p + 1) = 2 * d * (m + 1) by rw [hm]; ring, pow_mul, hpowS]
  have hσS : ∀ c : S, σ c = (c : K) ^ ℓ ^ d := fun c => by
    rw [hσ, show d * p = 2 * d * m + d by rw [hm]; ring, pow_add, pow_mul, pow_mul, hpowS]
  set σ₀ : S →+* S := iterateFrobenius S ℓ d with hσ₀def
  have hσ₀ : ∀ c, σ₀ c = c ^ ℓ ^ d := fun c => by rw [hσ₀def, iterateFrobenius_def]
  have hσ₀surj : Function.Surjective σ₀ := Finite.surjective_of_injective σ₀.injective
  have hcomm : ∀ c, σ.toRingHom (S.subtype c) = S.subtype (σ₀ c) := fun c => by
    change σ c = ((σ₀ c : S) : K)
    rw [hσS, hσ₀]
    rfl
  have hle := map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (ι := S.subtype)
    hσ₀surj hcomm
  set H := ((graphFixedRootGroup TwistTag.E6 S σ₀).map (baseChangeGL S.subtype)).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) with hHdef
  have hει : ε.toRingHom.comp S.subtype = S.subtype := RingHom.ext fun c => hεS c
  have hHfix : H ≤ fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε) := by
    intro x hx
    obtain ⟨y, -, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
    refine Subtype.ext ?_
    change Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x
    rw [units_map_entrywiseHom_eq_baseChangeGL, ← hyx, baseChangeGL_baseChangeGL, hει]
  have hcardH : Nat.card H = CFSG.Open.ordTwistedE6 (ℓ ^ d) := by
    rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective (baseChangeGL_injective _),
      CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hd hS2 σ₀ hσ₀]
  refine (dvd_trans ?_ (Subgroup.card_dvd_of_le hHfix))
  rw [hcardH]
  exact twentySeven_dvd_ordTwistedE6 _ (Nat.one_le_pow _ _ hℓ.pos)

theorem twentySeven_dvd_fixedSubgroup_twistedE6_of_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1)
    (hnd : β ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    27 ∣ Nat.card (fixedSubgroup β) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hη1 : Θ β ≠ 1 := fun h1 => hnd (by rw [← hker, MonoidHom.mem_ker]; exact h1)
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd0, r, ε, hε, ψ, hψ⟩ :=
    twisted_E6_field_descent_of_prime_order hℓ hf K hK2 σ hσ Θ hΘ Nat.prime_three
      (by norm_num) β hβ3 hη1
  have hε1 : ε ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := exists_pow_ne_self hℓ (n := d * (3 + 1)) (N := 2 * f) (by omega) (by omega)
      K hK2
    exact hc (by rw [← hε, h1]; rfl)
  have hβr : β ^ r ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hψ
    apply hε1
    have h := hΘ (fieldActor σ ε) 1 1 ε (by rw [map_one, map_one, one_mul, one_mul])
    rw [← hψ, map_one] at h
    exact h.symm
  have hβord : orderOf β = 3 :=
    orderOf_eq_prime hβ3 fun h => hnd (h ▸ Subgroup.one_mem _)
  have hr3 : ¬ 3 ∣ r := by
    rintro ⟨t, rfl⟩
    exact hβr (by rw [pow_mul, hβ3, one_pow])
  obtain ⟨s, hs⟩ := exists_mul_mod_eq_one Nat.prime_three
    (Nat.pos_of_ne_zero fun h => hr3 (Nat.dvd_of_mod_eq_zero h)) (Nat.mod_lt r (by norm_num))
  have hrs : r * s % 3 = s * (r % 3) % 3 := by
    rw [Nat.mul_mod r s, Nat.mul_mod s (r % 3), Nat.mod_mod, mul_comm (r % 3)]
  have hpow : (β ^ r) ^ s = β := by
    rw [← pow_mul]
    exact pow_eq_self_of_mod_eq_one hβord (hrs.trans hs)
  rw [CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_pow_eq hpow]
  have hconj : Nat.card (fixedSubgroup (β ^ r)) =
      Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    card_fixedSubgroup_eq_of_intertwine (ψ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
      (β ^ r) _ fun x => by
        have h := congrArg (fun g : MulAut (twistedE6RootGroup K σ) => g (ψ x)) hψ
        simpa [MulAut.mul_apply] using h.symm
  rw [hconj]
  have hK' : Nat.card K = ℓ ^ (2 * (d * 3)) := by rw [hK2, hd, mul_comm 3 d]
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ, hd, mul_comm 3 d]
  exact twentySeven_dvd_card_fixedSubgroup_fieldActor hℓ hd0 Nat.prime_three (by norm_num) K hK'
    σ ε hσ' hε

theorem twentySeven_dvd_fixedSubgroup_twistedE6_of_not_dvd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq : ¬ 3 ∣ ℓ ^ f + 1) (β : MulAut (twistedE6RootGroup K σ))
    (hβ3 : β ^ 3 = 1) (hβ : β ∉ twistedE6Inn K σ) :
    27 ∣ Nat.card (fixedSubgroup β) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  refine twentySeven_dvd_fixedSubgroup_twistedE6_of_field hℓ hf K hK σ hσ β hβ3 fun hmem => hβ ?_
  exact mem_inner_of_mem_inn_sup_diag Nat.prime_three hK hσ
    (fun h => hq (h.trans (Nat.gcd_dvd_right 3 _))) hcube hβ3 hmem

@[expose] def TwistedE6InnerDiagLowerBound : Prop :=
  ∀ {ℓ f : ℕ}, ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) → 3 ∣ ℓ ^ f + 1 →
    ∀ β : MulAut (twistedE6RootGroup K σ), β ^ 3 = 1 →
      β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ → β ∉ twistedE6Inn K σ →
        27 ∣ Nat.card (fixedSubgroup β)

theorem twentySeven_dvd_fixedSubgroup_twistedE6_of_innerDiag
    (hdiag : TwistedE6InnerDiagLowerBound) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1)
    (hβ : β ∉ twistedE6Inn K σ) :
    27 ∣ Nat.card (fixedSubgroup β) := by
  by_cases hmem : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  · by_cases hq : 3 ∣ ℓ ^ f + 1
    · exact hdiag hℓ hf K hK σ hσ hq β hβ3 hmem hβ
    · exact twentySeven_dvd_fixedSubgroup_twistedE6_of_not_dvd hℓ hf K hK σ hσ hq β hβ3 hβ
  · exact twentySeven_dvd_fixedSubgroup_twistedE6_of_field hℓ hf K hK σ hσ β hβ3 hmem

end CFSG.HardMathSupport.Lang.E27
