module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientDescent
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Generic

variable {G : Type*} [Group G]

@[expose] def fixedSubgroupConjEquiv (ψ β : MulAut G) :
    fixedSubgroup β ≃* fixedSubgroup (ψ * β * ψ⁻¹) where
  toFun x := ⟨ψ x, by
    have hx : β x = x := x.2
    change (ψ * β * ψ⁻¹) (ψ x) = ψ x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]⟩
  invFun y := ⟨ψ⁻¹ y, by
    have hy : (ψ * β * ψ⁻¹) y = y := y.2
    change β (ψ⁻¹ y) = ψ⁻¹ y
    have h1 : ψ (β (ψ⁻¹ y)) = y := hy
    have h2 : β (ψ⁻¹ y) = ψ⁻¹ (ψ (β (ψ⁻¹ y))) := (MulAut.inv_apply_self _ _ _).symm
    rw [h2, h1]⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self _ _ _)
  right_inv y := Subtype.ext (MulAut.apply_inv_self _ _ _)
  map_mul' x y := Subtype.ext (map_mul ψ _ _)

theorem card_fixedSubgroup_of_conj_eq_mul {ψ β γ : MulAut G} (h : ψ * β * ψ⁻¹ = γ) :
    Nat.card (fixedSubgroup γ) = Nat.card (fixedSubgroup β) := by
  subst h
  exact (Nat.card_congr (fixedSubgroupConjEquiv ψ β).toEquiv).symm

theorem fixedSubgroup_inv_eq (β : MulAut G) : fixedSubgroup β⁻¹ = fixedSubgroup β := by
  ext x
  change β⁻¹ x = x ↔ β x = x
  constructor
  · intro h
    have h1 : β (β⁻¹ x) = β x := congrArg (fun y => β y) h
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  · intro h
    have h1 : β⁻¹ (β x) = β⁻¹ x := congrArg (fun y => β⁻¹ y) h
    rw [MulAut.inv_apply_self] at h1
    exact h1.symm

end Generic


section TwistedFixed

variable (t : TwistTag) {K : Type} [Field K]

theorem coe_twistedEntrywiseAut_one (σ : K ≃+* K) (u : adjointGroup t.tag K) :
    (twistedEntrywiseAut t 1 σ u : ModGL t.tag K) = twistHom t K σ.toRingHom u := by
  rw [coe_twistedEntrywiseAut, twistHom_apply, zpow_one]

theorem fixedSubgroup_twistedEntrywiseAut_one (σ : K ≃+* K) :
    fixedSubgroup (twistedEntrywiseAut t 1 σ) =
      (twistedFixedGroup t K σ.toRingHom).subgroupOf (adjointGroup t.tag K) := by
  ext u
  rw [Subgroup.mem_subgroupOf, coe_mem_twistedFixedGroup_iff]
  change twistedEntrywiseAut t 1 σ u = u ↔ twistC t K σ.toRingHom u = u
  constructor
  · intro h
    exact Subtype.ext (by rw [coe_twistC, ← coe_twistedEntrywiseAut_one, h])
  · intro h
    exact Subtype.ext (by rw [coe_twistedEntrywiseAut_one, ← coe_twistC, h])

@[expose] def fixedSubgroupTwistedEntrywiseAutOneEquiv (σ : K ≃+* K) :
    fixedSubgroup (twistedEntrywiseAut t 1 σ) ≃* twistedFixedGroup t K σ.toRingHom :=
  (MulEquiv.subgroupCongr (fixedSubgroup_twistedEntrywiseAut_one t σ)).trans
    (Subgroup.subgroupOfEquivOfLe (twistedFixedGroup_le_adjointGroup t K σ.toRingHom))

theorem card_fixedSubgroup_twistedEntrywiseAut_one (σ : K ≃+* K) :
    Nat.card (fixedSubgroup (twistedEntrywiseAut t 1 σ)) =
      Nat.card (twistedFixedGroup t K σ.toRingHom) :=
  Nat.card_congr (fixedSubgroupTwistedEntrywiseAutOneEquiv t σ).toEquiv

theorem diagramConjAut_pow_order : diagramConjAut t K ^ t.order = 1 := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  have h := coe_diagramConjAut_zpow t K (t.order : ℤ) u
  rw [zpow_natCast, zpow_natCast, diagramMap_pow_order] at h
  rw [h, MulAut.one_apply]
  group

theorem diagramConjAut_zpow_add_mul_order (j k : ℤ) :
    diagramConjAut t K ^ (j + k * t.order) = diagramConjAut t K ^ j := by
  rw [zpow_add, mul_comm k, zpow_mul, zpow_natCast, diagramConjAut_pow_order, one_zpow, mul_one]

theorem twistedEntrywiseAut_inv (j : ℤ) (σ : K ≃+* K) :
    (twistedEntrywiseAut t j σ)⁻¹ = twistedEntrywiseAut t (-j) σ⁻¹ := by
  have hc := (diagramConjAut_zpow_comm t j σ).inv_inv
  have hE : (entrywiseAdjointAut t.tag σ)⁻¹ = entrywiseAdjointAut t.tag σ⁻¹ :=
    (map_inv (entrywiseAdjointAutHom (τ := t.tag)) σ).symm
  unfold twistedEntrywiseAut
  rw [mul_inv_rev, ← hc.eq, ← zpow_neg, hE]

theorem twistedEntrywiseAut_add_mul_order (j k : ℤ) (σ : K ≃+* K) :
    twistedEntrywiseAut t (j + k * t.order) σ = twistedEntrywiseAut t j σ := by
  unfold twistedEntrywiseAut
  rw [diagramConjAut_zpow_add_mul_order]

theorem fixedSubgroup_twistedEntrywiseAut_D4_two (σ : K ≃+* K) :
    fixedSubgroup (twistedEntrywiseAut TwistTag.D4 2 σ) =
      fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ⁻¹) := by
  rw [← fixedSubgroup_inv_eq, twistedEntrywiseAut_inv]
  have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-2) 1 σ⁻¹
  rw [show (-2 : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 1 by decide] at h
  rw [h]

end TwistedFixed

section Order

theorem twentySeven_dvd_trialityD4_order {q : ℕ} (hq : ¬ 3 ∣ q) :
    27 ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact hq (dvd_zero 3))
  have hq2 : q ^ 2 ≡ 1 [MOD 3] := by
    have h : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h with h | h <;> simp [Nat.ModEq, Nat.pow_mod, h]
  have h1 : 3 ∣ q ^ 2 - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq0)).1 hq2.symm
  have h2 : 3 ∣ q ^ 6 - 1 := by
    have : q ^ 6 ≡ 1 [MOD 3] := by
      have := hq2.pow 3
      simpa [← pow_mul] using this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq0)).1 this.symm
  have h3 : 3 ∣ q ^ 8 + q ^ 4 + 1 := by
    have h8 : q ^ 8 ≡ 1 [MOD 3] := by simpa [← pow_mul] using hq2.pow 4
    have h4 : q ^ 4 ≡ 1 [MOD 3] := by simpa [← pow_mul] using hq2.pow 2
    have := (h8.add h4).add (Nat.ModEq.refl 1)
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (by decide))
  have h27 : 27 ∣ (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    have := mul_dvd_mul (mul_dvd_mul h1 h2) h3
    simpa using this
  have : q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) =
      q ^ 12 * ((q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) := by ring
  rw [this]
  exact h27.mul_left _

theorem order_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    (ℓ ^ f) ^ 12 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) ∣
      Nat.card (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j σ)) := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ f) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rcases hj with rfl | rfl
  · rw [card_fixedSubgroup_twistedEntrywiseAut_one]
    obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1
      (Or.inl rfl) σ.toRingHom (fun c => by simpa using hσ c)
    rw [← hC]
    exact Subgroup.card_dvd_of_le (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom)
  · rw [fixedSubgroup_twistedEntrywiseAut_D4_two, card_fixedSubgroup_twistedEntrywiseAut_one]
    have hσ3 : σ ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      change σ (σ (σ c)) = c
      rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring,
        hq3]
    have hinv : ∀ c, (σ⁻¹) c = c ^ ((ℓ ^ f) ^ 2) := by
      have h1 : σ⁻¹ = σ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hσ3)
      intro c
      rw [h1, pow_two]
      change σ (σ c) = _
      rw [hσ, hσ, ← pow_mul, sq]
    obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 2
      (Or.inr rfl) (σ⁻¹).toRingHom (fun c => hinv c)
    rw [← hC]
    exact Subgroup.card_dvd_of_le (graphFixedRootGroup_le TwistTag.D4 K (σ⁻¹).toRingHom)

theorem twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (h3 : ¬ 3 ∣ ℓ ^ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    27 ∣ Nat.card (fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j σ)) :=
  (twentySeven_dvd_trialityD4_order h3).trans
    (order_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 hℓ hf K hK σ hσ j hj)

end Order

end CFSG.HardMathSupport.Lang.E6Descent
