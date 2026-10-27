module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Transport
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (matrixLinearEquiv_scalar)

section ThreeDvd

variable {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}

theorem three_dvd_card_of_perm {Q₀ : QuadraticForm k (Fin d → k)}
    (hnd : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hT : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (π : Equiv.Perm (Fin d)) (hπ3 : ∀ y, π (π (π y)) = y) (hπ1 : ∃ y, π y ≠ y)
    (hπQ : ∀ v : Fin d → k, Q₀ (v ∘ π) = Q₀ v) :
    3 ∣ Nat.card (matrixProjectiveDerived Q₀) := by
  classical
  let L : (Fin d → k) ≃ₗ[k] (Fin d → k) := LinearEquiv.funCongrLeft k k π
  let x : GL (Fin d) k := matrixLinearIso.symm L
  have hxL : matrixLinearIso x = L := MulEquiv.apply_symm_apply _ _
  have hLv : ∀ v, L v = v ∘ π := fun v => rfl
  have hx : x ∈ matrixIsometries Q₀ := by
    rw [mem_matrixIsometries_iff]
    intro v
    have : matrixLinearEquiv x v = L v := by rw [← hxL]; rfl
    rw [this, hLv, hπQ]
  have hx3 : x * x * x = 1 := by
    apply matrixLinearIso.injective
    rw [map_mul, map_mul, map_one, hxL]
    ext v i
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, hLv, Function.comp_apply, id_eq]
    rw [hπ3]
  have hxd : x ∈ matrixDerived Q₀ := by
    have h := mul_mem (sq_mem_matrixDerived k hnd hT hx) (sq_mem_matrixDerived k hnd hT hx)
    convert h using 1
    calc x = x * (x * x * x) := by rw [hx3, mul_one]
      _ = x * x * (x * x) := by group
  let t : matrixProjectiveDerived Q₀ := matrixProjectiveProjection Q₀ ⟨x, hxd⟩
  have ht3 : t ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxd⟩ : matrixDerived Q₀) ^ 3 = 1 := Subtype.ext (by simpa [pow_succ] using hx3)
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : (⟨x, hxd⟩ : matrixDerived Q₀) ∈ matrixDerivedScalars Q₀ :=
      (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q₀ _).mp h1
    obtain ⟨y, hy⟩ := hπ1
    let e : Fin d → k := Pi.single (π y) 1
    have h2 := congrFun (congrArg (fun A : GL (Fin d) k => matrixLinearEquiv A e)
      (show x = _ from hc.symm)) y
    have h3 : matrixLinearEquiv x e y = 1 := by
      have : matrixLinearEquiv x e = L e := by rw [← hxL]; rfl
      rw [this, hLv]
      simp [e]
    simp only [matrixLinearEquiv_scalar, Pi.smul_apply] at h2
    rw [h3] at h2
    have h4 : e y = 0 := Pi.single_eq_of_ne (fun h => hy h.symm) _
    rw [h4] at h2
    simp at h2
  have := orderOf_eq_prime ht3 ht1
  rw [← this]
  exact orderOf_dvd_natCard t

end ThreeDvd

section Fixed

open scoped commutatorElement

open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
  (matrixProjectiveConjugationHom_eq_fieldAutT)

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem isPerfect_of_simple_nonabelian {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem exists_fixed_perfect_of_subfieldSetup (S : SubfieldSetup k Q₀ Q' σ p)
    {β : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q' g' (Θ x))
    (h3 : 3 ∣ Nat.card (matrixProjectiveDerived Q₀)) :
    ∃ D : Subgroup (matrixProjectiveDerived Q), (∀ x ∈ D, β x = x) ∧ ⁅D, D⁆ = D ∧
      3 ∣ Nat.card D := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  have hfa := matrixProjectiveConjugationHom_eq_fieldAutT S g' hl hr
  obtain ⟨hsimple, hnab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hperf := isPerfect_of_simple_nonabelian hsimple hnab
  let J := subfieldDerivedImage k S.hext
  let D := J.map Θ.symm.toMonoidHom
  let eD : ↥D ≃* matrixProjectiveDerived Q₀ :=
    (J.equivMapOfInjective Θ.symm.toMonoidHom Θ.symm.injective).symm.trans
      (inclEquiv k S.hext hd).symm
  refine ⟨D, ?_, commutator_eq_self_of_equiv_perfect D eD, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    apply Θ.injective
    rw [hΘ, hfa]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply]
    exact fieldAutT_fixes_J k Q' σ S.hQσ S.hext S.hσk hj
  · rw [Nat.card_congr eD.toEquiv]
    exact h3

end Fixed

section Perm

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem exists_perm_three (m : ℕ) (hm : 3 ≤ m) :
    ∃ c : Equiv.Perm (Fin m), (∀ x, c (c (c x)) = x) ∧ ∃ x, c x ≠ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (Equiv.Perm (Fin m)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    exact Nat.dvd_factorial (by norm_num) hm
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨c, fun x => ?_, ?_⟩
  · have h := congrArg (fun g : Equiv.Perm (Fin m) => g x) (hc ▸ pow_orderOf_eq_one c)
    simpa [pow_succ] using h
  · by_contra hcon
    have : c = 1 := Equiv.ext fun x => by_contra fun h => hcon ⟨x, h⟩
    rw [this, orderOf_one] at hc
    omega

theorem exists_perm_of_equiv {d : ℕ} {ι : Type} (e : ι ≃ Fin d) (τ : Equiv.Perm ι)
    (h3 : ∀ x, τ (τ (τ x)) = x) (h1 : ∃ x, τ x ≠ x) :
    ∃ π : Equiv.Perm (Fin d), (∀ y, π (π (π y)) = y) ∧ (∃ y, π y ≠ y) ∧
      ∀ x, π (e x) = e (τ x) := by
  refine ⟨e.permCongr τ, fun y => ?_, ?_, fun x => by simp [Equiv.permCongr_apply]⟩
  · simp [Equiv.permCongr_apply, h3]
  · obtain ⟨x, hx⟩ := h1
    exact ⟨e x, by simpa [Equiv.permCongr_apply] using hx⟩

variable (F : Type) [Field F]

theorem exists_perm_odd {n : ℕ} (hn : 3 ≤ n) :
    ∃ π : Equiv.Perm (Fin (2 * n + 1)), (∀ y, π (π (π y)) = y) ∧ (∃ y, π y ≠ y) ∧
      ∀ v : Fin (2 * n + 1) → F, coordinateQuadOdd n F (v ∘ π) = coordinateQuadOdd n F v := by
  obtain ⟨c, hc3, hc1⟩ := exists_perm_three n hn
  obtain ⟨π, h3, h1, hπ⟩ := exists_perm_of_equiv (oddIndexEquiv n)
    (Equiv.sumCongr c (Equiv.sumCongr c (Equiv.refl Unit)))
    (by rintro (i | i | i) <;> simp [hc3]) (by
      obtain ⟨x, hx⟩ := hc1
      exact ⟨.inl x, by simpa using hx⟩)
  refine ⟨π, h3, h1, fun v => ?_⟩
  rw [coordinateQuadOdd_apply, coordinateQuadOdd_apply]
  simp only [Function.comp_apply, hπ]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_refl, id_eq]
  rw [Equiv.sum_comp c (fun i => v (oddIndexEquiv n (.inl i)) *
    v (oddIndexEquiv n (.inr (.inl i))))]

theorem exists_perm_plus {n : ℕ} (hn : 3 ≤ n) :
    ∃ π : Equiv.Perm (Fin (2 * n)), (∀ y, π (π (π y)) = y) ∧ (∃ y, π y ≠ y) ∧
      ∀ v : Fin (2 * n) → F, coordinateQuadPlus n F (v ∘ π) = coordinateQuadPlus n F v := by
  obtain ⟨c, hc3, hc1⟩ := exists_perm_three n hn
  obtain ⟨π, h3, h1, hπ⟩ := exists_perm_of_equiv (plusIndexEquiv n)
    (Equiv.sumCongr c c)
    (by rintro (i | i) <;> simp [hc3]) (by
      obtain ⟨x, hx⟩ := hc1
      exact ⟨.inl x, by simpa using hx⟩)
  refine ⟨π, h3, h1, fun v => ?_⟩
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp only [Function.comp_apply, hπ]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  rw [Equiv.sum_comp c (fun i => v (plusIndexEquiv n (.inl i)) *
    v (plusIndexEquiv n (.inr i)))]

theorem exists_perm_minus {n : ℕ} (hn : 4 ≤ n) (hn1 : 1 ≤ n) (b c' : F) :
    ∃ π : Equiv.Perm (Fin (2 * n)), (∀ y, π (π (π y)) = y) ∧ (∃ y, π y ≠ y) ∧
      ∀ v : Fin (2 * n) → F,
        coordinateQuadMinus n F hn1 b c' (v ∘ π) = coordinateQuadMinus n F hn1 b c' v := by
  obtain ⟨c, hc3, hc1⟩ := exists_perm_three (n - 1) (by omega)
  obtain ⟨π, h3, h1, hπ⟩ := exists_perm_of_equiv (minusIndexEquiv n hn1)
    (Equiv.sumCongr c (Equiv.sumCongr c (Equiv.refl (Fin 2))))
    (by rintro (i | i | i) <;> simp [hc3]) (by
      obtain ⟨x, hx⟩ := hc1
      exact ⟨.inl x, by simpa using hx⟩)
  refine ⟨π, h3, h1, fun v => ?_⟩
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [Function.comp_apply, hπ]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_refl, id_eq]
  rw [Equiv.sum_comp c (fun i => v (minusIndexEquiv n hn1 (.inl i)) *
    v (minusIndexEquiv n hn1 (.inr (.inl i))))]

end Perm

end CFSG.HardMathSupport.Malle.E27Lie
