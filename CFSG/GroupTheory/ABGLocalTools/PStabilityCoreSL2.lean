module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreOdd
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGlauberman

public section

open Subgroup

namespace CFSG.ABGLocalTools

theorem quadratic_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0) (n : ℕ) :
    (((a ^ n : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - 1) ^ 2 = 0 := by
  set N := (a : V →ₗ[K] V) - 1 with hN
  have h1 : (a : V →ₗ[K] V) = 1 + N := by rw [hN]; abel
  rw [Units.val_pow_eq_pow_val, h1, CFSG.LinearGroups.one_add_pow_of_sq_eq_zero ha,
    add_sub_cancel_left, (Nat.cast_commute n N).mul_pow, ha, mul_zero]

theorem odd_card_of_charP {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p ≠ 2) : Odd (Nat.card K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card, hn]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

theorem HasSL2Quotient.of_odd_kernel {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hodd : SL2OddNormal)
    {X Y : Type*} [Group X] [Finite X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) (h : HasSL2Quotient p X) : HasSL2Quotient p Y := by
  have key : ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
      ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective φ →
        ∃ φ' : Y →* Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective φ' := by
    intro K _ _ hK φ hφ
    have hN : (f.ker.map φ).Normal := f.normal_ker.map φ hφ
    have hNodd : Odd (Nat.card (f.ker.map φ)) := Odd.of_dvd_nat hker (card_map_dvd _ _)
    have hbot := hodd K hK _ hN hNodd
    have hle : f.ker ≤ φ.ker := by
      intro y hy
      have : φ y ∈ f.ker.map φ := ⟨y, hy, rfl⟩
      rw [hbot, mem_bot] at this
      exact this
    refine ⟨f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨φ, hle⟩, fun t => ?_⟩
    obtain ⟨y, rfl⟩ := hφ t
    exact ⟨f y, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  rcases h with ⟨K, hK, hKf, hKc, φ, hφ⟩ | ⟨φ, hφ⟩
  · obtain ⟨φ', hφ'⟩ := key K (odd_card_of_charP hp) φ hφ
    exact Or.inl ⟨K, hK, hKf, hKc, φ', hφ'⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨φ', hφ'⟩ := key (ZMod 5) (by rw [Nat.card_zmod]; decide) φ hφ
    exact Or.inr ⟨φ', hφ'⟩

variable {G M : Type*} [Group G] [Finite G] [Group M] {p : ℕ} [Fact p.Prime] {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

theorem false_of_split (hp : p ≠ 2) (π : G →* M) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) {x : G} (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (J : Subgroup M) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (hpF : ¬ p ∣ Nat.card F) (hpF1 : ¬ p ∣ Nat.card F + 1)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hborel : SL2BorelOfSplitElement)
    (hxJ : π x ∈ J) (hxo : orderOf (π x) = p) : False := by
  set ι : Matrix.SpecialLinearGroup (Fin 2) F →* M := J.subtype.comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := (subtype_injective J).comp e.symm.injective
  set g := e ⟨π x, hxJ⟩ with hg
  have hιg : ι g = π x := by simp [hι, hg]
  have hgo : orderOf g = p := by
    rw [hg, MulEquiv.orderOf_eq, ← orderOf_coe]
    exact hxo
  obtain ⟨B, hgB, hBc, hBp, -⟩ := hborel F p hp hF hpF hpF1 g hgo
  have hxB : π x ∈ B.map ι := ⟨g, hgB, hιg⟩
  have h := mem_pCore_of_twoSubgroupsCyclic hp π hπ hker ρ hρ hx
    (hBc.map_of_injective ι hιinj) hxB
  rw [pCore_map_eq_bot_of_injective hBp ι hιinj, mem_bot] at h
  have h1 : π x = 1 := congrArg Subtype.val h
  rw [h1, orderOf_one] at hxo
  exact (Fact.out : p.Prime).one_lt.ne hxo

theorem false_of_nonsplit
    (hp : p ≠ 2) (π : G →* M) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) {x : G} (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (J : Subgroup M) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (h5 : 5 < Nat.card F) (hpF : ¬ p ∣ Nat.card F) (hpF1 : p ∣ Nat.card F + 1)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hchoice : SL2ElementChoice)
    (hoddn : SL2OddNormal) (hdickson : SL2DicksonQuotient) (hxJ : π x ∈ J)
    (hxo : orderOf (π x) = p) : False := by
  set ι : Matrix.SpecialLinearGroup (Fin 2) F →* M := J.subtype.comp e.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := (subtype_injective J).comp e.symm.injective
  set g := e ⟨π x, hxJ⟩ with hg
  have hιg : ι g = π x := by simp [hι, hg]
  have hgo : orderOf g = p := by
    rw [hg, MulEquiv.orderOf_eq, ← orderOf_coe]
    exact hxo
  obtain ⟨u, w, hw, hwp, hw35⟩ := hchoice F p hp hF h5 hpF1 g hgo
  obtain ⟨û, hû⟩ := hπ (ι u)
  set x' := û * x * û⁻¹ with hx'
  set X := closure ({x, x'} : Set G) with hX
  set Xg := closure ({g, u * g * u⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hXg
  have hπx' : π x' = ι (u * g * u⁻¹) := by
    rw [hx', map_mul, map_mul, map_inv, hû, map_mul, map_mul, map_inv, hιg]
  have hXmap : X.map π = Xg.map ι := by
    rw [hX, hXg, MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair,
      hπx', hιg]
  have hnp : ¬ IsPGroup p X := by
    intro hXp
    have h1 : IsPGroup p (Xg.map ι) := hXmap ▸ hXp.map π
    obtain ⟨k, hk⟩ := h1 ⟨ι w, w, hw, rfl⟩
    apply hwp k
    apply hιinj
    rw [map_pow, map_one]
    exact congrArg Subtype.val hk
  set σ := ρ.comp X.subtype with hσ
  have hab := closure_pair_preimage_eq_top x x'
  have hb : ((σ ⟨x', subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
      V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
    change ((ρ (û * x * û⁻¹) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0
    have := (CFSG.LinearGroups.quadratic_linear_p_elements p (ρ x) hx).2 (ρ û⁻¹)
    rwa [map_inv, inv_inv, ← map_inv, ← map_mul, ← map_mul] at this
  have hσinj : Function.Injective σ := by
    rw [hσ, MonoidHom.coe_comp]
    exact hρ.comp (subtype_injective X)
  have hnpσ : ¬ IsPGroup p σ.range := fun h => hnp (h.of_equiv (MonoidHom.ofInjective hσinj).symm)
  have hSL := hasSL2Quotient_of_rep hp σ hab hx hb hnpσ
  set fX := π.subgroupMap X with hfX
  have hkerX : Odd (Nat.card fX.ker) := by
    have h1 : Nat.card (fX.ker.map X.subtype) = Nat.card fX.ker :=
      card_map_of_injective (subtype_injective X)
    have h2 : fX.ker.map X.subtype ≤ π.ker := by
      rintro _ ⟨y, hy, rfl⟩
      have := congrArg Subtype.val hy
      exact this
    rw [← h1]
    exact Odd.of_dvd_nat hker (card_dvd_of_le h2)
  have hSL2 := hSL.of_odd_kernel hp hoddn fX (π.subgroupMap_surjective X) hkerX
  have e2 : Xg ≃* (X.map π) :=
    (Xg.equivMapOfInjective ι hιinj).trans (MulEquiv.subgroupCongr hXmap.symm)
  have hSL3 : HasSL2Quotient p Xg := hSL2.of_surjective e2.toMonoidHom e2.surjective
  have hgo' : orderOf (u * g * u⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hgo
  obtain ⟨h35, hall⟩ := hdickson F p hp hF hpF g (u * g * u⁻¹) hgo hgo' hSL3
  obtain ⟨h4, h6, h10⟩ := hw35 h35
  rcases hall w hw with h | h | h
  · exact h4 h
  · exact h6 h
  · exact h10 h

theorem map_eq_one_of_quadratic
    (hp : p ≠ 2) (π : G →* M) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) {x : G} (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) (J : Subgroup M) {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h5 : 5 < Nat.card F) (hpF : ¬ p ∣ Nat.card F)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hchoice : SL2ElementChoice)
    (hborel : SL2BorelOfSplitElement) (hoddn : SL2OddNormal) (hdickson : SL2DicksonQuotient)
    (hout : ∀ y : G, ((ρ y : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 → π y ^ p = 1 → π y ∈ J) :
    π x = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ := hxp
  have hdvd : orderOf (π x) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hs
    exact hne hs
  have hpm : p ∣ orderOf (π x) := by rw [hs]; exact dvd_pow_self p hs0
  have hm0 : orderOf (π x) ≠ 0 := by rw [hs]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  set x₁ := x ^ (orderOf (π x) / p) with hx₁def
  have hx₁o : orderOf (π x₁) = p := by
    rw [hx₁def, map_pow]
    exact orderOf_pow_orderOf_div hm0 hpm
  have hx₁ : ((ρ x₁ : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
    rw [hx₁def, map_pow]
    exact quadratic_pow (ρ x) hx _
  have hx₁J := hout x₁ hx₁ (by rw [← hx₁o]; exact pow_orderOf_eq_one _)
  by_cases hp1 : p ∣ Nat.card F + 1
  · exact false_of_nonsplit hp π hπ hker ρ hρ hx₁ J hF h5 hpF hp1 e hchoice hoddn hdickson hx₁J
      hx₁o
  · exact false_of_split hp π hπ hker ρ hρ hx₁ J hF hpF hp1 e hborel hx₁J hx₁o

end CFSG.ABGLocalTools
