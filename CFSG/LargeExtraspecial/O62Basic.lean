module

public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.Fischer.Classification.PartIII.Arf.Gamma

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsPlus (Q : QuadraticForm (ZMod 2) V) : Prop :=
  ∃ W : Submodule (ZMod 2) V, 2 * finrank (ZMod 2) W = 6 ∧ ∀ w ∈ W, Q w = 0

abbrev V₀ : Type := Fin 6 → ZMod 2

noncomputable def qPlus : QuadraticForm (ZMod 2) V₀ := proj 0 1 + proj 2 3 + proj 4 5

noncomputable abbrev qMinus : QuadraticForm (ZMod 2) V₀ :=
  CFSG.Fischer.Classification.quadMinusSix

theorem qPlus_apply (x : V₀) : qPlus x = x 0 * x 1 + x 2 * x 3 + x 4 * x 5 := by
  simp only [qPlus, add_apply, proj_apply]

theorem qMinus_apply (x : V₀) :
    qMinus x = x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5 :=
  CFSG.Fischer.Classification.quadMinusSix_apply x

theorem polar_qPlus (x y : V₀) :
    polar qPlus x y = x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4 := by
  simp only [polar, qPlus_apply, Pi.add_apply]
  ring

theorem polar_qMinus (x y : V₀) :
    polar qMinus x y = x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4 :=
  CFSG.Fischer.Classification.polar_quadMinusSix x y

theorem polar_qPlus_eq_polar_qMinus (x y : V₀) : polar qPlus x y = polar qMinus x y := by
  rw [polar_qPlus, polar_qMinus]

theorem polar_qPlus_nondeg : ∀ x : V₀, (∀ y, polar qPlus x y = 0) → x = 0 := by
  intro x hx
  simp only [polar_qPlus_eq_polar_qMinus] at hx
  exact CFSG.Fischer.Classification.polar_quadMinusSix_nondeg x hx

theorem polar_qMinus_nondeg : ∀ x : V₀, (∀ y, polar qMinus x y = 0) → x = 0 :=
  CFSG.Fischer.Classification.polar_quadMinusSix_nondeg

theorem nondegenerate_of_forall {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {Q : QuadraticForm (ZMod 2) W} (h : ∀ x, (∀ y, polar Q x y = 0) → x = 0) :
    Q.polarBilin.Nondegenerate :=
  ⟨fun x hx => h x fun y => by simpa only [polarBilin_apply_apply] using hx y,
    fun y hy => h y fun x => by
      rw [polar_comm]
      simpa only [polarBilin_apply_apply] using hy x⟩

theorem qPlus_nondegenerate : qPlus.polarBilin.Nondegenerate :=
  nondegenerate_of_forall polar_qPlus_nondeg

theorem qMinus_nondegenerate : qMinus.polarBilin.Nondegenerate :=
  nondegenerate_of_forall polar_qMinus_nondeg

private theorem card_filter_qPlus : (Finset.univ.filter (fun v : V₀ =>
    v 0 * v 1 + v 2 * v 3 + v 4 * v 5 = 1)).card = 28 := by
  decide +kernel

theorem ncard_qPlus : {v : V₀ | qPlus v = 1}.ncard = 28 := by
  rw [Set.ncard_eq_toFinset_card']
  simp only [qPlus_apply, Set.toFinset_ofPred]
  exact card_filter_qPlus

theorem ncard_qMinus : {v : V₀ | qMinus v = 1}.ncard = 36 :=
  CFSG.Fischer.Classification.ncard_quadMinusSix

theorem natCard_eq_sixtyFour [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 6) :
    Nat.card V = 64 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hV]
  rfl

theorem forall_polar_of_nondegenerate {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) : ∀ x, (∀ y, polar Q x y = 0) → x = 0 :=
  fun x hx => hQ.1 x fun y => by rw [polarBilin_apply_apply]; exact hx y

theorem exists_linearEquiv_model [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ L : V ≃ₗ[ZMod 2] V₀, (∀ v, qPlus (L v) = Q v) ∨ (∀ v, qMinus (L v) = Q v) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard := natCard_eq_sixtyFour hV
  have hnd := forall_polar_of_nondegenerate hQ
  have hV₀ : Nat.card V = Nat.card V₀ := by
    rw [hcard, Nat.card_eq_fintype_card]
    rfl
  rcases CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic (Q := Q) hnd (m := 3)
    (by rw [hcard]; norm_num) with h | h
  · obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq Q qPlus hnd
      polar_qPlus_nondeg hV₀ (by rw [ncard_qPlus]; omega)
    exact ⟨L, Or.inl hL⟩
  · obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq Q qMinus hnd
      polar_qMinus_nondeg hV₀ (by rw [ncard_qMinus]; omega)
    exact ⟨L, Or.inr hL⟩

theorem isPlus_of_qPlus [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (L : V ≃ₗ[ZMod 2] V₀) (hL : ∀ v, qPlus (L v) = Q v) : IsPlus Q := by
  set f : V₀ →ₗ[ZMod 2] (Fin 3 → ZMod 2) := LinearMap.funLeft (ZMod 2) (ZMod 2) ![1, 3, 5]
  have hf : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (by decide)
  have hk : finrank (ZMod 2) (LinearMap.ker f) = 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_fin_fun] at h
    rw [Module.finrank_fin_fun] at h
    omega
  refine ⟨(LinearMap.ker f).map (L.symm : V₀ →ₗ[ZMod 2] V), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hk]
  · rintro w ⟨u, hu, rfl⟩
    have h1 : u 1 = 0 := congrFun hu 0
    have h3 : u 3 = 0 := congrFun hu 1
    have h5 : u 5 = 0 := congrFun hu 2
    rw [LinearEquiv.coe_coe, ← hL, LinearEquiv.apply_symm_apply, qPlus_apply]
    simp [h1, h3, h5]

theorem exists_linearEquiv_qMinus [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) (hm : ¬ IsPlus Q) :
    ∃ L : V ≃ₗ[ZMod 2] V₀, ∀ v, qMinus (L v) = Q v := by
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model hV hQ
  · exact absurd (isPlus_of_qPlus L hL) hm
  · exact ⟨L, hL⟩

theorem zmod2_eq_zero_or_eq_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem ncard_map_eq_zero [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) :
    {v | Q v = 0}.ncard = 36 ∨ {v | Q v = 0}.ncard = 28 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard := natCard_eq_sixtyFour hV
  have hc : {v | Q v = 0} = {v | Q v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (Q v) with h | h <;> simp [h]
  have hsum := Set.ncard_add_ncard_compl {v | Q v = 1}
  rw [← hc, hcard] at hsum
  rcases CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic (Q := Q)
    (forall_polar_of_nondegenerate hQ) (m := 3) (by rw [hcard]; norm_num) with h | h
  · norm_num at h
    left
    omega
  · norm_num at h
    right
    omega

theorem card_orthogonalGroup [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 51840 := by
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq hQ (m := 3) (by rw [hV])
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2] at h1
  rcases ncard_map_eq_zero hV hQ with h | h
  · left
    rw [h] at h1
    omega
  · right
    rw [h] at h1
    omega

theorem card_omegaGroup [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate) :
    Nat.card (omegaGroup Q hQ) = 20160 ∨ Nat.card (omegaGroup Q hQ) = 25920 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have h := S12DW.card_orthogonalGroup_eq hQ
  rcases card_orthogonalGroup hV hQ with h1 | h1
  · left
    omega
  · right
    omega

theorem finite_linearEquiv [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem card_le_of_isPGroup_of_not_dvd {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hPK : P ≤ K) (h2 : IsPGroup 2 P) {e : ℕ} (hK : ¬ 2 ^ (e + 1) ∣ Nat.card K) :
    Nat.card P ≤ 2 ^ e := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd := Subgroup.card_dvd_of_le hPK
  rw [hk] at hdvd ⊢
  by_contra hlt
  have hle : e + 1 ≤ k := by
    by_contra h'
    exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact hK ((Nat.pow_dvd_pow 2 hle).trans hdvd)

theorem card_le_of_isPGroup [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h2 : IsPGroup 2 P) : Nat.card P ≤ 2 ^ 7 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := finite_linearEquiv (V := V)
  refine card_le_of_isPGroup_of_not_dvd hP h2 ?_
  rcases card_orthogonalGroup hV hQ with h | h <;> rw [h] <;> decide

theorem card_le_of_isPGroup_omega [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ omegaGroup Q hQ) (h2 : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ 6 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := finite_linearEquiv (V := V)
  refine card_le_of_isPGroup_of_not_dvd hP h2 ?_
  rcases card_omegaGroup hV hQ with h | h <;> rw [h] <;> decide

end CFSG.LargeExtraspecial.O62
