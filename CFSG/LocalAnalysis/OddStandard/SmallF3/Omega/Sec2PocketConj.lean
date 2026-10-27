module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_invType_of_quaternion_omegaProj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {f : QuaternionGroup 2 →* omegaProj hQ}
    (hf : Function.Injective f) :
    ∃ y : omegaGroup hQ, (y : OGroup Q) * y = 1 ∧ invType (y : OGroup Q) = (4, 1) ∧
      omegaToProj hQ y = f (QuaternionGroup.a 2) := by
  have ha2ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
  have ha2 : f (QuaternionGroup.a 2) ≠ 1 := fun h => ha2ne (hf (by rw [h, map_one]))
  obtain ⟨q, hq⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.a 1))
  obtain ⟨r, hr⟩ := omegaToProj_surjective hQ (f (QuaternionGroup.xa 0))
  obtain ⟨hρqq, hb, hc⟩ := q8_lift_relations hQ hq hr
  have hyy : ((q : OGroup Q) * (q : OGroup Q)) * ((q : OGroup Q) * (q : OGroup Q)) = 1 :=
    sq_sq_eq_one_of_q8_lifts (G := OGroup Q) (p := piOrth Q) (q := (q : OGroup Q))
      (r := (r : OGroup Q)) (fun y => (mul_piOrth_comm y).symm) piOrth_mul_self hb hc
  have hy1 : (q : OGroup Q) * (q : OGroup Q) ≠ 1 := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inl h)))
  have hyπ : (q : OGroup Q) * (q : OGroup Q) ≠ piOrth Q := fun h =>
    ha2 (hρqq.symm.trans ((omegaToProj_eq_one_iff hQ (q * q)).mpr (Or.inr h)))
  exact ⟨q * q, hyy, invType_eq_of_q8_lift hQ hdim q.2 r.2 hyy hy1 hyπ hb hc, hρqq⟩

theorem exists_conj_of_quaternion_omegaProj (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {f₁ f₂ : QuaternionGroup 2 →* omegaProj hQ}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) :
    ∃ c : omegaProj hQ,
      c * f₁ (QuaternionGroup.a 2) * c⁻¹ = f₂ (QuaternionGroup.a 2) := by
  obtain ⟨y₁, hy₁, ht₁, hy₁f⟩ := exists_invType_of_quaternion_omegaProj hQ hdim hf₁
  obtain ⟨y₂, hy₂, ht₂, hy₂f⟩ := exists_invType_of_quaternion_omegaProj hQ hdim hf₂
  obtain ⟨c, hc, hconj⟩ :=
    exists_mem_omegaGroup_conj hQ (by omega) hy₁ hy₂ (ht₁.trans ht₂.symm)
  refine ⟨omegaToProj hQ ⟨c, hc⟩, ?_⟩
  rw [← hy₁f, ← hy₂f, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hconj

end Model

theorem exists_conj_of_mk_eq_of_odd {A : Type} [Group A] {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (N : Subgroup A) [N.Normal] (hN : Odd (Nat.card N))
    (hab : (QuotientGroup.mk a : A ⧸ N) = QuotientGroup.mk b) : ∃ n ∈ N, n * a * n⁻¹ = b := by
  have hm : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
  set m : A := a⁻¹ * b with hmdef
  have hainv : a⁻¹ = a := (mul_eq_one_iff_eq_inv.mp ha).symm
  have hbm : b = a * m := by rw [hmdef]; group
  have h1 : a * m * a⁻¹ = m⁻¹ := by
    have h : (a * m * a) * m = 1 := by
      calc (a * m * a) * m = (a * m) * (a * m) := by group
        _ = 1 := by rw [← hbm]; exact hb
    rw [hainv]
    exact eq_inv_of_mul_eq_one_left h
  obtain ⟨j, hj⟩ : Odd (orderOf m) :=
    hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hm)
  have hpow : m ^ (2 * j + 1) = 1 := hj ▸ pow_orderOf_eq_one m
  set x : A := m ^ j with hx
  have hxx : x * x = m⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hpow, hx]
    group
  have hxa : a * x * a⁻¹ = x⁻¹ := by
    rw [hx, ← conj_pow, h1, inv_pow]
  have hxa' : a * x⁻¹ * a⁻¹ = x := by
    rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group, hxa, inv_inv]
  refine ⟨x, N.pow_mem hm j, ?_⟩
  calc x * a * x⁻¹ = x * (a * x⁻¹ * a⁻¹) * a := by group
    _ = (x * x) * a := by rw [hxa']
    _ = m⁻¹ * a := by rw [hxx]
    _ = (a * m * a⁻¹) * a := by rw [h1]
    _ = b := by rw [hbm]; group

theorem asc82OmegaPlusPocketedConj_holds : Asc82OmegaPlusPocketedConj := by
  intro G _ _ Y hY z₁ z₂ h₁ h₂
  obtain ⟨hz₁Y, f₁, hf₁, hf₁z⟩ := exists_quaternion_quotient_of_le (le_refl Y) h₁
  obtain ⟨hz₂Y, f₂, hf₂, hf₂z⟩ := exists_quaternion_quotient_of_le (le_refl Y) h₂
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, -, ⟨e⟩⟩ := isOmegaStar_of_lieModel_plus hY.2
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨c, hc⟩ := exists_conj_of_quaternion_omegaProj hQ hdim
    (f₁ := e.toMonoidHom.comp f₁) (f₂ := e.toMonoidHom.comp f₂)
    (e.injective.comp hf₁) (e.injective.comp hf₂)
  have hc' : e.symm c * (QuotientGroup.mk (⟨z₁, hz₁Y⟩ : ↥Y)) * (e.symm c)⁻¹ =
      QuotientGroup.mk (⟨z₂, hz₂Y⟩ : ↥Y) := by
    have h := congrArg e.symm hc
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hf₁z, hf₂z,
      map_mul, map_inv, MulEquiv.symm_apply_apply] at h
    exact h
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm c)
  rw [← hb] at hc'
  have hord : ∀ {z : G} (hz : z ∈ Y), orderOf z = 2 → (⟨z, hz⟩ : ↥Y) * ⟨z, hz⟩ = 1 := by
    intro z hz hz2
    refine Subtype.ext ?_
    change z * z = 1
    rw [← pow_two]
    exact hz2 ▸ pow_orderOf_eq_one z
  have hz₁₁ := hord hz₁Y h₁.1
  have hz₂₂ := hord hz₂Y h₂.1
  obtain ⟨n, hn, hconj⟩ := exists_conj_of_mk_eq_of_odd
    (a := b * ⟨z₁, hz₁Y⟩ * b⁻¹) (b := ⟨z₂, hz₂Y⟩)
    (by calc b * ⟨z₁, hz₁Y⟩ * b⁻¹ * (b * ⟨z₁, hz₁Y⟩ * b⁻¹)
          = b * (⟨z₁, hz₁Y⟩ * ⟨z₁, hz₁Y⟩) * b⁻¹ := by group
        _ = 1 := by rw [hz₁₁]; group)
    hz₂₂ (oddCore ↥Y) odd_card_oddCore (by rw [← hc']; simp)
  refine ⟨((n * b : ↥Y)⁻¹ : ↥Y), ((n * b)⁻¹).2, ?_⟩
  have h := congrArg Subtype.val hconj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  rw [← h]
  group

end CFSG.OddStandard.SmallF3.Omega
