module

public import CFSG.LargeExtraspecial.A2ModNatural
public import CFSG.LieType.ChevTwo.OrthogonalBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.Natural

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open Matrix
open CFSG.RankThree.GF2n.Stroth80.Classify (orthSubgroup)

theorem not_ordD_dvd_ordTwistedD {m : ℕ} (hm : 2 ≤ m) : ¬ ordD m 2 ∣ ordTwistedD m 2 := by
  rw [Ord.ordD_two_eq (by omega), Ord.ordTwistedD_two_eq (by omega)]
  intro h
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) := Finset.prod_pos fun i hi =>
    AS35YT.one_le_two_pow_two_mul_sub_one (Finset.mem_Icc.mp hi).1
  rw [mul_right_comm (2 ^ (m * (m - 1))) (2 ^ m - 1),
    mul_right_comm (2 ^ (m * (m - 1))) (2 ^ m + 1)] at h
  have h1 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by positivity) hP) h
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 2 ^ m - 1 ∣ 2 := by
    have := Nat.dvd_sub h1 (dvd_refl (2 ^ m - 1))
    rwa [show 2 ^ m + 1 - (2 ^ m - 1) = 2 by omega] at this
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_ordTwistedD_dvd_ordD {m : ℕ} (hm : 1 ≤ m) : ¬ ordTwistedD m 2 ∣ ordD m 2 := by
  rw [Ord.ordD_two_eq hm, Ord.ordTwistedD_two_eq hm]
  intro h
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) := Finset.prod_pos fun i hi =>
    AS35YT.one_le_two_pow_two_mul_sub_one (Finset.mem_Icc.mp hi).1
  have h2 : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
  have hpos : 0 < 2 ^ (m * (m - 1)) * (2 ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1),
      (2 ^ (2 * i) - 1) := Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) hP
  have hle := Nat.le_of_dvd hpos h
  have hlt : 2 ^ (m * (m - 1)) * (2 ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) <
      2 ^ (m * (m - 1)) * (2 ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)) hP
  omega

theorem card_statedOmega_plus_two {m : ℕ} (hm : 4 ≤ m) :
    Nat.card ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) = ordD m 2 := by
  have h : StatedClassicalModel ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) .POmegaPlus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(CFSG.LieType.ChevTwo.statedProjEquivTwo _).symm⟩⟩
  simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl

theorem card_statedOmega_minus_two {m : ℕ} (hm : 4 ≤ m) :
    Nat.card ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) = ordTwistedD m 2 := by
  have h : StatedClassicalModel ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))
      .POmegaMinus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, by simp, 1, 1,
      by decide, ⟨(CFSG.LieType.ChevTwo.statedProjEquivTwo _).symm⟩⟩
  simpa using (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.2 rfl

theorem eq_one_of_irreducible {β γ : ZMod 2} (hβ : β ≠ 0)
    (hs : ∀ s : ZMod 2, s ^ 2 + β * s + γ ≠ 0) : β = 1 ∧ γ = 1 := by
  have hγ : γ ≠ 0 := fun h => hs 0 (by rw [h]; ring)
  revert hβ hγ
  revert β γ
  decide

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem radU_eq_bot_of_card [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {m : ℕ}
    (hlt : 2 ^ ((m - 1) ^ 2) * ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) < Nat.card X)
    (hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m) :
    AS35YS.radU Q (commSpaceOf ρ ⊤) = ⊥ ∧
      finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) = 2 * m := by
  obtain ⟨j, hj, hcard⟩ := exists_card_le_spOrd hQ hiso hinj h2
  have hjm : m ≤ j := by
    by_contra hlt'
    have := AS35YN.spOrd_le (show j ≤ m - 1 by omega)
    omega
  have hq : finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) +
      finrank (ZMod 2) (AS35YS.radU Q (commSpaceOf ρ ⊤)) =
        finrank (ZMod 2) (commSpaceOf ρ ⊤) :=
    Submodule.finrank_quotient_add_finrank _
  have hle := finrank_quo_le (ρ := ρ) (Q := Q)
  have hrad : finrank (ZMod 2) (AS35YS.radU Q (commSpaceOf ρ ⊤)) = 0 := by omega
  exact ⟨Submodule.finrank_eq_zero.mp hrad, by omega⟩

theorem singular_of_radU_eq_bot (h : AS35YS.radU Q (commSpaceOf ρ ⊤) = ⊥) :
    ∀ v ∈ commSpaceOf ρ ⊤, (∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) → Q v = 0 := by
  intro v hv hpol
  have hmem : (⟨v, hv⟩ : commSpaceOf ρ ⊤) ∈ AS35YS.radU Q (commSpaceOf ρ ⊤) :=
    AS35YS.mem_radU.mpr hpol
  rw [h, Submodule.mem_bot] at hmem
  have : v = 0 := congrArg Subtype.val hmem
  rw [this, map_zero]

theorem natAct_mem_orthSubgroup (hiso : ∀ x v, Q (ρ x v) = Q v)
    (h : ∀ v ∈ commSpaceOf ρ ⊤, (∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) → Q v = 0) (x : X) :
    natAct hiso x ∈ orthSubgroup (AS35YS.qQuo h) := fun w =>
  AS35YS.qQuo_quoHom (hiso := range_isometry hiso) (hU := range_mem_commSpaceOf) h _ w

theorem range_natAct_le_commutator (hiso : ∀ x v, Q (ρ x v) = Q v)
    (h : ∀ v ∈ commSpaceOf ρ ⊤, (∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) → Q v = 0)
    (hperf : commutator X = ⊤) :
    (natAct hiso).range ≤ ⁅orthSubgroup (AS35YS.qQuo h), orthSubgroup (AS35YS.qQuo h)⁆ := by
  have hle : (natAct hiso).range ≤ orthSubgroup (AS35YS.qQuo h) := by
    rintro _ ⟨x, rfl⟩
    exact natAct_mem_orthSubgroup hiso h x
  calc (natAct hiso).range = Subgroup.map (natAct hiso) (commutator X) := by
        rw [hperf, MonoidHom.range_eq_map]
    _ = ⁅(natAct hiso).range, (natAct hiso).range⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    _ ≤ _ := Subgroup.commutator_mono hle hle

theorem card_commutator_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (ZMod 2) W) (Qf : QuadraticForm (ZMod 2) W)
    (Q' : (ι → ZMod 2) → ZMod 2) (hQ' : ∀ v, Qf (b.equivFun.symm v) = Q' v) :
    Nat.card ↥⁅orthSubgroup Qf, orthSubgroup Qf⁆ = Nat.card ↥(StatedOmega Q') := by
  have hr := CFSG.RankThree.GF2n.Stroth80.Classify.range_comp_eq_statedOmega b Qf
    (⁅orthSubgroup Qf, orthSubgroup Qf⁆.subtype) (Subgroup.range_subtype _) Q' hQ'
  rw [← hr]
  exact Nat.card_congr (MonoidHom.ofInjective
    (b.toGL.injective.comp (Subgroup.subtype_injective _))).toEquiv

theorem exists_coords_of_range_eq [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h : ∀ v ∈ commSpaceOf ρ ⊤, (∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) → Q v = 0)
    (hrad : AS35YS.radU Q (commSpaceOf ρ ⊤) = ⊥) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)))
    (Q' : (ι → ZMod 2) → ZMod 2) (hQ' : ∀ v, AS35YS.qQuo h (b.equivFun.symm v) = Q' v)
    (hr : (natAct hiso).range =
      ⁅orthSubgroup (AS35YS.qQuo h), orthSubgroup (AS35YS.qQuo h)⁆) :
    ∃ (φ : X ≃* ↥(StatedOmega Q')) (π : V →ₗ[ZMod 2] (ι → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤,
        π (ρ x v) = ((φ x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, Q' (π v) = Q v) := by
  have hrange := CFSG.RankThree.GF2n.Stroth80.Classify.range_comp_eq_statedOmega b
    (AS35YS.qQuo h) (natAct hiso) hr Q' hQ'
  set ψ : X →* GL ι (ZMod 2) := b.toGL.toMonoidHom.comp (natAct hiso) with hψ
  have hψinj : Function.Injective ψ :=
    b.toGL.injective.comp (natAct_injective hQ hiso hinj h2)
  let φ : X ≃* ↥(StatedOmega Q') :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrange)
  have hφ : ∀ x, ((φ x : StatedOmega Q') : GL ι (ZMod 2)) = ψ x := fun x => rfl
  set π₀ : commSpaceOf ρ ⊤ →ₗ[ZMod 2] (ι → ZMod 2) :=
    b.equivFun.toLinearMap.comp (AS35YS.radU Q (commSpaceOf ρ ⊤)).mkQ with hπ₀
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend π₀
  have hπU : ∀ u : commSpaceOf ρ ⊤, π u = b.equivFun (Submodule.Quotient.mk u) := fun u =>
    LinearMap.congr_fun hπ u
  refine ⟨φ, π, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨w, rfl⟩ := b.equivFun.surjective y
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨u, u.2, hπU u⟩
  · rw [eq_bot_iff]
    intro v hvmem
    obtain ⟨hv, hv0⟩ := Submodule.mem_inf.mp hvmem
    rw [LinearMap.mem_ker, hπU ⟨v, hv⟩, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero, hrad, Submodule.mem_bot] at hv0
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val hv0
  · intro x v hv
    rw [hπU ⟨ρ x v, apply_mem_commSpaceOf ρ (Subgroup.mem_top x) hv⟩, hπU ⟨v, hv⟩, hφ, hψ,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun]
    rfl
  · intro v hv
    rw [hπU ⟨v, hv⟩, ← hQ', LinearEquiv.symm_apply_apply, AS35YS.qQuo_mk]

theorem exists_natural_plus [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) (hperf : commutator X = ⊤)
    {m : ℕ} (hm : 4 ≤ m) (hX : Nat.card X = ordD m 2)
    (hlt : 2 ^ ((m - 1) ^ 2) * ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) < Nat.card X)
    (hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadPlus m (ZMod 2))))
      (π : V →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadPlus m (ZMod 2) (π v) = Q v) := by
  obtain ⟨hrad, hdimW⟩ := radU_eq_bot_of_card hQ hiso hinj h2 hlt hdim
  have h := singular_of_radU_eq_bot hrad
  have hnd := AS35YS.qQuo_nondegenerate h
  have hle := range_natAct_le_commutator hiso h hperf
  have hinjW := natAct_injective hQ hiso hinj h2
  have hcardR : Nat.card (natAct hiso).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinjW).toEquiv).symm
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤)) := Module.finite_of_finite (ZMod 2)
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤) ≃ₗ[ZMod 2] AS35YS.Quo Q (commSpaceOf ρ ⊤)) :=
    AS35YR.finite_linearEquiv_YR
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    (AS35YS.qQuo h) hnd).2.2.1 m (by omega) hdimW with ⟨b, hb⟩ | ⟨β, γ, hβ, hs, b, hb⟩
  · have hQ' : ∀ v, AS35YS.qQuo h (b.equivFun.symm v) = StatedQuadPlus m (ZMod 2) v := by
      intro v
      rw [CFSG.RankThree.GF2n.Stroth80.Classify.basis_equivFun_symm_plus b v]
      exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))
    have hcard := (card_commutator_eq b (AS35YS.qQuo h) _ hQ').trans (card_statedOmega_plus_two hm)
    have hr : (natAct hiso).range =
        ⁅orthSubgroup (AS35YS.qQuo h), orthSubgroup (AS35YS.qQuo h)⁆ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardR, hX])
    exact exists_coords_of_range_eq hQ hiso hinj h2 h hrad b _ hQ' hr
  · obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible hβ hs
    have hQ' : ∀ v, AS35YS.qQuo h (b.equivFun.symm v) = StatedQuadMinus m (ZMod 2) 1 1 v := by
      intro v
      rw [CFSG.RankThree.GF2n.Stroth80.Classify.basis_equivFun_symm_minus b v]
      exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr (Sum.inl i)))
        (v (Sum.inr (Sum.inr 0))) (v (Sum.inr (Sum.inr 1)))
    have hcard :=
      (card_commutator_eq b (AS35YS.qQuo h) _ hQ').trans (card_statedOmega_minus_two hm)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardR, hX, hcard] at hdvd
    exact (not_ordD_dvd_ordTwistedD (by omega) hdvd).elim

theorem exists_natural_minus [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) (hperf : commutator X = ⊤)
    {m : ℕ} (hm : 4 ≤ m) (hX : Nat.card X = ordTwistedD m 2)
    (hlt : 2 ^ ((m - 1) ^ 2) * ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) < Nat.card X)
    (hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)))
      (π : V →ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadMinus m (ZMod 2) 1 1 (π v) = Q v) := by
  obtain ⟨hrad, hdimW⟩ := radU_eq_bot_of_card hQ hiso hinj h2 hlt hdim
  have h := singular_of_radU_eq_bot hrad
  have hnd := AS35YS.qQuo_nondegenerate h
  have hle := range_natAct_le_commutator hiso h hperf
  have hinjW := natAct_injective hQ hiso hinj h2
  have hcardR : Nat.card (natAct hiso).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinjW).toEquiv).symm
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤)) := Module.finite_of_finite (ZMod 2)
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤) ≃ₗ[ZMod 2] AS35YS.Quo Q (commSpaceOf ρ ⊤)) :=
    AS35YR.finite_linearEquiv_YR
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    (AS35YS.qQuo h) hnd).2.2.1 m (by omega) hdimW with ⟨b, hb⟩ | ⟨β, γ, hβ, hs, b, hb⟩
  · have hQ' : ∀ v, AS35YS.qQuo h (b.equivFun.symm v) = StatedQuadPlus m (ZMod 2) v := by
      intro v
      rw [CFSG.RankThree.GF2n.Stroth80.Classify.basis_equivFun_symm_plus b v]
      exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))
    have hcard := (card_commutator_eq b (AS35YS.qQuo h) _ hQ').trans (card_statedOmega_plus_two hm)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardR, hX, hcard] at hdvd
    exact (not_ordTwistedD_dvd_ordD (by omega) hdvd).elim
  · obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible hβ hs
    have hQ' : ∀ v, AS35YS.qQuo h (b.equivFun.symm v) = StatedQuadMinus m (ZMod 2) 1 1 v := by
      intro v
      rw [CFSG.RankThree.GF2n.Stroth80.Classify.basis_equivFun_symm_minus b v]
      exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr (Sum.inl i)))
        (v (Sum.inr (Sum.inr 0))) (v (Sum.inr (Sum.inr 1)))
    have hcard :=
      (card_commutator_eq b (AS35YS.qQuo h) _ hQ').trans (card_statedOmega_minus_two hm)
    have hr : (natAct hiso).range =
        ⁅orthSubgroup (AS35YS.qQuo h), orthSubgroup (AS35YS.qQuo h)⁆ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardR, hX])
    exact exists_coords_of_range_eq hQ hiso hinj h2 h hrad b _ hQ' hr

end CFSG.LargeExtraspecial.A2Mod.Natural
