module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter
public import CFSG.LocalAnalysis.ComponentInitial.ScalarNormalizerFieldPart
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiRootA
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public noncomputable section

universe u

namespace CFSG.LieType.Suzuki

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ShultStronglyClosedTI (suzukiU_layer_kernel)

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiFrob_pow_four_ne_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = x ^ 2 ^ (a + 1)) : φ ^ 4 ≠ 1 := by
  obtain ⟨-, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  intro h4
  have hψ : ∀ x : K, (φ ^ 2) x = x ^ 2 := fun x => by
    rw [sq, RingAut.mul_apply, hφ, hφ, hθθ]
  have hx : ∀ x : K, x ^ 4 = x := fun x => by
    have h := ringAut_pow_apply_of_sq hψ 2 x
    rw [← pow_mul, h4, RingAut.one_apply] at h
    norm_num at h
    exact h.symm
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 4)
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ 4 - Polynomial.X : Polynomial K) (f := id) Function.injective_id
    (fun x => by simp [hx x])
    (by
      rw [hdeg, hcard]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

omit [Finite K] in
@[expose] def glToAddAut [Module (ZMod 2) K] :
    LinearMap.GeneralLinearGroup (ZMod 2) K →* Multiplicative (AddAut K) where
  toFun g := Multiplicative.ofAdd (LinearMap.GeneralLinearGroup.toLinearEquiv g).toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite K] in
theorem glToAddAut_apply [Module (ZMod 2) K] (g : LinearMap.GeneralLinearGroup (ZMod 2) K)
    (x : K) : (glToAddAut g).toAdd x = (g : K →ₗ[ZMod 2] K) x :=
  rfl

theorem suzukiGroup_outer_isCyclic_card_dvd
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsCyclic (Outer (suzukiGroup a K)) ∧ Nat.card (Outer (suzukiGroup a K)) ∣ 2 * a + 1 := by
  classical
  obtain ⟨hchar, ⟨φ, hφ⟩, -⟩ := suzuki_frobenius_exponents a K hK
  let _ : Module (ZMod 2) K := (ZMod.algebra K 2).toModule
  have hφ4 := suzukiFrob_pow_four_ne_one ha hK φ hφ
  obtain ⟨hΨfst, hΨrange, hΨres, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK φ hφ4
  obtain ⟨ι, hι, hιsymm, -⟩ := Suzuki_root_A_isomorphism hK φ hφ
  obtain ⟨-, -, -, -, -, hprod, -⟩ := Suzuki_model_opposite_root_interface ha hK
  set V := (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom
  set C := pairAutSubgroup (suzukiU a K) V
  set r := pairAutRestrict (suzukiU a K) V
  set ρ : C →* LinearMap.GeneralLinearGroup (ZMod 2) K :=
    suzukiQuotAction.comp ((MulAut.congr ι).toMonoidHom.comp r)
  have hρform : ∀ β : C, ∃ (c : Kˣ) (σ : K ≃+* K), ∀ x,
      (ρ β : K →ₗ[ZMod 2] K) x = c * σ x := by
    intro β
    have hmem : ρ β ∈ Set.range (suzukiQuotAction (K := K) (φ := φ)) := ⟨_, rfl⟩
    rw [hΨrange] at hmem
    exact hmem
  have hρN : ∀ β : C, glToAddAut (ρ β) ∈
      Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) := fun β =>
    (mem_normalizer_scalarAddAut_iff _).2 (hρform β)
  set η : C →* (K ≃+* K) :=
    scalarNormalizerFieldPart.comp ((glToAddAut.comp ρ).codRestrict _ hρN)
  set π : C →* Outer (suzukiGroup a K) := (QuotientGroup.mk' (inner _)).comp C.subtype
  have hπs : Function.Surjective π := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (suzukiGroup a K)) q
    obtain ⟨g, β, hβ, rfl⟩ := hprod α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K)) =
      ((MulAut.conj g * β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K))
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner (suzukiGroup a K))
      (MulAut.conj g)).2 ⟨g, rfl⟩, one_mul]
  have hker : η.ker ≤ π.ker := by
    intro β hβ
    obtain ⟨c, hc⟩ := (scalarNormalizerFieldPart_eq_one_iff _).1 (MonoidHom.mem_ker.1 hβ)
    set α := MulAut.congr ι (r β)
    have hαq : ∀ x, (suzukiQuotAction α : K →ₗ[ZMod 2] K) x = c * (1 : K ≃+* K) x := hc
    have hαz := hΨres α c 1 hαq
    have hαapply : ∀ p, α p = ι (r β (ι.symm p)) := fun p => rfl
    have hrβ : ∀ y : suzukiU a K, ((r β y : suzukiU a K) : suzukiGroup a K) =
        (β : MulAut (suzukiGroup a K)) y := fun y => rfl
    have hcθ : (c : K) * φ c = (c : K) ^ (2 ^ (a + 1) + 1) := by
      rw [hφ]
      exact (pow_succ' _ _).symm
    have hβZ : ∀ z : K, (β : MulAut (suzukiGroup a K)) (suzukiSElt a K 0 z) =
        suzukiSElt a K 0 ((c : K) ^ (2 ^ (a + 1) + 1) * z) := by
      intro z
      have h0 : ∀ w : K, ((ι.symm ⟨0, w⟩ : suzukiU a K) : suzukiGroup a K) =
          suzukiSElt a K 0 w := by
        intro w
        rw [hιsymm, zero_pow (Nat.succ_ne_zero _), add_zero]
      have h1 := congrArg (fun p => ((ι.symm p : suzukiU a K) : suzukiGroup a K)) (hαz z)
      simp only [hαapply, MulEquiv.symm_apply_apply, hrβ, h0] at h1
      rw [h1, RingAut.one_apply, hcθ]
    have hβfst : ∀ u v : K, ∃ w : K,
        (β : MulAut (suzukiGroup a K)) (suzukiSElt a K u v) = suzukiSElt a K (c * u) w := by
      intro u v
      obtain ⟨u', w, huw⟩ := (mem_suzukiU_iff hK).1
        (r β ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩).2
      refine ⟨w, ?_⟩
      rw [← hrβ ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩, ← huw]
      have e1 : r β ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩ =
          ⟨suzukiSElt a K u' w, suzukiSElt_mem_suzukiU a K u' w⟩ := Subtype.ext huw.symm
      have e2 := hΨfst α (ι ⟨suzukiSElt a K u v, suzukiSElt_mem_suzukiU a K u v⟩)
      rw [hαapply, MulEquiv.symm_apply_apply, e1] at e2
      simp only [hι, hαq, RingAut.one_apply] at e2
      exact congrArg₂ (suzukiSElt a K) e2.symm rfl
    set d := suzukiDElt a K c with hd
    set γ := MulAut.conj d * (β : MulAut (suzukiGroup a K)) with hγ
    have hγapply : ∀ x, γ x = d * (β : MulAut (suzukiGroup a K)) x * d⁻¹ := fun x => rfl
    have hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K := by
      have hdU : (suzukiU a K).map (MulAut.conj d).toMonoidHom = suzukiU a K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1
          (suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K c))
      rw [hγ, show (MulAut.conj d * (β : MulAut (suzukiGroup a K))).toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp (β : MulAut (suzukiGroup a K)).toMonoidHom from rfl,
        ← Subgroup.map_map, β.2.1, hdU]
    have hγZ : ∀ v ∈ suzukiZ0 a K, γ v = v := by
      intro v hv
      obtain ⟨z, rfl⟩ := (mem_suzukiZ0_iff hK).1 hv
      rw [hγapply, hβZ, hd, suzukiDElt_conj' hK, mul_zero, Units.val_inv_eq_inv_val, inv_pow,
        inv_mul_cancel_left₀ (pow_ne_zero _ c.ne_zero)]
    have hγUZ : ∀ x ∈ suzukiU a K, x⁻¹ * γ x ∈ suzukiZ0 a K := by
      intro x hx
      obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
      obtain ⟨w, hw⟩ := hβfst u v
      rw [hγapply, hw, hd, suzukiDElt_conj' hK, Units.val_inv_eq_inv_val,
        inv_mul_cancel_left₀ c.ne_zero, suzukiSElt_inv hK, suzukiSElt_mul hK, mem_suzukiZ0_iff hK]
      exact ⟨_, congrArg₂ (suzukiSElt a K) (CharTwo.add_self_eq_zero u).symm rfl⟩
    obtain ⟨b, -, hb⟩ := suzukiU_layer_kernel ha hK γ hγU hγZ hγUZ
    have hβb : (β : MulAut (suzukiGroup a K)) = MulAut.conj (d⁻¹ * b) := by
      rw [map_mul, ← hb, hγ, map_inv, inv_mul_cancel_left]
    exact MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff (N := inner (suzukiGroup a K)) _).2
      ⟨d⁻¹ * b, hβb.symm⟩)
  obtain ⟨hcardAut, hcycAut⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  set θ : η.range →* Outer (suzukiGroup a K) :=
    (QuotientGroup.lift η.ker π hker).comp (QuotientGroup.quotientKerEquivRange η).symm.toMonoidHom
    with hθ
  have hθs : Function.Surjective θ := by
    intro q
    obtain ⟨β, rfl⟩ := hπs q
    refine ⟨QuotientGroup.quotientKerEquivRange η (β : C ⧸ η.ker), ?_⟩
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
  have : IsCyclic (RingAut K) := hcycAut
  refine ⟨isCyclic_of_surjective θ hθs, ?_⟩
  refine (Subgroup.card_dvd_of_surjective hθs).trans ?_
  rw [← hcardAut]
  exact Subgroup.card_subgroup_dvd_card _

theorem isCyclic_card_dvd_of_injective {X Y : Type*} [Group X] [Group Y] {n : ℕ}
    (hY : IsCyclic Y ∧ Nat.card Y ∣ n) (f : X →* Y) (hf : Function.Injective f) :
    IsCyclic X ∧ Nat.card X ∣ n :=
  have := hY.1
  ⟨isCyclic_of_injective f hf, (Subgroup.card_dvd_of_injective f hf).trans hY.2⟩

theorem Suzuki_model_and_perfect_cover_outer_cyclicity
    (H : Type) [Group H] (p f : ℕ)
    (h : SuzukiModel H p f) :
    (IsCyclic (Outer H) ∧ Nat.card (Outer H) ∣ f ∧ Odd (Nat.card (Outer H))) ∧
    ∀ (J : Type u) [Group J] [Group.IsPerfect J], Nonempty (J ⧸ Subgroup.center J ≃* H) →
      IsCyclic (Outer J) ∧ Nat.card (Outer J) ∣ f ∧ Odd (Nat.card (Outer J)) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hodd : Odd (2 * a + 1) := odd_two_mul_add_one a
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism e
  have hH : IsCyclic (Outer H) ∧ Nat.card (Outer H) ∣ 2 * a + 1 :=
    isCyclic_card_dvd_of_injective (suzukiGroup_outer_isCyclic_card_dvd ha hK) E.toMonoidHom
      E.injective
  refine ⟨⟨hH.1, hH.2, hodd.of_dvd_nat hH.2⟩, fun J _ _ ⟨eJ⟩ => ?_⟩
  obtain ⟨⟨EJ, -⟩, -⟩ := outer_isomorphism eJ
  have hJ := isCyclic_card_dvd_of_injective hH (EJ.toMonoidHom.comp (outerCenterQuotientHom J))
    (EJ.injective.comp (perfect_central_quotient_Schreier J).1)
  exact ⟨hJ.1, hJ.2, hodd.of_dvd_nat hJ.2⟩

end CFSG.LieType.Suzuki
