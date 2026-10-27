module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeCommonField

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Ree.ReeTag

namespace LargeReeCatalog

variable (K : Type) [Field K] in
@[expose] def unitsPairRingAut : RingAut K →* MulAut (Kˣ × Kˣ) where
  toFun σ := MulEquiv.prodCongr (unitsRingAut K σ) (unitsRingAut K σ)
  map_one' := MulEquiv.ext fun _ => Prod.ext (Units.ext rfl) (Units.ext rfl)
  map_mul' _ _ := MulEquiv.ext fun _ => Prod.ext (Units.ext rfl) (Units.ext rfl)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem exists_largeReeCoord_apply_suzuki [Module (ZMod 2) K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K}
    {e : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≃* SuzukiA K σ}
    (he : ∀ (t v : K) (h : largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩),
      e ⟨_, h⟩ = ⟨t, v + t * σ t⟩)
    (α : largeReeOppAut K a) (s v : K) :
    ∃ s' w, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeCoord a K s v,
        largeReeCoord_mem_reeGamma hK s v⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeCoord a K s' w ∧
      MulAut.congr e (largeReeRestrictU2 ha hK α) ⟨s, v + s * σ s⟩ = ⟨s', w + s' * σ s'⟩ := by
  obtain ⟨s', w, hsw⟩ := exists_largeReeCoord_eq hK
    (largeReeRestrictU2 ha hK α ⟨_, largeReeCoord_mem hK s v⟩).2
  have h3 : largeReeRestrictU2 ha hK α ⟨_, largeReeCoord_mem hK s v⟩ =
      ⟨largeReeCoord a K s' w, largeReeCoord_mem hK s' w⟩ := Subtype.ext hsw.symm
  refine ⟨s', w, (coe_largeReeRestrictU2 ha hK α _).symm.trans (congrArg Subtype.val h3), ?_⟩
  rw [← he s v (largeReeCoord_mem hK s v), MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h3, he]

theorem eq_one_of_isLargeReeParam_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : largeReeOppAut K a) (hα : IsLargeReeParam a hK α (1, 1, 1)) : α = 1 := by
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  let _ : Module (ZMod 2) K := Module.compHom K (ZMod.castHom (dvd_refl 2) K)
  have h2 : (2 : K) = 0 := F4_two_eq_zero
  obtain ⟨ρ, σ, hρ, hσ, -, hσρ, -, h4⟩ := large_Ree_field_powers a K hK
  have hρσ : ∀ c, ρ (σ c) = c := fun c => congrArg (fun e : K ≃+* K => e c) hσρ
  have hσ' : ∀ c, σ c = largeReeSigma a c := fun c => by rw [hσ, largeReeSigma]
  obtain ⟨e, he⟩ := exists_mulEquiv_suzukiA hK σ hσ'
  obtain ⟨-, -, -, ⟨E, hE⟩, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK σ (h4 ha)
  have hker : MulAut.congr e (largeReeRestrictU2 ha hK α) ∈
      (suzukiQuotAction (K := K) (φ := σ)).ker := by
    rw [MonoidHom.mem_ker]
    refine Units.ext (LinearMap.ext fun x => ?_)
    have key := suzukiQuotAction_largeRee ha hK he α hα.2.2 x
    rw [Units.val_one, one_mul] at key
    exact key
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : K →+ K, ∀ x z,
      MulAut.congr e (largeReeRestrictU2 ha hK α) ⟨x, z⟩ = ⟨x, z + ℓ x⟩ := by
    refine ⟨Multiplicative.toAdd (E.symm ⟨_, hker⟩), fun x z => ?_⟩
    have h := hE (Multiplicative.toAdd (E.symm ⟨_, hker⟩)) x z
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at h
    exact h
  have hu : ∀ s v, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeCoord a K s v,
      largeReeCoord_mem_reeGamma hK s v⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
        largeReeCoord a K s (v + ℓ s) := fun s v => by
    obtain ⟨s', w, h1, h3⟩ := exists_largeReeCoord_apply_suzuki ha hK he α s v
    rw [hℓ] at h3
    obtain ⟨hs, hw⟩ := BinExt.mk.inj h3
    subst hs
    rw [h1]
    congr 1
    linear_combination hw.symm
  have hh : ∀ t, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ :
      F4.reeGamma K a) : ModGL F4.tag K) = largeReeA1H a t := fun t => hα.2.1 t
  have hℓmul : ∀ (t : Kˣ) (s : K),
      ℓ (((t : K) ^ 2 ^ a)⁻¹ * s) = ((t : K) * (t : K) ^ 2 ^ a)⁻¹ * ℓ s := fun t s => by
    have hconj : (⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) *
        ⟨largeReeCoord a K s 0, largeReeCoord_mem_reeGamma hK s 0⟩ *
        (⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a)⁻¹ =
          ⟨largeReeCoord a K (((t : K) ^ 2 ^ a)⁻¹ * s) (((t : K) * (t : K) ^ 2 ^ a)⁻¹ * 0),
            largeReeCoord_mem_reeGamma hK _ _⟩ :=
      Subtype.ext (largeReeA1H_conj_largeReeCoord hK t s 0)
    have h1 := congrArg (fun g => (((α : MulAut (F4.reeGamma K a)) g : F4.reeGamma K a) :
      ModGL F4.tag K)) hconj
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hh, hu, hu] at h1
    have h3 := (largeReeCoord_injective
      ((largeReeA1H_conj_largeReeCoord hK t s (0 + ℓ s)).symm.trans h1)).2
    linear_combination h3.symm
  have hform : ∀ s, ℓ s = s * σ s * ℓ 1 := fun s => by
    by_cases hs : s = 0
    · rw [hs, map_zero, map_zero, zero_mul, zero_mul]
    have hσs : σ s ≠ 0 := (map_ne_zero σ).2 hs
    have h := hℓmul (Units.mk0 (σ s)⁻¹ (inv_ne_zero hσs)) 1
    have e1 : ((Units.mk0 (σ s)⁻¹ (inv_ne_zero hσs) : Kˣ) : K) ^ 2 ^ a = s⁻¹ := by
      rw [Units.val_mk0, ← hρ, map_inv₀, hρσ]
    rw [e1, Units.val_mk0, inv_inv, mul_one] at h
    rw [h, mul_inv, inv_inv, inv_inv]
    ring
  obtain ⟨s₀, hs₀⟩ : ∃ s, σ s ≠ s := by
    by_contra hcon
    have h1 : σ = 1 := RingEquiv.ext fun s => not_not.1 fun h => hcon ⟨s, h⟩
    exact h4 ha (by rw [h1, one_pow])
  have hc : ℓ 1 = 0 := by
    have hadd := map_add ℓ s₀ 1
    rw [hform (s₀ + 1), hform s₀, hform 1, map_add, map_one] at hadd
    have h0 : (s₀ + σ s₀) * ℓ 1 = 0 := by linear_combination hadd
    have hne : s₀ + σ s₀ ≠ 0 := fun h0' => hs₀ (by linear_combination h0' - s₀ * h2)
    exact (mul_eq_zero.1 h0).resolve_left hne
  refine eq_one_of_forall_fix ha hK α (fun c => ?_) fun g => Subtype.ext ?_
  · rw [hα.1 c, Units.val_one, one_mul]
    rfl
  · obtain ⟨s, v, hsv⟩ := exists_largeReeCoord_eq hK g.2
    rw [coe_largeReeRestrictU2]
    refine (coe_apply_congr (α : MulAut (F4.reeGamma K a)) hsv.symm _
      (largeReeCoord_mem_reeGamma hK s v)).trans ((hu s v).trans ?_)
    rw [hform, hc, mul_zero, add_zero]
    exact hsv

end LargeReeCatalog

open LargeReeCatalog

theorem large_Ree_opposite_Sylow_parameters_faithful (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ Φ : largeReeOppAut K a →* (Kˣ × Kˣ) ⋊[unitsPairRingAut K] RingAut K,
      (∀ (α : largeReeOppAut K a) (p : Kˣ × Kˣ × (K ≃+* K)),
        (∀ (c : K) (hc : largeReeA1X a c ∈ F4.reeGamma K a),
          (((α : MulAut (F4.reeGamma K a)) ⟨_, hc⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
            largeReeA1X a (p.1 * p.2.2 c)) →
        (∀ (t : Kˣ) (ht : largeReeA1H a t ∈ F4.reeGamma K a),
          (((α : MulAut (F4.reeGamma K a)) ⟨_, ht⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
            largeReeA1H a (Units.map p.2.2.toMonoidHom t)) →
        (∀ (s v : K) (hsv : largeReeCoord a K s v ∈ F4.reeGamma K a), ∃ w : K,
          (((α : MulAut (F4.reeGamma K a)) ⟨_, hsv⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
            largeReeCoord a K (p.2.1 * p.2.2 s) w) →
        Φ α = ⟨(p.1, p.2.1), p.2.2⟩) ∧
      Function.Injective Φ ∧
      Nat.card (largeReeOppAut K a) ∣ (2 ^ (2 * a + 1) - 1) ^ 2 * (2 * a + 1) ∧
      Odd (Nat.card (largeReeOppAut K a)) := by
  classical
  choose P hP using exists_isLargeReeParam ha hK
  have hPmul : ∀ α γ : largeReeOppAut K a, P (α * γ) =
      ((P α).1 * Units.map (P α).2.2.toMonoidHom (P γ).1,
        (P α).2.1 * Units.map (P α).2.2.toMonoidHom (P γ).2.1, (P α).2.2 * (P γ).2.2) :=
    fun α γ => (hP (α * γ)).unique ((hP α).mul (hP γ))
  have hP1 : P 1 = (1, 1, 1) := (hP 1).unique (isLargeReeParam_one hK)
  let Φ : largeReeOppAut K a →* (Kˣ × Kˣ) ⋊[unitsPairRingAut K] RingAut K :=
    { toFun := fun α => ⟨((P α).1, (P α).2.1), (P α).2.2⟩
      map_one' := by
        simp only [hP1]
        rfl
      map_mul' := fun α γ => by
        rw [hPmul]
        rfl }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have h1 : P α = (1, 1, 1) := by
      have e := SemidirectProduct.ext_iff.1 hα
      have e1 : ((P α).1, (P α).2.1) = ((1 : Kˣ), (1 : Kˣ)) := e.1
      have e2 : (P α).2.2 = 1 := e.2
      obtain ⟨e1a, e1b⟩ := Prod.mk.inj e1
      exact Prod.ext e1a (Prod.ext e1b e2)
    have h := hP α
    rw [h1] at h
    exact eq_one_of_isLargeReeParam_one ha hK α h
  have hcard := Subgroup.card_dvd_of_injective Φ hΦ
  rw [SemidirectProduct.card, Nat.card_prod, Nat.card_units, hK,
    (card_ringAut_and_isCyclic Nat.prime_two K hK).1, ← sq] at hcard
  have hodd : Odd ((2 ^ (2 * a + 1) - 1) ^ 2 * (2 * a + 1)) := by
    refine Odd.mul (Odd.pow ?_) (odd_two_mul_add_one a)
    have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    have h2 : Even (2 ^ (2 * a + 1)) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd h1 h2 odd_one
  refine ⟨Φ, fun α p hx hh hu => ?_, hΦ, hcard, hodd.of_dvd_nat hcard⟩
  have hp : P α = p := (hP α).unique ⟨fun c => hx c _, fun t => hh t _, fun s v => hu s v _⟩
  change (⟨((P α).1, (P α).2.1), (P α).2.2⟩ : (Kˣ × Kˣ) ⋊[unitsPairRingAut K] RingAut K) = _
  rw [hp]

end CFSG.ComponentClassification.UnbalancedCatalog
