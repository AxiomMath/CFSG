module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.Open.StatedCenterThree

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

theorem ringAut_pow_apply {K : Type} [Field K] (σ : K ≃+* K) (n : ℕ) (c : K) :
    (σ ^ n) c = (⇑σ)^[n] c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ]
    exact (ih _).trans rfl

theorem ringAut_apply_eq_of_pow_three {K : Type} [Field K] (σ : K ≃+* K) (hσ : σ ^ 3 = 1) {z : K}
    (hz : z ^ 3 = 1) : σ z = z := by
  by_contra hne
  have hz1 : z ≠ 1 := fun h => hne (by rw [h, map_one])
  have hq : z ^ 2 + z + 1 = 0 := by
    have h1 : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hz1)
  have hw3 : (σ z) ^ 3 = 1 := by rw [← map_pow, hz, map_one]
  have hw1 : σ z ≠ 1 := fun h => hz1 (σ.injective (by rw [h, map_one]))
  have hqw : (σ z) ^ 2 + σ z + 1 = 0 := by
    have h1 : (σ z - 1) * ((σ z) ^ 2 + σ z + 1) = 0 := by linear_combination hw3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hw1)
  have hprod : (σ z - z) * (σ z + z + 1) = 0 := by linear_combination hqw - hq
  have hw : σ z = z ^ 2 := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linear_combination h - hq
  have hσσ : σ (σ z) = z := by
    rw [hw, map_pow, hw]
    linear_combination z * hz
  have h3 : (σ ^ 3) z = z := by rw [hσ]; rfl
  rw [ringAut_pow_apply] at h3
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq] at h3
  rw [hσσ] at h3
  exact hne h3

section Model


theorem minBC_comp {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ι : k →+* k') (ι' : k' →+* k'') :
    (minBC e6Data_valid ι').comp (minBC e6Data_valid ι) = minBC e6Data_valid (ι'.comp ι) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
  rintro _ ⟨i, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply]
    rw [minBC_xm_single, minBC_xm_single, minBC_xm_single]
    rfl
  · simp only [MonoidHom.comp_apply]
    rw [minBC_xm_neg_single, minBC_xm_neg_single, minBC_xm_neg_single]
    rfl

theorem minBC_id {k : Type} [Field k] :
    minBC e6Data_valid (RingHom.id k) = MonoidHom.id (e6Data_valid.minGroup k) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
  rintro _ ⟨i, c, rfl | rfl⟩
  · rw [minBC_xm_single]
    rfl
  · rw [minBC_xm_neg_single]
    rfl

@[expose] def minBCAut {K : Type} [Field K] (σ : K ≃+* K) : MulAut (e6Data_valid.minGroup K) :=
  MonoidHom.toMulEquiv (minBC e6Data_valid σ.toRingHom) (minBC e6Data_valid σ.symm.toRingHom)
    (by
      rw [minBC_comp, ← minBC_id]
      congr 1
      ext c
      exact σ.symm_apply_apply c)
    (by
      rw [minBC_comp, ← minBC_id]
      congr 1
      ext c
      exact σ.apply_symm_apply c)

theorem minBCAut_apply {K : Type} [Field K] (σ : K ≃+* K) (x : e6Data_valid.minGroup K) :
    minBCAut σ x = minBC e6Data_valid σ.toRingHom x := rfl

section Torus

variable {k k' : Type} [Field k] [Field k'] (ι : k →+* k')

theorem minBC_nt (a : Fin Tag.E6.rank) (t : kˣ) :
    minBC e6Data_valid ι (e6Data_valid.nt k a t) = e6Data_valid.nt k' a (Units.map (ι : k →* k') t) := by
  change minBC e6Data_valid ι (e6Data_valid.xm k (Pi.single a 1) t *
      e6Data_valid.xm k (-Pi.single a 1) (-((t⁻¹ : kˣ) : k)) * e6Data_valid.xm k (Pi.single a 1) t) =
    e6Data_valid.xm k' (Pi.single a 1) ((Units.map (ι : k →* k') t : k'ˣ) : k') *
      e6Data_valid.xm k' (-Pi.single a 1) (-((((Units.map (ι : k →* k') t)⁻¹ : k'ˣ)) : k')) *
        e6Data_valid.xm k' (Pi.single a 1) ((Units.map (ι : k →* k') t : k'ˣ) : k')
  rw [map_mul, map_mul, minBC_xm_single, minBC_xm_neg_single]
  have h1 : ι (-((t⁻¹ : kˣ) : k)) = -((((Units.map (ι : k →* k') t)⁻¹ : k'ˣ)) : k') := by
    rw [map_neg, ← map_inv (Units.map (ι : k →* k')) t, Units.coe_map]
    rfl
  rw [h1]
  rfl

theorem minBC_hm (a : Fin Tag.E6.rank) (t : kˣ) :
    minBC e6Data_valid ι (e6Data_valid.hm k a t) = e6Data_valid.hm k' a (Units.map (ι : k →* k') t) := by
  change minBC e6Data_valid ι (e6Data_valid.nt k a t * (e6Data_valid.nt k a 1)⁻¹) =
    e6Data_valid.nt k' a (Units.map (ι : k →* k') t) * (e6Data_valid.nt k' a 1)⁻¹
  rw [map_mul, map_inv, minBC_nt, minBC_nt, map_one]

theorem minBC_minTorus (u : Fin Tag.E6.rank → kˣ) :
    minBC e6Data_valid ι (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k' (fun i => Units.map (ι : k →* k') (u i)) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun i => Units.map (ι : k →* k') ((1 : Fin Tag.E6.rank → kˣ) i)) = 1 := by
      funext i
      exact map_one _
    rw [e]
    simp only [map_one]
  | hmul t t' ht ht' =>
    have e : (fun i => Units.map (ι : k →* k') ((t * t') i)) =
        (fun i => Units.map (ι : k →* k') (t i)) * (fun i => Units.map (ι : k →* k') (t' i)) := by
      funext i
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun i => Units.map (ι : k →* k') ((Pi.mulSingle a s : Fin Tag.E6.rank → kˣ) i)) =
        Pi.mulSingle a (Units.map (ι : k →* k') s) := by
      funext i
      by_cases h : i = a
      · subst h
        simp
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [minTorus_mulSingle, e, minTorus_mulSingle, minBC_hm]

end Torus

section Elem

variable {K : Type} [Field K] [Finite K]

@[expose] def torusHom3 (K : Type) [Field K] :
    (Fin Tag.E6.rank → rootsOfUnity 3 K) →* e6Data_valid.minGroup K :=
  (minTorus e6Data_valid K).comp
    (Pi.monoidHom fun i => (rootsOfUnity 3 K).subtype.comp
      (Pi.evalMonoidHom (fun _ => rootsOfUnity 3 K) i))

theorem torusHom3_apply (v : Fin Tag.E6.rank → rootsOfUnity 3 K) :
    torusHom3 K v = minTorus e6Data_valid K (fun i => ((v i : rootsOfUnity 3 K) : Kˣ)) := rfl

theorem torusHom3_injective : Function.Injective (torusHom3 K) := by
  intro v w h
  have h' : minTorus e6Data_valid K (fun i => ((v i : rootsOfUnity 3 K) : Kˣ)) =
      minTorus e6Data_valid K (fun i => ((w i : rootsOfUnity 3 K) : Kˣ)) := h
  have h1 := minTorus_injective e6Data_valid K h'
  funext i
  exact Subtype.ext (congrFun h1 i)

theorem exists_torus3_E6 (h3 : 3 ∣ Nat.card K - 1) {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    ∃ E : Subgroup (e6Data_valid.minGroup K),
      E ≤ MonoidHom.eqLocus (minBCAut σ).toMonoidHom (MonoidHom.id _) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 6 := by
  have hμcard : Nat.card (rootsOfUnity 3 K) = 3 := CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3
  have hμ3 : ∀ z : rootsOfUnity 3 K, z ^ 3 = 1 := fun z => Subtype.ext ((mem_rootsOfUnity 3 _).1 z.2)
  refine ⟨(torusHom3 K).range, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨v, rfl⟩
    show minBC e6Data_valid σ.toRingHom (torusHom3 K v) = torusHom3 K v
    rw [torusHom3_apply, minBC_minTorus]
    congr 2
    funext i
    refine Units.ext ?_
    exact ringAut_apply_eq_of_pow_three σ hσ (by
      have := congrArg (fun z : rootsOfUnity 3 K => (((z : Kˣ)) : K)) (hμ3 (v i))
      simpa using this)
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show torusHom3 K a * torusHom3 K b = torusHom3 K b * torusHom3 K a
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro x ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := funext fun i => by simpa using hμ3 (a i)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective torusHom3_injective).toEquiv.symm, Nat.card_fun, hμcard,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl

end Elem

section Isog

variable {K : Type} [Field K] [Finite K]

theorem e6Isogeny_minBCAut (σ : K ≃+* K) (x : e6Data_valid.minGroup K) :
    e6Isogeny K (minBCAut σ x) = entrywiseAdjointAut Tag.E6 σ (e6Isogeny K x) := by
  refine Subtype.ext ?_
  rw [minBCAut_apply, e6Isogeny_minBC σ.toRingHom x, coe_entrywiseAdjointAut,
    units_map_entrywiseHom_eq_baseChangeGL]

end Isog

end Model

end CFSG.LieType.SemisimpleCentralizers.HeldLang
