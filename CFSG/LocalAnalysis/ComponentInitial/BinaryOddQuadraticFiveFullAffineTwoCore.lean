module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveOrthogonalGroup
public import CFSG.Assembly.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection Orth

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E}

namespace FullAffine

theorem aff_apply (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) (x : E × ZMod 2) :
    k x = k.linear x + k 0 := by
  have h := congrFun (AffineMap.decomp k.toAffineMap) x
  simpa using h

theorem eq_toAffineEquiv_of_apply_zero {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (h : k 0 = 0) : k = k.linear.toAffineEquiv :=
  AffineEquiv.ext fun x => by
    rw [aff_apply, h, add_zero]
    rfl

abbrev tr (v : E × ZMod 2) : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) :=
  AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) v

theorem tr_apply (v x : E × ZMod 2) : tr v x = v + x :=
  rfl

theorem tr_add (v w : E × ZMod 2) : tr (v + w) = tr v * tr w :=
  AffineEquiv.ext fun x => by
    rw [AffineEquiv.coe_mul, Function.comp_apply, tr_apply, tr_apply, tr_apply, add_assoc]

theorem tr_zero : tr (0 : E × ZMod 2) = 1 :=
  AffineEquiv.ext fun x => by
    rw [tr_apply, zero_add]
    rfl

theorem tr_rV_mul_self : tr (rV : E × ZMod 2) * tr rV = 1 := by
  rw [← tr_add, add_self_eq_zero_zmod_two, tr_zero]

theorem conj_tr (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) (v : E × ZMod 2) :
    k * tr v * k⁻¹ = tr (k.linear v) :=
  AffineEquiv.ext fun x => by
    change k (v + k.symm x) = k.linear v + x
    rw [aff_apply k, map_add, add_assoc, ← aff_apply k, AffineEquiv.apply_symm_apply]

@[expose] def toAff :
    ((E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)) →* ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) where
  toFun g := g.toAffineEquiv
  map_one' := AffineEquiv.ext fun _ => rfl
  map_mul' _ _ := AffineEquiv.ext fun _ => rfl

theorem toAff_eq (g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)) : toAff g = g.toAffineEquiv :=
  rfl

@[expose] def twoCoreLin (b : LinearMap.BilinForm (ZMod 2) E) (lam : ZMod 2)
    (A : E × ZMod 2) : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2) :=
  LinearEquiv.ofInvolutive
    { toFun := fun B => B + (lam * b A.1 B.1) • rV
      map_add' := fun B B' => by
        simp only [Prod.fst_add, map_add, mul_add, add_smul]
        abel
      map_smul' := fun c B => by
        simp only [Prod.smul_fst, map_smul, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
        ring_nf }
    fun B => by
      change B + (lam * b A.1 B.1) • rV + (lam * b A.1 (B + (lam * b A.1 B.1) • rV).1) • rV = B
      simp only [Prod.fst_add, Prod.smul_fst, rV, smul_zero, add_zero]
      rw [add_assoc, add_self_eq_zero_zmod_two, add_zero]

@[expose] def twoCoreMap (b : LinearMap.BilinForm (ZMod 2) E) (lam : ZMod 2)
    (A : E × ZMod 2) : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) :=
  tr A * toAff (twoCoreLin b lam A)

theorem twoCoreMap_apply (b : LinearMap.BilinForm (ZMod 2) E) (lam : ZMod 2)
    (A B : E × ZMod 2) : twoCoreMap b lam A B = B + A + (lam * b A.1 B.1) • rV := by
  change A + (B + (lam * b A.1 B.1) • rV) = _
  abel

theorem twoCoreMap_mul (b : LinearMap.BilinForm (ZMod 2) E) (lam : ZMod 2)
    (A A' : E × ZMod 2) : twoCoreMap b lam A * twoCoreMap b lam A' =
      twoCoreMap b lam (A + A' + (lam * b A.1 A'.1) • rV) :=
  AffineEquiv.ext fun B => by
    rw [AffineEquiv.coe_mul, Function.comp_apply, twoCoreMap_apply, twoCoreMap_apply,
      twoCoreMap_apply]
    simp only [Prod.fst_add, Prod.smul_fst, rV, smul_zero, add_zero, map_add,
      LinearMap.add_apply]
    module

@[expose] def twoCoreGroup (hb : b.IsAlt) (lam : ZMod 2) :
    Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) where
  carrier := Set.range (twoCoreMap b lam)
  one_mem' := ⟨0, AffineEquiv.ext fun B => by
    rw [twoCoreMap_apply]
    simp⟩
  mul_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨A', rfl⟩
    exact ⟨_, (twoCoreMap_mul b lam A A').symm⟩
  inv_mem' := by
    rintro _ ⟨A, rfl⟩
    refine ⟨A, eq_inv_of_mul_eq_one_left ?_⟩
    rw [twoCoreMap_mul, hb.self_eq_zero, mul_zero, zero_smul, add_zero,
      add_self_eq_zero_zmod_two]
    exact AffineEquiv.ext fun B => by
      rw [twoCoreMap_apply]
      simp

theorem mem_twoCoreGroup (hb : b.IsAlt) (lam : ZMod 2)
    {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} :
    p ∈ twoCoreGroup hb lam ↔ ∃ A, twoCoreMap b lam A = p :=
  Iff.rfl

structure AffHyp (Q : QuadraticForm (ZMod 2) E)
    (K : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))) : Prop where
  trans : ∀ x y : E × ZMod 2, ∃ k ∈ K, k x = y
  stab : ∀ g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2),
    toAff g ∈ K ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q)

variable {K : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))}

theorem linear_mem_of_apply_zero (hK : AffHyp Q K) {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hk : k ∈ K) (h0 : k 0 = 0) :
    k.linear ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) := by
  rw [← hK.stab, toAff_eq, ← eq_toAffineEquiv_of_apply_zero h0]
  exact hk

theorem toAff_hEquiv_mem (hQ : QuadraticMap.polarBilin Q = b) (hK : AffHyp Q K)
    (s : bilinIsometryGroup b) : toAff (hEquiv hQ s) ∈ K :=
  (hK.stab _).mpr (hEquiv_mem hQ s)

theorem finite_aff [Finite E] : Finite ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) :=
  Finite.of_injective _ AffineEquiv.coeFn_injective

theorem card_V [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4) :
    Nat.card (E × ZMod 2) = 32 := by
  rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := ZMod 2), hE, Nat.card_zmod]
  norm_num

theorem four_lt_card [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4) :
    4 < Nat.card E := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hE, Nat.card_zmod]
  norm_num

theorem card_K [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (hK : AffHyp Q K) : Nat.card K = 23040 := by
  choose g hgK hg using fun A : E × ZMod 2 => hK.trans 0 A
  let e1 : K ≃ (E × ZMod 2) × {k : K // (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) 0 = 0} :=
    { toFun := fun k => (k.1 0, ⟨⟨(g (k.1 0))⁻¹ * k.1, K.mul_mem (K.inv_mem (hgK _)) k.2⟩, by
        change (g (k.1 0)).symm (k.1 0) = 0
        rw [AffineEquiv.symm_apply_eq, hg]⟩)
      invFun := fun p => ⟨g p.1 * p.2.1.1, K.mul_mem (hgK _) p.2.1.2⟩
      left_inv := fun k => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun p => by
        obtain ⟨A, ⟨k, hk⟩, hk0⟩ := p
        have h1 : (g A * k) 0 = A := by
          rw [AffineEquiv.coe_mul, Function.comp_apply, hk0, hg]
        refine Prod.ext h1 (Subtype.ext (Subtype.ext ?_))
        change (g ((g A * k) 0))⁻¹ * (g A * k) = k
        rw [h1, inv_mul_cancel_left] }
  let e2 : {k : K // (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) 0 = 0} ≃
      TauCeti.QuadraticMap.orthogonalGroup (qForm Q) :=
    { toFun := fun k => ⟨k.1.1.linear, linear_mem_of_apply_zero hK k.1.2 k.2⟩
      invFun := fun g => ⟨⟨toAff g.1, (hK.stab _).mpr g.2⟩, map_zero g.1⟩
      left_inv := fun k => Subtype.ext (Subtype.ext (eq_toAffineEquiv_of_apply_zero k.2).symm)
      right_inv := fun g => rfl }
  rw [Nat.card_congr e1, Nat.card_prod, Nat.card_congr e2, card_orthogonalGroup_qForm hE hb hnd hQ,
    card_V hE]

theorem tr_rV_mem [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (hK : AffHyp Q K) : tr rV ∈ K := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have := finite_aff (E := E)
  obtain ⟨g, hgK, hg0⟩ := hK.trans 0 rV
  have hgr : g⁻¹ rV = 0 := by
    change g.symm rV = 0
    rw [AffineEquiv.symm_apply_eq, hg0]
  let stab : (E × ZMod 2) → Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) := fun x =>
    { carrier := {k | k x = x}
      one_mem' := rfl
      mul_mem' := fun {k k'} hk hk' => by
        change k (k' x) = x
        rw [show k' x = x from hk', show k x = x from hk]
      inv_mem' := fun {k} hk => by
        change k.symm x = x
        rw [AffineEquiv.symm_apply_eq]
        exact (show k x = x from hk).symm }
  let H' := (TauCeti.QuadraticMap.orthogonalGroup (qForm Q)).map toAff
  have hH'0 : H' = K ⊓ stab 0 := by
    ext k
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨(hK.stab g').mpr hg', map_zero g'⟩
    · rintro ⟨hk, hk0⟩
      exact ⟨k.linear, linear_mem_of_apply_zero hK hk hk0,
        (eq_toAffineEquiv_of_apply_zero hk0).symm⟩
  have hle : H' ≤ K ⊓ stab rV := by
    rintro _ ⟨g', hg', rfl⟩
    exact ⟨(hK.stab g').mpr hg', apply_rV_of_mem hnd hQ hg'⟩
  let e : (K ⊓ stab 0 : Subgroup _) ≃ (K ⊓ stab rV : Subgroup _) :=
    { toFun := fun k => ⟨g * k.1 * g⁻¹, K.mul_mem (K.mul_mem hgK k.2.1) (K.inv_mem hgK), by
        change g (k.1 (g⁻¹ rV)) = rV
        rw [hgr, show k.1 0 = 0 from k.2.2, hg0]⟩
      invFun := fun k => ⟨g⁻¹ * k.1 * g, K.mul_mem (K.mul_mem (K.inv_mem hgK) k.2.1) hgK, by
        change g⁻¹ (k.1 (g 0)) = 0
        rw [hg0, show k.1 rV = rV from k.2.2, hgr]⟩
      left_inv := fun k => Subtype.ext (by
        change g⁻¹ * (g * k.1 * g⁻¹) * g = k.1
        group)
      right_inv := fun k => Subtype.ext (by
        change g * (g⁻¹ * k.1 * g) * g⁻¹ = k.1
        group) }
  have hEq : H' = K ⊓ stab rV :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hH'0, Nat.card_congr e])
  have hlin : g.linear ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) := by
    refine mem_orthogonalGroup_of_normalizes hb hnd hQ (four_lt_card hE) g.linear fun s => ?_
    have hc : g * toAff (hEquiv hQ s) * g⁻¹ ∈ K ⊓ stab rV :=
      ⟨K.mul_mem (K.mul_mem hgK (toAff_hEquiv_mem hQ hK s)) (K.inv_mem hgK), by
        change g (hEquiv hQ s (g⁻¹ rV)) = rV
        rw [hgr, map_zero, hg0]⟩
    rw [← hEq] at hc
    obtain ⟨g', hg', hg'eq⟩ := hc
    have h1 := congrArg AffineEquiv.linear hg'eq
    change g' = g.linear * hEquiv hQ s * g.linear⁻¹ at h1
    rw [← h1]
    exact hg'
  have htr : tr rV = g * (toAff g.linear)⁻¹ := AffineEquiv.ext fun x => by
    change rV + x = g (g.linear.symm x)
    rw [aff_apply, LinearEquiv.apply_symm_apply, hg0, add_comm]
  rw [htr]
  exact K.mul_mem hgK (K.inv_mem ((hK.stab _).mpr hlin))

@[expose] def transSub (K : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))) :
    Submodule (ZMod 2) (E × ZMod 2) where
  carrier := {v | tr v ∈ K}
  add_mem' := fun {v w} hv hw => by
    change tr (v + w) ∈ K
    rw [tr_add]
    exact K.mul_mem hv hw
  zero_mem' := by
    change tr 0 ∈ K
    rw [tr_zero]
    exact K.one_mem
  smul_mem' := fun c v hv => by
    rcases zmod_two_cases c with rfl | rfl
    · change tr ((0 : ZMod 2) • v) ∈ K
      rw [zero_smul, tr_zero]
      exact K.one_mem
    · rwa [one_smul]

theorem mem_transSub {v : E × ZMod 2} : v ∈ transSub K ↔ tr v ∈ K :=
  Iff.rfl

theorem linear_rV [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (hK : AffHyp Q K) {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hk : k ∈ K) :
    k.linear rV = rV := by
  have hr := tr_rV_mem hE hb hnd hQ hK
  have hrV : (rV : E × ZMod 2) ≠ 0 := fun h => by
    have h1 := congrArg Prod.snd h
    simp [rV] at h1
  rcases invariant_submodule_V hb hnd hQ (four_lt_card hE) (transSub K) (fun s v hv => by
      rw [mem_transSub] at hv ⊢
      rw [show hEquiv hQ s v = (toAff (hEquiv hQ s)).linear v from rfl, ← conj_tr]
      exact K.mul_mem (K.mul_mem (toAff_hEquiv_mem hQ hK s) hv)
        (K.inv_mem (toAff_hEquiv_mem hQ hK s))) with hT | hT | hT
  · exfalso
    have h1 : rV ∈ transSub K := hr
    rw [hT, Submodule.mem_bot] at h1
    exact hrV h1
  · have h1 : k.linear rV ∈ transSub K := by
      rw [mem_transSub, ← conj_tr]
      exact K.mul_mem (K.mul_mem hk hr) (K.inv_mem hk)
    rw [hT, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd (k.linear.injective (hc.symm.trans (map_zero _).symm)) hrV
    · rw [← hc, one_smul]
  · have h1 : k 0 ∈ transSub K := hT ▸ Submodule.mem_top
    have hk' : (tr (k 0))⁻¹ * k ∈ K := K.mul_mem (K.inv_mem h1) hk
    have hk'0 : ((tr (k 0))⁻¹ * k) 0 = 0 := by
      change (tr (k 0)).symm (k 0) = 0
      rw [AffineEquiv.symm_apply_eq, tr_apply, add_zero]
    have h2 := apply_rV_of_mem hnd hQ (linear_mem_of_apply_zero hK hk' hk'0)
    exact h2

@[expose] def indE (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) : E →ₗ[ZMod 2] E :=
  (LinearMap.fst (ZMod 2) E (ZMod 2)) ∘ₗ k.linear.toLinearMap ∘ₗ (LinearMap.inl (ZMod 2) E (ZMod 2))

theorem indE_apply (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) (x : E) :
    indE k x = (k.linear (x, 0)).1 :=
  rfl

theorem linear_apply_of_rV {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hr : k.linear rV = rV)
    (B : E × ZMod 2) : k.linear B = k.linear (B.1, 0) + B.2 • rV := by
  conv_lhs => rw [eq_fst_add_smul_rV B]
  rw [map_add, map_smul, hr]

theorem fst_apply_of_rV {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hr : k.linear rV = rV)
    (B : E × ZMod 2) : (k B).1 = indE k B.1 + (k 0).1 := by
  rw [aff_apply, linear_apply_of_rV hr, Prod.fst_add, Prod.fst_add, indE_apply]
  simp [rV]

theorem indE_mul {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hr : k.linear rV = rV)
    (k' : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) (x : E) :
    indE (k * k') x = indE k (indE k' x) := by
  rw [indE_apply, indE_apply, indE_apply]
  change (k.linear (k'.linear (x, 0))).1 = _
  rw [linear_apply_of_rV hr (k'.linear (x, 0)), Prod.fst_add]
  simp [rV]

theorem eq_one_of_fst [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) (hK : AffHyp Q K)
    {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hk : k ∈ K) (h0 : k 0 = 0)
    (h : ∀ B, (k B).1 = B.1) : k = 1 := by
  obtain ⟨s, hs⟩ := exists_hEquiv_eq hnd hQ (linear_mem_of_apply_zero hK hk h0)
  have hs1 : s = 1 := Subtype.ext (gl_ext fun x => by
    have h1 := h (x, 0)
    rw [aff_apply, h0, add_zero, hs, hEquiv_apply] at h1
    exact h1)
  rw [eq_toAffineEquiv_of_apply_zero h0, hs, hs1, hEquiv_one]
  rfl

theorem fst_eq_iff [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (hK : AffHyp Q K) {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hk : k ∈ K) :
    (∀ B, (k B).1 = B.1) ↔ k = 1 ∨ k = tr rV := by
  constructor
  · intro h
    have h1 : (k 0).1 = 0 := h 0
    rcases zmod_two_cases (k 0).2 with h2 | h2
    · exact Or.inl (eq_one_of_fst hnd hQ hK hk (Prod.ext h1 h2) h)
    · right
      have hk' : tr rV * k ∈ K := K.mul_mem (tr_rV_mem hE hb hnd hQ hK) hk
      have hk'0 : (tr rV * k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) 0 = 0 := by
        change rV + k 0 = 0
        rw [show k 0 = rV from Prod.ext h1 h2, add_self_eq_zero_zmod_two]
      have h3 := eq_one_of_fst hnd hQ hK hk' hk'0 fun B => by
        change (rV + k B).1 = B.1
        rw [Prod.fst_add, h B]
        simp [rV]
      calc k = tr rV * tr rV * k := by rw [tr_rV_mul_self, one_mul]
        _ = tr rV := by rw [mul_assoc, h3, mul_one]
  · rintro (rfl | rfl) B
    · rfl
    · change (rV + B).1 = B.1
      simp [rV]

section Ind

variable [FiniteDimensional (ZMod 2) E] {hE : Module.finrank (ZMod 2) E = 4} {hb : b.IsAlt}
  {hnd : b.Nondegenerate} {hQ : QuadraticMap.polarBilin Q = b} {hK : AffHyp Q K}

variable (hE hb hnd hQ hK) in
@[expose] def indHom : K →* LinearMap.GeneralLinearGroup (ZMod 2) E :=
  MonoidHom.toHomUnits
    { toFun := fun k => indE k.1
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun k k' => LinearMap.ext fun x =>
        indE_mul (linear_rV hE hb hnd hQ hK k.2) k'.1 x }

variable (hE hb hnd hQ hK) in
@[expose] def pSub : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) :=
  (indHom hE hb hnd hQ hK).ker.map K.subtype

theorem mem_pSub {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} :
    p ∈ pSub hE hb hnd hQ hK ↔ p ∈ K ∧ ∀ x, indE p x = x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, fun x => ?_⟩
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) E =>
      (g : E →ₗ[ZMod 2] E) x) (MonoidHom.mem_ker.mp hk)
    exact h1
  · rintro ⟨hp, h⟩
    exact ⟨⟨p, hp⟩, MonoidHom.mem_ker.mpr (Units.ext (LinearMap.ext h)), rfl⟩

theorem pSub_le : pSub hE hb hnd hQ hK ≤ K := fun _ hp => (mem_pSub.mp hp).1

theorem tr_rV_mem_pSub : tr rV ∈ pSub hE hb hnd hQ hK :=
  mem_pSub.mpr ⟨tr_rV_mem hE hb hnd hQ hK, fun _ => rfl⟩

theorem fst_apply_of_mem_pSub {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (B : E × ZMod 2) : (p B).1 = B.1 + (p 0).1 := by
  rw [fst_apply_of_rV (linear_rV hE hb hnd hQ hK (mem_pSub.mp hp).1), (mem_pSub.mp hp).2]

theorem eq_one_of_mem_pSub {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (h0 : p 0 = 0) : p = 1 :=
  eq_one_of_fst hnd hQ hK (mem_pSub.mp hp).1 h0 fun B => by
    rw [fst_apply_of_mem_pSub hp, h0, Prod.fst_zero, add_zero]

theorem eq_of_mem_pSub {p p' : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (hp' : p' ∈ pSub hE hb hnd hQ hK) (h : p 0 = p' 0) :
    p = p' := by
  have h1 := eq_one_of_mem_pSub ((pSub hE hb hnd hQ hK).mul_mem
    ((pSub hE hb hnd hQ hK).inv_mem hp') hp) (by
      change p'.symm (p 0) = 0
      rw [AffineEquiv.symm_apply_eq, h])
  rw [← mul_inv_cancel_left p' p, h1, mul_one]

theorem conj_mem_pSub {k p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hk : k ∈ K)
    (hp : p ∈ pSub hE hb hnd hQ hK) : k * p * k⁻¹ ∈ pSub hE hb hnd hQ hK := by
  obtain ⟨hpK, hp1⟩ := mem_pSub.mp hp
  refine mem_pSub.mpr ⟨K.mul_mem (K.mul_mem hk hpK) (K.inv_mem hk), fun x => ?_⟩
  have hkr := linear_rV hE hb hnd hQ hK hk
  have hpr := linear_rV hE hb hnd hQ hK hpK
  rw [indE_mul (by rw [show (k * p).linear = k.linear * p.linear from rfl,
    LinearEquiv.mul_apply, hpr, hkr]), indE_mul hkr, hp1, ← indE_mul hkr, mul_inv_cancel]
  rfl

theorem indHom_toAff_hEquiv (s : bilinIsometryGroup b) :
    indHom hE hb hnd hQ hK ⟨toAff (hEquiv hQ s), toAff_hEquiv_mem hQ hK s⟩ = s :=
  Units.ext (LinearMap.ext fun _ => rfl)

theorem exists_mem_pSub_fst (e : E) :
    ∃ p ∈ pSub hE hb hnd hQ hK, (p 0).1 = e := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have := finite_aff (E := E)
  let P := pSub hE hb hnd hQ hK
  let TE : Submodule (ZMod 2) E :=
    { carrier := {e | ∃ p ∈ P, (p 0).1 = e}
      add_mem' := fun {e e'} ⟨p, hp, hpe⟩ ⟨p', hp', hpe'⟩ => ⟨p * p', P.mul_mem hp hp', by
        change (p (p' 0)).1 = e + e'
        rw [fst_apply_of_mem_pSub hp, hpe, hpe', add_comm]⟩
      zero_mem' := ⟨1, P.one_mem, rfl⟩
      smul_mem' := fun c e ⟨p, hp, hpe⟩ => by
        rcases zmod_two_cases c with rfl | rfl
        · exact ⟨1, P.one_mem, by rw [zero_smul]; rfl⟩
        · exact ⟨p, hp, by rw [one_smul, hpe]⟩ }
  rcases eq_bot_or_eq_top_of_invariant hb hnd TE (fun s e ⟨p, hp, hpe⟩ => by
      refine ⟨toAff (hEquiv hQ s) * p * (toAff (hEquiv hQ s))⁻¹,
        conj_mem_pSub (toAff_hEquiv_mem hQ hK s) hp, ?_⟩
      change (hEquiv hQ s (p ((hEquiv hQ s).symm 0))).1 = sE s e
      rw [map_zero, hEquiv_apply, hpe]) with hT | hT
  ·
    exfalso
    have hfst : ∀ p ∈ P, (p 0).1 = 0 := fun p hp => by
      have h1 : (p 0).1 ∈ TE := ⟨p, hp, rfl⟩
      rw [hT, Submodule.mem_bot] at h1
      exact h1
    have hcardP : Nat.card P ≤ 2 := by
      have h1 := Nat.card_le_card_of_injective (fun p : P => (p.1 0).2) (fun p p' h => by
          refine Subtype.ext (eq_of_mem_pSub p.2 p'.2 (Prod.ext ?_ h))
          rw [hfst _ p.2, hfst _ p'.2])
      rwa [Nat.card_zmod] at h1
    have hK' := card_K hE hb hnd hQ hK
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (indHom hE hb hnd hQ hK).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (indHom hE hb hnd hQ hK)).toEquiv]
      at hK'
    have hker : Nat.card (indHom hE hb hnd hQ hK).ker = Nat.card P :=
      (Subgroup.card_map_of_injective K.subtype_injective).symm
    rw [hker] at hK'
    have hdvd := Subgroup.card_subgroup_dvd_card (indHom hE hb hnd hQ hK).range
    rw [card_generalLinearGroup hE] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hpos : 0 < Nat.card P := Nat.card_pos
    rcases (show Nat.card P = 1 ∨ Nat.card P = 2 by omega) with h | h
    · rw [h, mul_one] at hK'
      rw [hK'] at hm
      omega
    · rw [h] at hK'
      rw [show Nat.card (indHom hE hb hnd hQ hK).range = 11520 by omega] at hm
      omega
  · exact ⟨_, (show e ∈ TE from hT ▸ Submodule.mem_top).choose_spec⟩

theorem exists_mem_pSub_apply_zero (A : E × ZMod 2) :
    ∃ p ∈ pSub hE hb hnd hQ hK, p 0 = A := by
  obtain ⟨p, hp, hpe⟩ := exists_mem_pSub_fst (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ)
    (hK := hK) A.1
  rcases zmod_two_cases ((p 0).2 + A.2) with h | h
  · exact ⟨p, hp, Prod.ext hpe (eq_of_add_eq_zero_zmod2 h)⟩
  · refine ⟨tr rV * p, (pSub hE hb hnd hQ hK).mul_mem tr_rV_mem_pSub hp, Prod.ext ?_ ?_⟩
    · change (rV + p 0).1 = A.1
      rw [Prod.fst_add, hpe]
      simp [rV]
    · change (rV + p 0).2 = A.2
      rw [Prod.snd_add]
      simp only [rV]
      have key : ∀ c a : ZMod 2, c + a = 1 → 1 + c = a := by decide
      exact key _ _ h

theorem card_pSub : Nat.card (pSub hE hb hnd hQ hK) = 32 := by
  rw [← card_V hE]
  refine Nat.card_congr (Equiv.ofBijective (fun p : pSub hE hb hnd hQ hK => p.1 0)
    ⟨fun p p' h => Subtype.ext (eq_of_mem_pSub p.2 p'.2 h), fun A => ?_⟩)
  obtain ⟨p, hp, hpA⟩ := exists_mem_pSub_apply_zero (hE := hE) (hb := hb) (hnd := hnd)
    (hQ := hQ) (hK := hK) A
  exact ⟨⟨p, hp⟩, hpA⟩

theorem range_indHom : (indHom hE hb hnd hQ hK).range = bilinIsometryGroup b := by
  have hfin : Finite (LinearMap.GeneralLinearGroup (ZMod 2) E) :=
    Nat.finite_of_card_ne_zero (by rw [card_generalLinearGroup hE]; decide)
  refine (Subgroup.eq_of_le_of_card_ge (fun g hg => ?_) ?_).symm
  · exact ⟨_, indHom_toAff_hEquiv (s := ⟨g, hg⟩)⟩
  · have hK' := card_K hE hb hnd hQ hK
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (indHom hE hb hnd hQ hK).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (indHom hE hb hnd hQ hK)).toEquiv,
      ← Subgroup.card_map_of_injective K.subtype_injective] at hK'
    change _ * Nat.card (pSub hE hb hnd hQ hK) = _ at hK'
    rw [card_pSub] at hK'
    rw [card_bilinIsometryGroup hE hb hnd]
    omega

end Ind

theorem indE_mem [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (hK : AffHyp Q K) {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hk : k ∈ K) :
    ∀ x y, b (indE k x) (indE k y) = b x y := by
  have h1 : indHom hE hb hnd hQ hK ⟨k, hk⟩ ∈ bilinIsometryGroup b := by
    rw [← range_indHom (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ) (hK := hK)]
    exact ⟨_, rfl⟩
  exact h1

@[expose] def lin2 (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) : E →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.snd (ZMod 2) E (ZMod 2)) ∘ₗ k.linear.toLinearMap ∘ₗ
    (LinearMap.inl (ZMod 2) E (ZMod 2))

theorem lin2_apply (k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) (x : E) :
    lin2 k x = (k.linear (x, 0)).2 :=
  rfl

section Ind

variable [FiniteDimensional (ZMod 2) E] {hE : Module.finrank (ZMod 2) E = 4} {hb : b.IsAlt}
  {hnd : b.Nondegenerate} {hQ : QuadraticMap.polarBilin Q = b} {hK : AffHyp Q K}

theorem linear_apply_of_mem_pSub {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (B : E × ZMod 2) :
    p.linear B = B + lin2 p B.1 • rV := by
  have hr := linear_rV hE hb hnd hQ hK (mem_pSub.mp hp).1
  have h1 : p.linear (B.1, 0) = (B.1, 0) + lin2 p B.1 • rV := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, ← indE_apply, (mem_pSub.mp hp).2]
      simp [rV]
    · rw [Prod.snd_add, ← lin2_apply]
      simp [rV]
  rw [linear_apply_of_rV hr, h1]
  refine Prod.ext ?_ ?_
  · simp [rV]
  · simp only [Prod.snd_add, Prod.smul_snd, rV, smul_eq_mul, mul_one]
    ring

theorem lin2_mul {p p' : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (hp' : p' ∈ pSub hE hb hnd hQ hK) (x : E) :
    lin2 (p * p') x = lin2 p x + lin2 p' x := by
  rw [lin2_apply]
  change (p.linear (p'.linear (x, 0))).2 = _
  rw [linear_apply_of_mem_pSub hp, linear_apply_of_mem_pSub hp']
  simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, rV, smul_zero, add_zero,
    smul_eq_mul, mul_one, zero_add]
  ring

theorem lin2_eq_zero {p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (h : (p 0).1 = 0) : lin2 p = 0 := by
  rcases (fst_eq_iff hE hb hnd hQ hK (mem_pSub.mp hp).1).mp (fun B => by
      rw [fst_apply_of_mem_pSub hp, h, add_zero]) with rfl | rfl
  · rfl
  · rfl

theorem lin2_eq_of_fst {p p' : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)}
    (hp : p ∈ pSub hE hb hnd hQ hK) (hp' : p' ∈ pSub hE hb hnd hQ hK)
    (h : (p 0).1 = (p' 0).1) : lin2 p = lin2 p' := by
  have hq : p'⁻¹ * p ∈ pSub hE hb hnd hQ hK :=
    (pSub hE hb hnd hQ hK).mul_mem ((pSub hE hb hnd hQ hK).inv_mem hp') hp
  have hq0 : ((p'⁻¹ * p) 0).1 = 0 := by
    have h1 := fst_apply_of_mem_pSub hp' ((p'⁻¹ * p) 0)
    rw [show p' ((p'⁻¹ * p) 0) = p 0 from p'.apply_symm_apply (p 0), h] at h1
    exact (add_eq_right.mp h1.symm)
  ext x
  rw [show p = p' * (p'⁻¹ * p) by group, lin2_mul hp' hq, lin2_eq_zero hq hq0,
    LinearMap.zero_apply, add_zero]

theorem exists_lin2_eq :
    ∃ lam : ZMod 2, ∀ p ∈ pSub hE hb hnd hQ hK, ∀ x, lin2 p x = lam * b (p 0).1 x := by
  choose pE hpE hpE0 using fun e : E => exists_mem_pSub_apply_zero (hE := hE) (hb := hb)
    (hnd := hnd) (hQ := hQ) (hK := hK) (e, 0)
  have hfst : ∀ e, (pE e 0).1 = e := fun e => by rw [hpE0]
  have hadd : ∀ e e' x, lin2 (pE (e + e')) x = lin2 (pE e) x + lin2 (pE e') x := fun e e' x => by
    rw [lin2_eq_of_fst (hpE (e + e')) ((pSub hE hb hnd hQ hK).mul_mem (hpE e) (hpE e')) (by
      change (pE (e + e') 0).1 = (pE e (pE e' 0)).1
      rw [fst_apply_of_mem_pSub (hpE e), hfst, hfst, hfst, add_comm]), lin2_mul (hpE e) (hpE e')]
  have hzero : ∀ x, lin2 (pE 0) x = 0 := fun x => by
    rw [lin2_eq_zero (hpE 0) (hfst 0), LinearMap.zero_apply]
  let Ψ : LinearMap.BilinForm (ZMod 2) E := LinearMap.mk₂ (ZMod 2) (fun e x => lin2 (pE e) x)
    (fun e e' x => hadd e e' x)
    (fun c e x => by
      rcases zmod_two_cases c with rfl | rfl
      · rw [zero_smul, hzero, zero_smul]
      · rw [one_smul, one_smul])
    (fun e x y => map_add _ x y)
    (fun c e x => map_smul _ c x)
  have hΨ : ∀ e x, Ψ e x = lin2 (pE e) x := fun _ _ => rfl
  have hinv : ∀ (s : bilinIsometryGroup b) e x, Ψ (sE s e) (sE s x) = Ψ e x := by
    intro s e x
    have hh := toAff_hEquiv_mem hQ hK s
    have hq := conj_mem_pSub hh (hpE e)
    have hq0 : ((toAff (hEquiv hQ s) * pE e * (toAff (hEquiv hQ s))⁻¹) 0).1 = sE s e := by
      change (hEquiv hQ s (pE e ((hEquiv hQ s).symm 0))).1 = sE s e
      rw [map_zero, hpE0, hEquiv_apply]
    rw [hΨ, hΨ, ← lin2_eq_of_fst hq (hpE (sE s e)) (by rw [hq0, hfst]), lin2_apply]
    have hsymm : (hEquiv hQ s).symm (sE s x, 0) = (x, Q x + Q (sE s x)) := by
      rw [LinearEquiv.symm_apply_eq, hEquiv_apply]
      refine Prod.ext rfl ?_
      change (0 : ZMod 2) = Q x + Q (sE s x) + Q x + Q (sE s x)
      have key : ∀ a c : ZMod 2, (0 : ZMod 2) = a + c + a + c := by decide
      exact key _ _
    change (hEquiv hQ s ((pE e).linear ((hEquiv hQ s).symm (sE s x, 0)))).2 = _
    rw [hsymm, linear_apply_of_mem_pSub (hpE e), hEquiv_apply]
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, rV, smul_zero,
      add_zero, smul_eq_mul, mul_one]
    have key : ∀ a c d : ZMod 2, a + c + d + a + c = d := by decide
    exact key _ _ _
  obtain ⟨lam, hlam⟩ := exists_eq_mul_of_invariant_bilin hb hnd Ψ hinv
  refine ⟨lam, fun p hp x => ?_⟩
  rw [lin2_eq_of_fst hp (hpE (p 0).1) (by rw [hfst]), ← hΨ, hlam]

theorem pSub_eq_twoCoreGroup {lam : ZMod 2}
    (hlam : ∀ p ∈ pSub hE hb hnd hQ hK, ∀ x, lin2 p x = lam * b (p 0).1 x) :
    pSub hE hb hnd hQ hK = twoCoreGroup hb lam := by
  have heq : ∀ p ∈ pSub hE hb hnd hQ hK, p = twoCoreMap b lam (p 0) := fun p hp =>
    AffineEquiv.ext fun B => by
      rw [twoCoreMap_apply, aff_apply, linear_apply_of_mem_pSub hp, hlam p hp]
      abel
  ext p
  constructor
  · intro hp
    exact ⟨p 0, (heq p hp).symm⟩
  · rintro ⟨A, rfl⟩
    obtain ⟨p, hp, hpA⟩ := exists_mem_pSub_apply_zero (hE := hE) (hb := hb) (hnd := hnd)
      (hQ := hQ) (hK := hK) A
    rw [← hpA, ← heq p hp]
    exact hp

theorem pCoreOf_eq_pSub : CFSG.Assembly.pCoreOf 2 K = pSub hE hb hnd hQ hK := by
  rw [CFSG.Open.pCoreOf, CFSG.pCore_eq_iSup]
  apply le_antisymm
  ·
    refine Subgroup.map_mono (iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_)
    let f := (indHom hE hb hnd hQ hK).codRestrict (bilinIsometryGroup b) fun k =>
      indE_mem hE hb hnd hQ hK k.2
    have hf : Function.Surjective f := fun s => by
      have hs : (s : LinearMap.GeneralLinearGroup (ZMod 2) E) ∈
          (indHom hE hb hnd hQ hK).range := by
        rw [range_indHom]
        exact s.2
      obtain ⟨k, hk⟩ := hs
      exact ⟨k, Subtype.ext hk⟩
    have h1 := eq_bot_of_normal_isPGroup hE hb hnd (N.map f) (hN.map f hf) (hp.map f)
    rw [Subgroup.map_eq_bot_iff,
      show f.ker = (indHom hE hb hnd hQ hK).ker from MonoidHom.ker_codRestrict _ _ _] at h1
    exact h1
  ·
    refine Subgroup.map_mono (le_iSup_of_le _ (le_iSup_of_le (MonoidHom.normal_ker _)
      (le_iSup_of_le ?_ le_rfl)))
    refine IsPGroup.of_card (n := 5) ?_
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact card_pSub

end Ind

theorem twoCoreMap_zero (b : LinearMap.BilinForm (ZMod 2) E) (lam : ZMod 2) :
    twoCoreMap b lam 0 = 1 :=
  AffineEquiv.ext fun B => by
    rw [twoCoreMap_apply]
    simp

theorem isElemAbelian_twoCoreGroup (hb : b.IsAlt) (lam : ZMod 2) :
    CFSG.Assembly.IsElemAbelian 2 (twoCoreGroup hb lam) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨A, hA⟩ := x.2
    obtain ⟨A', hA'⟩ := y.2
    change x.1 * y.1 = y.1 * x.1
    rw [← hA, ← hA', twoCoreMap_mul, twoCoreMap_mul, symm_apply hb A.1 A'.1]
    congr 1
    abel
  · rintro _ ⟨A, rfl⟩
    rw [sq, twoCoreMap_mul, hb.self_eq_zero, mul_zero, zero_smul, add_zero,
      add_self_eq_zero_zmod_two, twoCoreMap_zero]

theorem twoCoreGroup_regular (hb : b.IsAlt) (lam : ZMod 2) (x y : E × ZMod 2) :
    ∃! p, p ∈ twoCoreGroup hb lam ∧ p x = y := by
  have hfst : ∀ (A : E × ZMod 2) (c : ZMod 2), (A - c • rV).1 = A.1 := fun A c => by
    simp [rV]
  refine ⟨twoCoreMap b lam (y - x - (lam * b (y - x).1 x.1) • rV), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [twoCoreMap_apply, hfst]
    abel
  · rintro _ ⟨⟨A', rfl⟩, hA'⟩
    rw [twoCoreMap_apply] at hA'
    have h1 : A' = y - x - (lam * b A'.1 x.1) • rV := by
      rw [← hA']
      abel
    have h2 : A'.1 = (y - x).1 := by
      conv_lhs => rw [h1]
      rw [hfst]
    rw [h1, h2]

theorem toAff_eq_one {g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)} (h : toAff g = 1) : g = 1 :=
  LinearEquiv.ext fun x => congrArg (fun k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) => k x) h

end FullAffine

open FullAffine

theorem binary_odd_quadratic_five_full_affine_two_core_and_actions
    [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b)
    (K : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)))
    (htrans : ∀ x y : E × ZMod 2, ∃ k ∈ K, k x = y)
    (hK₀ : ∀ g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2),
      g.toAffineEquiv ∈ K ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) :
    (∀ h : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2),
      h ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) ↔
        ∃ S ∈ bilinIsometryGroup b, ∀ w t,
          h (w, t) = ((S : E →ₗ[ZMod 2] E) w, t + Q w + Q ((S : E →ₗ[ZMod 2] E) w))) ∧
    (∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q), h (0, 1) = (0, 1)) ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) = 720 ∧
    ∃ lam : ZMod 2,
      CFSG.Assembly.pCoreOf 2 K = twoCoreGroup hb lam ∧
      (∀ A B : E × ZMod 2, twoCoreMap b lam A B = B + A + (lam * b A.1 B.1) • (0, 1)) ∧
      CFSG.Assembly.IsElemAbelian 2 (twoCoreGroup hb lam) ∧
      Nat.card (twoCoreGroup hb lam) = 32 ∧
      (∀ x y : E × ZMod 2, ∃! p, p ∈ twoCoreGroup hb lam ∧ p x = y) ∧
      twoCoreGroup hb lam ≤ K ∧
      (∀ k ∈ K, ∀ p ∈ twoCoreGroup hb lam, k * p * k⁻¹ ∈ twoCoreGroup hb lam) ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q),
        g.toAffineEquiv ∈ twoCoreGroup hb lam → g = 1) ∧
      (∀ k ∈ K, ∃ p ∈ twoCoreGroup hb lam,
        ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q), k = p * g.toAffineEquiv) ∧
      (∀ k ∈ K, k.linear (0, 1) = (0, 1)) ∧
      (∀ k ∈ K, (∀ B, (k B).1 = B.1) ↔
        k = 1 ∨ k = AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) (0, 1)) ∧
      (∀ k ∈ K, ∃ S ∈ bilinIsometryGroup b, ∃ e : E,
        ∀ B, (k B).1 = (S : E →ₗ[ZMod 2] E) B.1 + e) ∧
      (∀ S ∈ bilinIsometryGroup b, ∀ e : E, ∃ k ∈ K,
        ∀ B, (k B).1 = (S : E →ₗ[ZMod 2] E) B.1 + e) ∧
      AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) (0, 1) ∈ K ∧
      (∀ k ∈ K, k * AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) (0, 1) * k⁻¹ =
        AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) (0, 1)) ∧
      AffineEquiv.constVAdd (ZMod 2) (E × ZMod 2) (0, 1) ∈ twoCoreGroup hb lam ∧
      (∀ p ∈ twoCoreGroup hb lam, ∃ e : E, ∀ B, (p B).1 = B.1 + e) ∧
      (∀ e : E, ∃ p ∈ twoCoreGroup hb lam, ∀ B, (p B).1 = B.1 + e) := by
  have hK : AffHyp Q K := ⟨htrans, hK₀⟩
  obtain ⟨lam, hlam⟩ := exists_lin2_eq (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ) (hK := hK)
  have hP := pSub_eq_twoCoreGroup hlam
  refine ⟨mem_orthogonalGroup_qForm_iff hnd hQ, fun h hh => apply_rV_of_mem hnd hQ hh,
    card_orthogonalGroup_qForm hE hb hnd hQ, lam, ?_, fun A B => twoCoreMap_apply b lam A B,
    isElemAbelian_twoCoreGroup hb lam, ?_, twoCoreGroup_regular hb lam, ?_, ?_, ?_, ?_,
    fun k hk => linear_rV hE hb hnd hQ hK hk, fun k hk => fst_eq_iff hE hb hnd hQ hK hk, ?_, ?_,
    tr_rV_mem hE hb hnd hQ hK, ?_, ?_, ?_, ?_⟩
  · rw [pCoreOf_eq_pSub (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ) (hK := hK), hP]
  · rw [← hP]
    exact card_pSub
  · rw [← hP]
    exact pSub_le
  · intro k hk p hp
    rw [← hP] at hp ⊢
    exact conj_mem_pSub hk hp
  · intro g _ hgP
    rw [← hP] at hgP
    exact toAff_eq_one (eq_one_of_mem_pSub hgP (map_zero g))
  · intro k hk
    obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hE := hE) (hb := hb) (hnd := hnd)
      (hQ := hQ) (hK := hK) (k 0)
    have h0 : (p⁻¹ * k) 0 = 0 := by
      change p.symm (k 0) = 0
      rw [AffineEquiv.symm_apply_eq, hp0]
    refine ⟨p, hP ▸ hp, (p⁻¹ * k).linear,
      linear_mem_of_apply_zero hK (K.mul_mem (K.inv_mem (pSub_le hp)) hk) h0, ?_⟩
    rw [← eq_toAffineEquiv_of_apply_zero h0, mul_inv_cancel_left]
  · intro k hk
    exact ⟨indHom hE hb hnd hQ hK ⟨k, hk⟩, indE_mem hE hb hnd hQ hK hk, (k 0).1,
      fun B => fst_apply_of_rV (linear_rV hE hb hnd hQ hK hk) B⟩
  · intro S hS e
    obtain ⟨p, hp, hpe⟩ := exists_mem_pSub_fst (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ)
      (hK := hK) e
    refine ⟨p * toAff (hEquiv hQ ⟨S, hS⟩),
      K.mul_mem (pSub_le hp) (toAff_hEquiv_mem hQ hK _), fun B => ?_⟩
    change (p (hEquiv hQ ⟨S, hS⟩ B)).1 = _
    rw [fst_apply_of_mem_pSub hp, hpe]
    rfl
  · intro k hk
    rw [conj_tr]
    exact congrArg tr (linear_rV hE hb hnd hQ hK hk)
  · rw [← hP]
    exact tr_rV_mem_pSub
  · intro p hp
    rw [← hP] at hp
    exact ⟨(p 0).1, fst_apply_of_mem_pSub hp⟩
  · intro e
    obtain ⟨p, hp, hpe⟩ := exists_mem_pSub_fst (hE := hE) (hb := hb) (hnd := hnd) (hQ := hQ)
      (hK := hK) e
    exact ⟨p, hP ▸ hp, fun B => by rw [fst_apply_of_mem_pSub hp, hpe]⟩

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
