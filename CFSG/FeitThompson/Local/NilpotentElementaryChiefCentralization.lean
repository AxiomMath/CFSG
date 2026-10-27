module

public import Mathlib.RepresentationTheory.Invariants
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections
import CFSG.FeitThompson.Local.FixedFreeComplementKernelActsTrivially
import CFSG.FeitThompson.Local.NormalModularSubgroupIrreducibleTrivial
import CFSG.FeitThompson.Local.NormalNilpotentCentralizesChiefFactors
import CFSG.FeitThompson.Foundations.SolvableExtensionNormalQuotient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {H R L X Y : Subgroup G} {p q e : ℕ}

theorem isSolvable_of_mul_coe_eq_univ [hH : H.Normal] [Group.IsSolvable ↥H] [Group.IsSolvable ↥R]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) : Group.IsSolvable G := by
  have hsurj : Function.Surjective ((mk' H).comp R.subtype) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨h, hh, r, hr, rfl⟩ : g ∈ (H : Set G) * (R : Set G) := by rw [hprod]; trivial
      refine ⟨⟨r, hr⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, mk'_apply]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hH.conj_mem h hh r⁻¹
  have : Group.IsSolvable (G ⧸ H) := Group.isSolvable_of_surjective hsurj
  exact isSolvable_of_normal_of_quotient H

theorem eq_one_of_representationOfMulAut_eq_one {M A V : Type*} [Monoid M] [Group A]
    [AddCommGroup V] (r : ℕ) [Module (ZMod r) V] (σ : M →* MulAut A)
    (ee : A ≃* Multiplicative V) {m : M} (h : representationOfMulAut r σ ee m = 1) : σ m = 1 := by
  ext a
  have h1 := representationOfMulAut_apply_toAdd r σ ee m a
  rw [h] at h1
  simp only [Module.End.one_apply] at h1
  have h2 : σ m a = a := ee.injective (Multiplicative.toAdd.injective h1.symm)
  simpa using h2

theorem commutator_le_of_forall_quotientFactorConj_eq_one [X.Normal] [Y.Normal] (K : Subgroup G)
    (h : ∀ g ∈ K, quotientFactorConj X Y g = 1) : ⁅K, X⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro g hg x hx
  have h2 : quotientFactorConj X Y g ⟨(x : G ⧸ Y), mk_mem_quotientFactor X Y hx⟩
      = ⟨(x : G ⧸ Y), mk_mem_quotientFactor X Y hx⟩ := by rw [h g hg]; rfl
  have h3 := congrArg (fun z : ↥(quotientFactor X Y) => (z : G ⧸ Y)) h2
  simp only [coe_quotientFactorConj_apply] at h3
  rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
  calc ((g * x * g⁻¹ * x⁻¹ : G) : G ⧸ Y)
      = ((g : G) : G ⧸ Y) * ((x : G) : G ⧸ Y) * ((g : G) : G ⧸ Y)⁻¹ * ((x : G) : G ⧸ Y)⁻¹ := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    _ = 1 := by rw [h3]; simp

theorem invariants_comp_subtype_map_mk'_eq_bot [Finite H] [H.Normal] [Group.IsSolvable ↥H]
    [X.Normal] [Y.Normal] [L.Normal] (hp : p.Prime) (hR : Nat.card R = p)
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) (hXH : X ≤ H) (hLX : ⁅L, X⁆ ≤ Y)
    {r d : ℕ} [Fact r.Prime] (ee : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)) :
    Representation.invariants
        ((representationOfMulAut r (quotientFactorConjAut X Y hLX) ee).comp
          (R.map (mk' L) : Subgroup (G ⧸ L)).subtype) = ⊥ := by
  rw [invariants_comp_subtype_eq_bot_iff]
  intro v hv
  set z : ↥(quotientFactor X Y) := ee.symm (Multiplicative.ofAdd v) with hzdef
  have hz : ∀ s ∈ R, quotientFactorConj X Y s z = z := by
    intro s hs
    have h1 := hv (mk s) ⟨s, hs, rfl⟩
    rw [representationOfMulAut_apply, quotientFactorConjAut_mk] at h1
    have h2 : Multiplicative.toAdd (ee (quotientFactorConj X Y s z))
        = Multiplicative.toAdd (ee z) := by rw [hzdef]; simpa using h1
    exact ee.injective (Multiplicative.toAdd.injective h2)
  obtain ⟨x, hx, hxz⟩ := (mem_quotientFactor X Y).1 z.2
  have hfix : ∀ s ∈ R, x⁻¹ * (s * x * s⁻¹) ∈ Y := by
    intro s hs
    have h3 := congrArg (fun w : ↥(quotientFactor X Y) => (w : G ⧸ Y)) (hz s hs)
    simp only [coe_quotientFactorConj_apply] at h3
    rw [← hxz] at h3
    have h4 : ((s * x * s⁻¹ : G) : G ⧸ Y) = ((x : G) : G ⧸ Y) := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h3
    exact (QuotientGroup.eq (s := Y)).1 h4.symm
  have hxY : x ∈ Y :=
    mem_of_forall_inv_mul_conj_mem hp hR hCH hXH le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal hx hfix
  have hz1 : z = 1 := by
    refine Subtype.ext ?_
    rw [← hxz]
    simpa using (QuotientGroup.eq_one_iff x).2 hxY
  have hv1 : Multiplicative.ofAdd v = 1 := by
    have := congrArg ee hz1
    simpa [hzdef] using this
  simpa using hv1

theorem natCard_map_mk'_eq_of_mulEquiv [L.Normal]
    (ee : (↥H ⧸ L.subgroupOf H) ≃* Multiplicative (Fin e → ZMod q)) :
    Nat.card (H.map (mk' L) : Subgroup (G ⧸ L)) = q ^ e := by
  rw [map_mk'_eq_quotientFactor,
    Nat.card_eq_of_bijective _ ((quotientFactorMulEquiv H L).symm.trans ee).bijective,
    Nat.card_eq_of_bijective Multiplicative.toAdd Multiplicative.toAdd.bijective]
  simp [Nat.card_fun, Nat.card_zmod]

theorem commutator_le_of_isChiefFactor_of_isNilpotent_of_elementaryQuotient
    [Finite G] [H.Normal] [Group.IsSolvable ↥H] [L.Normal]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) (hinf : H ⊓ R = ⊥)
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥)
    (hLH : L < H) (hLnil : Group.IsNilpotent ↥L) (hq : q.Prime) (_he : 1 ≤ e)
    (ee : (↥H ⧸ L.subgroupOf H) ≃* Multiplicative (Fin e → ZMod q))
    (hXY : IsChiefFactor X Y) (hXH : X ≤ H) : ⁅H, X⁆ ≤ Y := by
  have := hXY.normal_num
  have := hXY.normal_den
  have : Group.IsSolvable ↥R := isSolvable_of_natCard_eq_prime hp hR
  have hGsol : Group.IsSolvable G := isSolvable_of_mul_coe_eq_univ hprod
  have hLX : ⁅L, X⁆ ≤ Y := commutator_le_of_isChiefFactor ‹L.Normal› hLnil hXY
  obtain ⟨r, d, hr, hd, ee', hirr⟩ :=
    exists_prime_mulEquiv_isIrreducible_quotient_of_isChiefFactor X Y hXY hLX
  have _ifr : Fact r.Prime := ⟨hr⟩
  set ρ := representationOfMulAut r (quotientFactorConjAut X Y hLX) ee' with hρ
  have hUnormal : (H.map (mk' L) : Subgroup (G ⧸ L)).Normal := QuotientGroup.map_normal L H
  have hUcard : Nat.card (H.map (mk' L) : Subgroup (G ⧸ L)) = q ^ e :=
    natCard_map_mk'_eq_of_mulEquiv ee
  have hker : ∀ u ∈ (H.map (mk' L) : Subgroup (G ⧸ L)), ρ u = 1 := by
    by_cases hrq : r = q
    ·
      subst hrq
      exact fun u hu => le_ker_of_isIrreducible (a := e) hUcard hirr hu
    ·
      have hcompl : (H.map (mk' L) : Subgroup (G ⧸ L)).IsComplement' (R.map (mk' L)) :=
        Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          (disjoint_iff.2 (map_mk'_inf_map_mk'_eq_bot hLH.le hinf))
          (map_mk'_mul_map_mk'_eq_univ L hprod)
      have hC : ∀ w ∈ (R.map (mk' L) : Subgroup (G ⧸ L)), w ≠ 1 →
          (H.map (mk' L) : Subgroup (G ⧸ L)) ⊓ Subgroup.centralizer {w} = ⊥ := by
        intro w hw hw1
        obtain ⟨s, hs, rfl⟩ := hw
        exact map_mk'_inf_centralizer_singleton_eq_bot hp hR hCH hs
          (by rintro rfl; exact hw1 (by simp))
      have hk : (Nat.card (H.map (mk' L) : Subgroup (G ⧸ L)) : ZMod r) ≠ 0 := by
        rw [hUcard, Nat.cast_pow]
        refine pow_ne_zero _ ?_
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hdvd => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).1 hdvd)
      exact fun u hu =>
        eq_one_of_invariants_comp_subtype_eq_bot hUnormal hcompl hC hk ρ
          (invariants_comp_subtype_map_mk'_eq_bot hp hR hCH hXH hLX ee') hu
  refine commutator_le_of_forall_quotientFactorConj_eq_one H fun g hg => ?_
  have h1 : ρ (mk g) = 1 := hker _ ⟨g, hg, rfl⟩
  have h2 := eq_one_of_representationOfMulAut_eq_one r _ ee' h1
  rwa [quotientFactorConjAut_mk] at h2

theorem isNilpotent_of_isNilpotent_of_elementaryQuotient
    [Finite G] [H.Normal] [Group.IsSolvable ↥H] [L.Normal]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) (hinf : H ⊓ R = ⊥)
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥)
    (hLH : L < H) (hLnil : Group.IsNilpotent ↥L) (hq : q.Prime) (he : 1 ≤ e)
    (ee : (↥H ⧸ L.subgroupOf H) ≃* Multiplicative (Fin e → ZMod q)) :
    Group.IsNilpotent ↥H := by
  have : Group.IsSolvable ↥R := isSolvable_of_natCard_eq_prime hp hR
  have : Group.IsSolvable G := isSolvable_of_mul_coe_eq_univ hprod
  exact (isNilpotent_iff_forall_isChiefFactor H).2 fun _ _ hXY hXH =>
    commutator_le_of_isChiefFactor_of_isNilpotent_of_elementaryQuotient hprod hinf hp hR hCH
      hLH hLnil hq he ee hXY hXH

end CFSG.FeitThompson
