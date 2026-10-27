module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Conj

variable {K : Type*} [Group K]

theorem fixSub_conj_mul_mul_inv (c g : MulAut K) :
    fixSub (c * g * c⁻¹) = (fixSub g).map c.toMonoidHom := by
  ext z
  rw [Subgroup.mem_map_equiv]
  change (c * g * c⁻¹) z = z ↔ c.symm z ∈ fixSub g
  rw [mem_fixSub]
  constructor
  · intro h
    have := congrArg c.symm h
    simpa [MulAut.mul_apply] using this
  · intro h
    change c (g (c⁻¹ z)) = z
    have h' : g (c.symm z) = c.symm z := h
    have : (c⁻¹ : MulAut K) z = c.symm z := rfl
    rw [this, h']
    exact c.apply_symm_apply z

theorem card_fixSub_conj (c g : MulAut K) :
    Nat.card (fixSub (c * g * c⁻¹)) = Nat.card (fixSub g) := by
  rw [fixSub_conj_mul_mul_inv]
  exact Subgroup.card_map_of_injective c.injective

end Conj

section Core

variable {K : Type*} [Group K]

theorem pow_apply_eq_of_fix {J : Subgroup K} {g : MulAut K} (hg : ∀ u ∈ J, g u = u) (n : ℕ)
    {u : K} (hu : u ∈ J) : (g ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, hg u hu, ih]

theorem fieldCoreAt_of_canonical_conj_primeFaithful [Finite K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {δ : MulAut K}
    (hδp : orderOf δ = p) {J : Subgroup K} (hJq : CFSG.IsQuasisimple J)
    (hJ : ∀ g : K, g ∈ J ↔ δ g = g)
    (hfaith : ∀ g : MulAut K, (orderOf g).Prime → orderOf g ≠ p → g * δ = δ * g →
      (∀ u ∈ J, g u = u) → False)
    {x h : MulAut K} (hxh : x = h * δ * h⁻¹) {y : MulAut K} (hy : y ∈ innerAut K) (hy1 : y ≠ 1)
    (hyp : y ^ p = 1) (hcomm : y * x = x * y) : FieldCoreAt p x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hy hy1 hyp hcomm
  have hJp : ¬ Nat.Coprime p (Nat.card J) := by
    have hkJ : k ∈ J := (hJ k).2 hkδ
    have hdvd : p ∣ Nat.card J := by
      have : orderOf (⟨k, hkJ⟩ : J) = p := by
        rw [Subgroup.orderOf_mk]
        exact hkord
      rw [← this]
      exact orderOf_dvd_natCard _
    exact fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hdvd
  have hδ : FieldCoreAt p δ := by
    refine ⟨J, fun j hj => (hJ j).1 hj, fun f hf t ht => ?_, hJq, hJp, ?_⟩
    · refine (hJ _).2 ?_
      have hf' := mem_fixSub.1 hf
      have ht' := (hJ t).1 ht
      change δ (f * t * f⁻¹) = f * t * f⁻¹
      rw [map_mul, map_mul, map_inv]
      change δ f * δ t * (δ f)⁻¹ = f * t * f⁻¹
      rw [show δ f = f from hf', ht']
    · intro g hgp hgδ hgJ
      by_contra hg1
      have hne : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.1 h1)
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
      have hrp : r ≠ p := by
        rintro rfl
        exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hgp (dvd_refl r) hrd)
      set g' := g ^ (orderOf g / r) with hg'
      have hord : orderOf g' = r := orderOf_pow_orderOf_div (orderOf_pos g).ne' hrd
      refine hfaith g' (hord ▸ hr) (hord ▸ hrp) ?_ fun u hu => pow_apply_eq_of_fix hgJ _ hu
      exact ((Commute.pow_left (show Commute g δ from hgδ) _).eq)
  exact fieldCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)

end Core

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
