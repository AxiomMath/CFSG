module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEightCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEightAffine
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.SeitzReduction.RankOne

namespace SzEight

@[expose] def equivariantAddAut {M : Type*} [AddGroup M] (P : M → M) :
    Subgroup (Multiplicative (AddAut M)) where
  carrier := {h | ∃ φ : AddAut M, ∀ a, Multiplicative.toAdd h (P a) = P (φ a)}
  one_mem' := ⟨0, fun _ => rfl⟩
  mul_mem' := by
    rintro h₁ h₂ ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    exact ⟨φ₁ + φ₂, fun a => by simp only [toAdd_mul, AddAut.add_apply, hφ₂, hφ₁]⟩
  inv_mem' := by
    rintro h ⟨φ, hφ⟩
    refine ⟨-φ, fun a => ?_⟩
    simp only [toAdd_inv, AddAut.neg_apply]
    rw [AddEquiv.symm_apply_eq, hφ, AddEquiv.apply_symm_apply]

theorem mem_equivariantAddAut {M : Type*} [AddGroup M] {P : M → M}
    {h : Multiplicative (AddAut M)} :
    h ∈ equivariantAddAut P ↔ ∃ φ : AddAut M, ∀ a, Multiplicative.toAdd h (P a) = P (φ a) :=
  Iff.rfl

theorem card_equivariantAddAut_congr {M M' : Type*} [AddGroup M] [AddGroup M'] (e : M ≃+ M')
    {P : M → M} {P' : M' → M'} (he : ∀ m, e (P m) = P' (e m)) :
    Nat.card (equivariantAddAut P) = Nat.card (equivariantAddAut P') := by
  have he' : ∀ m', e.symm (P' m') = P (e.symm m') := fun m' => by
    rw [AddEquiv.symm_apply_eq, he, AddEquiv.apply_symm_apply]
  let c : Multiplicative (AddAut M) ≃ Multiplicative (AddAut M') :=
    { toFun h := Multiplicative.ofAdd (e.symm.trans ((Multiplicative.toAdd h).trans e))
      invFun h := Multiplicative.ofAdd (e.trans ((Multiplicative.toAdd h).trans e.symm))
      left_inv h := by
        apply Multiplicative.toAdd.injective
        ext m
        simp
      right_inv h := by
        apply Multiplicative.toAdd.injective
        ext m
        simp }
  refine Nat.card_congr (c.subtypeEquiv fun h => ?_)
  simp only [mem_equivariantAddAut]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨e.symm.trans (φ.trans e), fun m' => ?_⟩
    simp only [c, Equiv.coe_fn_mk, toAdd_ofAdd, AddEquiv.trans_apply, he', hφ, he]
  · rintro ⟨φ', hφ'⟩
    refine ⟨e.trans (φ'.trans e.symm), fun m => ?_⟩
    have h1 := hφ' (e m)
    simp only [c, Equiv.coe_fn_mk, toAdd_ofAdd, AddEquiv.trans_apply, ← he,
      AddEquiv.symm_apply_apply] at h1
    simp only [AddEquiv.trans_apply]
    rw [← he', ← h1, AddEquiv.symm_apply_apply]

@[expose] def basisValues (f : AddAut V) : V × V × V := (f (1, 0, 0), f (0, 1, 0), f (0, 0, 1))

theorem apply_eq_lin_basisValues (f : AddAut V) (v : V) : f v = lin (basisValues f) v :=
  eq_lin f.toAddMonoidHom v

theorem admissible_basisValues {h : Multiplicative (AddAut V)}
    (hh : h ∈ equivariantAddAut pow5) : Admissible (basisValues (Multiplicative.toAdd h)) := by
  obtain ⟨φ, hφ⟩ := hh
  have htw : ∀ v, twist (basisValues (Multiplicative.toAdd h)) v = φ v := fun v => by
    rw [twist, ← apply_eq_lin_basisValues, hφ, pow3_pow5]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · simp only [htw]
    exact apply_eq_lin_basisValues φ v
  · rw [← apply_eq_lin_basisValues] at hv
    exact (Multiplicative.toAdd h).map_eq_zero_iff.1 hv

theorem lin_injective_of_admissible {t : V × V × V} (ht : Admissible t) :
    Function.Injective (lin t) :=
  (injective_iff_map_eq_zero (linHom t)).2 ht.2

@[expose] noncomputable def linEquiv {t : V × V × V} (ht : Admissible t) : AddAut V :=
  AddEquiv.ofBijective (linHom t) (Finite.injective_iff_bijective.1
    (lin_injective_of_admissible ht))

theorem linEquiv_apply {t : V × V × V} (ht : Admissible t) (v : V) : linEquiv ht v = lin t v :=
  rfl

@[expose] noncomputable def twistEquiv {t : V × V × V} (ht : Admissible t) : AddAut V :=
  AddEquiv.ofBijective (linHom (twist t (1, 0, 0), twist t (0, 1, 0), twist t (0, 0, 1)))
    (Finite.injective_iff_bijective.1 fun v w hvw => by
      simp only [linHom_apply, ← ht.1] at hvw
      have h3 : Function.LeftInverse pow5 pow3 := pow5_pow3
      have h5 : Function.LeftInverse pow3 pow5 := pow3_pow5
      exact h5.injective (lin_injective_of_admissible ht (h3.injective hvw)))

theorem twistEquiv_apply {t : V × V × V} (ht : Admissible t) (v : V) :
    twistEquiv ht v = twist t v :=
  (ht.1 v).symm

theorem ofAdd_linEquiv_mem {t : V × V × V} (ht : Admissible t) :
    Multiplicative.ofAdd (linEquiv ht) ∈ equivariantAddAut pow5 :=
  ⟨twistEquiv ht, fun v => by
    rw [toAdd_ofAdd, linEquiv_apply, twistEquiv_apply, twist, pow5_pow3]⟩

theorem card_equivariantAddAut_pow5 : Nat.card (equivariantAddAut pow5) = 21 := by
  rw [← card_admissible, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun h := ⟨basisValues (Multiplicative.toAdd h.1), admissible_basisValues h.2⟩
      invFun t := ⟨Multiplicative.ofAdd (linEquiv t.2), ofAdd_linEquiv_mem t.2⟩
      left_inv h := ?_
      right_inv t := ?_ }
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    refine AddEquiv.ext fun v => ?_
    dsimp only
    rw [toAdd_ofAdd, linEquiv_apply, ← apply_eq_lin_basisValues]
  · apply Subtype.ext
    obtain ⟨h₀, h₁, h₂⟩ := lin_basis t.1
    simp only [basisValues, toAdd_ofAdd, linEquiv_apply, h₀, h₁, h₂]

theorem card_equivariantAddAut_pow_five {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 8) :
    Nat.card (equivariantAddAut (fun a : K => a ^ 5)) = 21 := by
  obtain ⟨e, he⟩ := exists_addEquiv_pow_five hK
  rw [← card_equivariantAddAut_congr (P' := fun a : K => a ^ 5) e he,
    card_equivariantAddAut_pow5]

end SzEight

open SzEight

theorem card_dvd_21_of_sq_equivariant {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 8)
    (Γ : Subgroup (Multiplicative (AddAut K)))
    (hΓ : ∀ h ∈ Γ, ∃ φ : AddAut K, ∀ a, Multiplicative.toAdd h (a ^ 5) = φ a ^ 5) :
    Nat.card Γ ∣ 21 := by
  rw [← card_equivariantAddAut_pow_five hK]
  exact Subgroup.card_dvd_of_le hΓ

theorem not_injective_of_card_eq_168_of_sq_equivariant {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 8) {H : Type*} [Group H] (hH : Nat.card H = 168)
    (ρ : H →* Multiplicative (AddAut K))
    (hρ : ∀ x, ∃ φ : AddAut K, ∀ a, Multiplicative.toAdd (ρ x) (a ^ 5) = φ a ^ 5) :
    ¬ Function.Injective ρ := by
  intro hinj
  have hdvd := card_dvd_21_of_sq_equivariant hK ρ.range (by
    rintro h ⟨x, rfl⟩
    exact hρ x)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hH] at hdvd
  norm_num at hdvd

theorem false_of_affine_card_eq_168_of_sq_equivariant {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 8) (N : Subgroup (Equiv.Perm K))
    (haff : ∀ x ∈ N, ∀ v w, x (v + w) + x 0 = x v + x w) (hN : Nat.card N = 168)
    (hs : IsSimpleGroup N) (hsq : ∀ x ∈ N, ∃ φ : AddAut K, ∀ a, x (a ^ 5) - x 0 = φ a ^ 5) :
    False := by
  refine not_injective_of_card_eq_168_of_sq_equivariant hK hN (affineLinearPartHom N haff)
    (fun x => ?_) (affineLinearPartHom_injective N haff hs (by omega))
  obtain ⟨φ, hφ⟩ := hsq x x.2
  exact ⟨φ, fun a => by rw [affineLinearPartHom_apply]; exact hφ a⟩

end CFSG.SeitzReduction.RankOne
