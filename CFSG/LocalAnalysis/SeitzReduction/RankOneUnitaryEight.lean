module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEightCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEight

public section

namespace CFSG.SeitzReduction.RankOne

namespace UEight

open SzEight

@[expose] def compatAddAut {Y Z : Type*} [AddGroup Y] [AddGroup Z] (P : Y → Z) :
    Subgroup (Multiplicative (AddAut Z)) where
  carrier := {h | ∃ φ : AddAut Y, ∀ a, Multiplicative.toAdd h (P a) = P (φ a)}
  one_mem' := ⟨0, fun _ => rfl⟩
  mul_mem' := by
    rintro h₁ h₂ ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    exact ⟨φ₁ + φ₂, fun a => by simp only [toAdd_mul, AddAut.add_apply, hφ₂, hφ₁]⟩
  inv_mem' := by
    rintro h ⟨φ, hφ⟩
    refine ⟨-φ, fun a => ?_⟩
    simp only [toAdd_inv, AddAut.neg_apply]
    rw [AddEquiv.symm_apply_eq, hφ, AddEquiv.apply_symm_apply]

theorem mem_compatAddAut {Y Z : Type*} [AddGroup Y] [AddGroup Z] {P : Y → Z}
    {h : Multiplicative (AddAut Z)} :
    h ∈ compatAddAut P ↔ ∃ φ : AddAut Y, ∀ a, Multiplicative.toAdd h (P a) = P (φ a) :=
  Iff.rfl

theorem card_compatAddAut_congr {Y Z Y' Z' : Type*} [AddGroup Y] [AddGroup Z] [AddGroup Y']
    [AddGroup Z'] (e : Y ≃+ Y') (e' : Z ≃+ Z') {P : Y → Z} {P' : Y' → Z'}
    (he : ∀ y, e' (P y) = P' (e y)) :
    Nat.card (compatAddAut P) = Nat.card (compatAddAut P') := by
  have he' : ∀ y', e'.symm (P' y') = P (e.symm y') := fun y' => by
    rw [AddEquiv.symm_apply_eq, he, AddEquiv.apply_symm_apply]
  let c : Multiplicative (AddAut Z) ≃ Multiplicative (AddAut Z') :=
    { toFun h := Multiplicative.ofAdd (e'.symm.trans ((Multiplicative.toAdd h).trans e'))
      invFun h := Multiplicative.ofAdd (e'.trans ((Multiplicative.toAdd h).trans e'.symm))
      left_inv h := by
        apply Multiplicative.toAdd.injective
        ext m
        simp
      right_inv h := by
        apply Multiplicative.toAdd.injective
        ext m
        simp }
  refine Nat.card_congr (c.subtypeEquiv fun h => ?_)
  simp only [mem_compatAddAut]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨e.symm.trans (φ.trans e), fun y' => ?_⟩
    simp only [c, Equiv.coe_fn_mk, toAdd_ofAdd, AddEquiv.trans_apply, he', hφ, he]
  · rintro ⟨φ', hφ'⟩
    refine ⟨e.trans (φ'.trans e.symm), fun y => ?_⟩
    have h1 := hφ' (e y)
    simp only [c, Equiv.coe_fn_mk, toAdd_ofAdd, AddEquiv.trans_apply, ← he,
      AddEquiv.symm_apply_apply] at h1
    simp only [AddEquiv.trans_apply]
    rw [← he', ← h1, AddEquiv.symm_apply_apply]

theorem diag_map_of_mem {h : Multiplicative (AddAut V)} (hh : h ∈ compatAddAut normW) (c x : V)
    (hcx : diag c x) : diag (Multiplicative.toAdd h c) (Multiplicative.toAdd h x) := by
  obtain ⟨φ, hφ⟩ := hh
  obtain ⟨a, b, rfl, hb, rfl⟩ := (diag_iff _ _).1 hcx
  refine (diag_iff _ _).2 ⟨φ a, φ b, (hφ a).symm, ?_, ?_⟩
  · rw [← hφ b, hb]
  · rw [← map_add, ← hφ (a + b)]

theorem admissibleN_basisValues {h : Multiplicative (AddAut V)} (hh : h ∈ compatAddAut normW) :
    AdmissibleN (basisValues (Multiplicative.toAdd h)) := by
  refine ⟨fun v hv => ?_, fun c x => ?_⟩
  · rw [← apply_eq_lin_basisValues] at hv
    exact (Multiplicative.toAdd h).map_eq_zero_iff.1 hv
  · rw [← apply_eq_lin_basisValues, ← apply_eq_lin_basisValues]
    refine ⟨diag_map_of_mem hh c x, fun hcx => ?_⟩
    have h1 := diag_map_of_mem (inv_mem hh) _ _ hcx
    simp only [toAdd_inv, AddAut.neg_apply, AddEquiv.symm_apply_apply] at h1
    exact h1

theorem card_compatAddAut_normW_le : Nat.card (compatAddAut normW) ≤ 21 := by
  rw [← card_admissibleN, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective
    (fun h => ⟨basisValues (Multiplicative.toAdd h.1), admissibleN_basisValues h.2⟩) ?_
  intro h₁ h₂ h12
  have h12' : basisValues (Multiplicative.toAdd h₁.1) = basisValues (Multiplicative.toAdd h₂.1) :=
    congrArg Subtype.val h12
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  refine AddEquiv.ext fun v => ?_
  rw [apply_eq_lin_basisValues, apply_eq_lin_basisValues, h12']

@[expose] noncomputable def addAutOfKer {M : Type*} [AddGroup M] [Finite M] (f : M → M)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hker : ∀ a, f a = 0 → a = 0) : AddAut M :=
  AddEquiv.ofBijective (AddMonoidHom.mk' f hadd)
    (Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero _).2 hker))

@[expose] noncomputable def frobAut : Multiplicative (AddAut V) :=
  Multiplicative.ofAdd (addAutOfKer frob frob_add frob_eq_zero)

@[expose] noncomputable def mulαAut : Multiplicative (AddAut V) :=
  Multiplicative.ofAdd (addAutOfKer mulα mulα_add mulα_eq_zero)

theorem frobAut_mem : frobAut ∈ compatAddAut normW :=
  ⟨addAutOfKer frob64 frob64_add frob64_eq_zero, fun a => (normW_frob64 a).symm⟩

theorem mulαAut_mem : mulαAut ∈ compatAddAut normW :=
  ⟨addAutOfKer scal scal_add scal_eq_zero, fun a => (normW_scal a).symm⟩

theorem toAdd_pow_succ_apply {M : Type*} [AddGroup M] (h : Multiplicative (AddAut M)) (k : ℕ)
    (v : M) :
    Multiplicative.toAdd (h ^ (k + 1)) v =
      Multiplicative.toAdd h (Multiplicative.toAdd (h ^ k) v) := by
  rw [pow_succ', toAdd_mul, AddAut.add_apply]

theorem orderOf_frobAut : orderOf frobAut = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ fun h1 => frob_ne ?_
  · apply Multiplicative.toAdd.injective
    refine AddEquiv.ext fun v => ?_
    simp only [toAdd_pow_succ_apply, pow_zero, toAdd_one, AddAut.zero_apply]
    exact frob_frob_frob v
  · have h2 := congrArg (fun f : Multiplicative (AddAut V) => Multiplicative.toAdd f (0, 1, 0)) h1
    exact h2

theorem orderOf_mulαAut : orderOf mulαAut = 7 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine orderOf_eq_prime ?_ fun h1 => mulα_ne ?_
  · apply Multiplicative.toAdd.injective
    refine AddEquiv.ext fun v => ?_
    simp only [toAdd_pow_succ_apply, pow_zero, toAdd_one, AddAut.zero_apply]
    exact mulα_seven v
  · have h2 := congrArg (fun f : Multiplicative (AddAut V) => Multiplicative.toAdd f (1, 0, 0)) h1
    exact h2

theorem card_compatAddAut_normW : Nat.card (compatAddAut normW) = 21 := by
  have h3 : 3 ∣ Nat.card (compatAddAut normW) := by
    have h := orderOf_dvd_natCard (⟨frobAut, frobAut_mem⟩ : compatAddAut normW)
    rwa [Subgroup.orderOf_mk, orderOf_frobAut] at h
  have h7 : 7 ∣ Nat.card (compatAddAut normW) := by
    have h := orderOf_dvd_natCard (⟨mulαAut, mulαAut_mem⟩ : compatAddAut normW)
    rwa [Subgroup.orderOf_mk, orderOf_mulαAut] at h
  have h21 : 21 ∣ Nat.card (compatAddAut normW) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
  have hpos : 0 < Nat.card (compatAddAut normW) := Nat.card_pos
  have hle := card_compatAddAut_normW_le
  obtain ⟨k, hk⟩ := h21
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

theorem card_compatAddAut_pow_nine {F Z : Type*} [Field F] [Finite F] [AddCommGroup Z]
    (hF : Nat.card F = 64) (hZ : Nat.card Z = 8) (ι : Z →+ F) (hι : Function.Injective ι)
    (N : F → Z) (hN : ∀ a, ι (N a) = a ^ 9) : Nat.card (compatAddAut N) = 21 := by
  have : CharP F 2 := charP_two_of_card_eq_sixtyFour hF
  obtain ⟨α, ω, hα, hω⟩ := exists_roots hF
  let e : W ≃+ F := AddEquiv.ofBijective (coord64 α ω) (coord64_bijective hF hα hω)
  have he : ∀ a, e a = coord64 α ω a := fun _ => rfl
  let f : V → Z := fun v => N (e (mul (mul v v) (mul v v), 0))
  have hf : ∀ v, ι (f v) = coord α v := fun v => by
    simp only [f, hN, he, coord64_pow_nine hα hω, normW_sqrt]
  have hfadd : ∀ v w, f (v + w) = f v + f w := fun v w => hι (by
    rw [map_add, hf, hf, hf, map_add])
  have hfinj : Function.Injective f := fun v w hvw =>
    coord_injective hα (by rw [← hf, ← hf, hvw])
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  let e' : V ≃+ Z := AddEquiv.ofBijective (AddMonoidHom.mk' f hfadd)
    ((Nat.bijective_iff_injective_and_card _).2 ⟨hfinj, by simp [hZ]⟩)
  have he' : ∀ a, e' (normW a) = N (e a) := fun a => hι (by
    change ι (f (normW a)) = _
    rw [hf, hN, he, coord64_pow_nine hα hω])
  rw [← card_compatAddAut_congr e e' he', card_compatAddAut_normW]

end UEight

open UEight

theorem card_dvd_21_of_norm_equivariant {F Z : Type*} [Field F] [Finite F] [AddCommGroup Z]
    (hF : Nat.card F = 64) (hZ : Nat.card Z = 8) (ι : Z →+ F) (hι : Function.Injective ι)
    (N : F → Z) (hN : ∀ a, ι (N a) = a ^ 9) (Γ : Subgroup (Multiplicative (AddAut Z)))
    (hΓ : ∀ h ∈ Γ, ∃ φ : AddAut F, ∀ a, Multiplicative.toAdd h (N a) = N (φ a)) :
    Nat.card Γ ∣ 21 := by
  rw [← card_compatAddAut_pow_nine hF hZ ι hι N hN]
  exact Subgroup.card_dvd_of_le hΓ

theorem not_injective_of_card_eq_168_of_norm_equivariant {F Z : Type*} [Field F] [Finite F]
    [AddCommGroup Z] (hF : Nat.card F = 64) (hZ : Nat.card Z = 8) (ι : Z →+ F)
    (hι : Function.Injective ι) (N : F → Z) (hN : ∀ a, ι (N a) = a ^ 9) {H : Type*} [Group H]
    (hH : Nat.card H = 168) (ρ : H →* Multiplicative (AddAut Z))
    (hρ : ∀ x, ∃ φ : AddAut F, ∀ a, Multiplicative.toAdd (ρ x) (N a) = N (φ a)) :
    ¬ Function.Injective ρ := by
  intro hinj
  have hdvd := card_dvd_21_of_norm_equivariant hF hZ ι hι N hN ρ.range (by
    rintro h ⟨x, rfl⟩
    exact hρ x)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hH] at hdvd
  norm_num at hdvd

theorem false_of_affine_card_eq_168_of_norm_equivariant {F Z : Type*} [Field F] [Finite F]
    [AddCommGroup Z] (hF : Nat.card F = 64) (hZ : Nat.card Z = 8) (ι : Z →+ F)
    (hι : Function.Injective ι) (N : F → Z) (hN : ∀ a, ι (N a) = a ^ 9)
    (X : Subgroup (Equiv.Perm Z)) (haff : ∀ x ∈ X, ∀ v w, x (v + w) + x 0 = x v + x w)
    (hX : Nat.card X = 168) (hs : IsSimpleGroup X)
    (hsq : ∀ x ∈ X, ∃ φ : AddAut F, ∀ a, x (N a) - x 0 = N (φ a)) : False := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  refine not_injective_of_card_eq_168_of_norm_equivariant hF hZ ι hι N hN hX
    (affineLinearPartHom X haff) (fun x => ?_) (affineLinearPartHom_injective X haff hs (by omega))
  obtain ⟨φ, hφ⟩ := hsq x x.2
  exact ⟨φ, fun a => by rw [affineLinearPartHom_apply]; exact hφ a⟩

end CFSG.SeitzReduction.RankOne
