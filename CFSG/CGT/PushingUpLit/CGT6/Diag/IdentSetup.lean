module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Ident

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

section Act

variable {V : Type} [CommGroup V]

@[expose] noncomputable def actV (H : Subgroup (MulAut V)) : ↥H →* AddMonoid.End (Additive V) where
  toFun h := AddMonoidHom.mk' (fun a => Additive.ofMul ((h : MulAut V) (Additive.toMul a)))
    (fun a b => by simp [map_mul])
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

theorem actV_apply (H : Subgroup (MulAut V)) (h : ↥H) (a : Additive V) :
    actV H h a = Additive.ofMul ((h : MulAut V) (Additive.toMul a)) := rfl

@[expose] noncomputable def actW (K : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W) : ↥K →* AddMonoid.End (Additive ↥W) where
  toFun k := AddMonoidHom.mk'
    (fun a => Additive.ofMul (⟨(k : MulAut V) (Additive.toMul a : W),
      hW k k.2 _ (Additive.toMul a : W).2⟩ : W))
    (fun a b => by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [map_mul])
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

theorem actW_apply (K : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W) (k : ↥K) (a : Additive ↥W) :
    actW K W hW k a = Additive.ofMul (⟨(k : MulAut V) (Additive.toMul a : W),
      hW k k.2 _ (Additive.toMul a : W).2⟩ : W) := rfl

@[expose] noncomputable def phiMap (W : Subgroup V) (k₀ : MulAut V) :
    Additive ↥W × Additive ↥W →+ Additive V :=
  AddMonoidHom.mk' (fun p => Additive.ofMul
    ((Additive.toMul p.1 : W) * k₀ (Additive.toMul p.2 : W)))
    (fun p q => by
      apply Additive.toMul.injective
      simp only [Prod.fst_add, Prod.snd_add, toMul_add, toMul_ofMul, Subgroup.coe_mul, map_mul]
      exact mul_mul_mul_comm _ _ _ _)

theorem phiMap_apply (W : Subgroup V) (k₀ : MulAut V) (p : Additive ↥W × Additive ↥W) :
    phiMap W k₀ p = Additive.ofMul
      ((Additive.toMul p.1 : W) * k₀ (Additive.toMul p.2 : W)) := rfl

theorem phiMap_bijective {W : Subgroup V} {k₀ : MulAut V} (hinf : W ⊓ diagImg k₀ W = ⊥)
    (hsup : W ⊔ diagImg k₀ W = ⊤) : Function.Bijective (phiMap W k₀) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : ((Additive.toMul x : W) : V) * k₀ ((Additive.toMul y : W) : V) =
        ((Additive.toMul x' : W) : V) * k₀ ((Additive.toMul y' : W) : V) :=
      Additive.ofMul.injective h
    have h3 : ((Additive.toMul x : W) : V) / ((Additive.toMul x' : W) : V) =
        k₀ ((Additive.toMul y' : W) : V) / k₀ ((Additive.toMul y : W) : V) := by
      rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
    have h2 : ((Additive.toMul x : W) : V) / ((Additive.toMul x' : W) : V) ∈
        W ⊓ diagImg k₀ W := by
      refine ⟨W.div_mem (Additive.toMul x : W).2 (Additive.toMul x' : W).2, ?_⟩
      refine ⟨((Additive.toMul y' : W) : V) / ((Additive.toMul y : W) : V),
        W.div_mem (Additive.toMul y' : W).2 (Additive.toMul y : W).2, ?_⟩
      rw [h3]
      exact map_div k₀ _ _
    rw [hinf, Subgroup.mem_bot, div_eq_one] at h2
    have h4 : ((Additive.toMul y : W) : V) = ((Additive.toMul y' : W) : V) := by
      rw [h2] at h1
      exact k₀.injective (mul_left_cancel h1).symm.symm
    have hx : x = x' := Additive.toMul.injective (Subtype.ext h2)
    have hy : y = y' := Additive.toMul.injective (Subtype.ext h4)
    rw [hx, hy]
  · intro v
    have hv : v.toMul ∈ W ⊔ diagImg k₀ W := by rw [hsup]; trivial
    obtain ⟨w, hw, z, hz, hwz⟩ := Subgroup.mem_sup.mp hv
    obtain ⟨u, hu, rfl⟩ := hz
    refine ⟨(Additive.ofMul ⟨w, hw⟩, Additive.ofMul ⟨u, hu⟩), ?_⟩
    apply Additive.toMul.injective
    exact hwz

theorem hsimple_of_minInv {K : Subgroup (MulAut V)} {W : Subgroup V} (hW : DiagMinInv K W) :
    ∀ N : AddSubgroup (Additive ↥W), (∀ k : ↥K, ∀ a ∈ N, actW K W hW.2.1 k a ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
  intro N hN
  let Q : Subgroup ↥W :=
    { carrier := {w | Additive.ofMul w ∈ N}
      mul_mem' := fun {a b} ha hb => N.add_mem ha hb
      one_mem' := N.zero_mem
      inv_mem' := fun {a} ha => N.neg_mem ha }
  let P : Subgroup V := Q.map W.subtype
  have hPW : P ≤ W := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  have hPinv : GInv K P := by
    rintro k hk _ ⟨w, hw, rfl⟩
    refine ⟨⟨k w, hW.2.1 k hk w w.2⟩, ?_, rfl⟩
    exact hN ⟨k, hk⟩ _ hw
  rcases hW.2.2 P hPinv hPW with h | h
  · left
    rw [AddSubgroup.eq_bot_iff_forall]
    intro a ha
    have h1 : ((Additive.toMul a : W) : V) ∈ P := ⟨Additive.toMul a, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact Additive.toMul.injective (Subtype.ext h1)
  · right
    rw [AddSubgroup.eq_top_iff']
    intro a
    have h1 : ((Additive.toMul a : W) : V) ∈ P := by
      rw [h]
      exact (Additive.toMul a : W).2
    obtain ⟨w, hw, hwa⟩ := h1
    have h2 : w = Additive.toMul a := Subtype.ext hwa
    rw [h2] at hw
    exact hw

end Act

section SL

theorem sl2Fq_isSimple {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) := by
  have hK : 4 ≤ Nat.card (Fq n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcen := sl2_center_eq_bot (Fq n)
  have hinj : Function.Injective (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Fq n)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  let e₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Fq n) :=
    MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Fq n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  exact MulEquiv.isSimpleGroup e₀

theorem sl2Fq_isPerfect {n : ℕ} (hn : 2 ≤ n) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) := by
  apply CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
  rw [GaloisField.card 2 n (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end SL

end CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
