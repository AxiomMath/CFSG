
module

public import CFSG.LieType.ChevTwo.InversionVacuousCert
public import CFSG.LieType.ChevTwo.InversionCheck

@[expose] public section

namespace CFSG.LieType.ChevTwo

theorem chev2RankTwoInverts
    : Chev2RankTwoInverts :=
  chev2RankTwoInverts_of_certs

namespace GL4Native

@[expose] def toL (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : List (ZMod 2) :=
  List.ofFn fun k : Fin 16 => A (ij k).1 (ij k).2

theorem ij_fst (k : Fin 16) : (ij k).1.val = k.val / 4 := rfl
theorem ij_snd (k : Fin 16) : (ij k).2.val = k.val % 4 := rfl

theorem ij_eq_of (i j : Fin 4) (k : Fin 16) (hk : k.val = 4 * i.val + j.val) :
    ij k = (i, j) := by
  apply Prod.ext
  · apply Fin.ext
    rw [ij_fst, hk]
    dsimp only
    omega
  · apply Fin.ext
    rw [ij_snd, hk]
    dsimp only
    omega

theorem getD_ofFn_eq (f : Fin 16 → ZMod 2) (n : ℕ) (hn : n < 16) :
    (List.ofFn f).getD n 0 = f ⟨n, hn⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hn, dite_true, Option.getD_some]

theorem ent_toL (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    ent (toL A) i j = A i j := by
  unfold ent toL
  rw [getD_ofFn_eq _ _ (by omega)]
  have : ij ⟨4 * i.val + j.val, by omega⟩ = (i, j) := ij_eq_of i j _ rfl
  simp only [this]

theorem ent_toL' (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    ent (toL A) i j = A ⟨i, hi⟩ ⟨j, hj⟩ :=
  ent_toL A ⟨i, hi⟩ ⟨j, hj⟩

theorem toL_injective {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : toL A = toL B) : A = B := by
  ext i j
  rw [← ent_toL A i j, ← ent_toL B i j, h]

theorem mulL_toL (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    mulL (toL A) (toL B) = toL (A * B) := by
  have hR : toL (A * B) = List.ofFn fun k : Fin 16 => (A * B) (ij k).1 (ij k).2 := rfl
  rw [hR]
  unfold mulL
  congr 1
  funext k
  have hk1 : k.val / 4 < 4 := by omega
  have hk2 : k.val % 4 < 4 := by omega
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  rw [ent_toL' _ _ _ hk1 (by norm_num : (0:ℕ) < 4), ent_toL' _ _ _ (by norm_num : (0:ℕ) < 4) hk2,
    ent_toL' _ _ _ hk1 (by norm_num : (1:ℕ) < 4), ent_toL' _ _ _ (by norm_num : (1:ℕ) < 4) hk2,
    ent_toL' _ _ _ hk1 (by norm_num : (2:ℕ) < 4), ent_toL' _ _ _ (by norm_num : (2:ℕ) < 4) hk2,
    ent_toL' _ _ _ hk1 (by norm_num : (3:ℕ) < 4), ent_toL' _ _ _ (by norm_num : (3:ℕ) < 4) hk2]
  rfl

theorem oneL_toL : toL (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = oneL := by
  unfold toL oneL
  rfl

theorem powL_toL (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (n : ℕ) :
    powL (toL A) n = toL (A ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [powL, dif_pos rfl, pow_zero, oneL_toL]
    · have hhalf : powL (toL A) (n / 2) = toL (A ^ (n / 2)) := ih (n / 2) (by omega)
      rw [powL, dif_neg h0]
      dsimp only
      rw [hhalf, mulL_toL]
      by_cases hodd : n % 2 = 1
      · rw [if_pos hodd, mulL_toL]
        congr 1
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      · rw [if_neg hodd]
        congr 1
        rw [← pow_add]
        congr 1
        omega

theorem trL_toL (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : trL (toL A) = A.trace := by
  unfold trL
  rw [ent_toL' _ 0 0 (by norm_num) (by norm_num), ent_toL' _ 1 1 (by norm_num) (by norm_num),
    ent_toL' _ 2 2 (by norm_num) (by norm_num), ent_toL' _ 3 3 (by norm_num) (by norm_num)]
  simp [Matrix.trace, Fin.sum_univ_four]

end GL4Native

namespace OffNative

@[expose] def glEquivAut : GL (Fin 4) (ZMod 2) ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2))

@[expose] def prodHom (U W : Type) [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W]
    [Module (ZMod 2) W] : (U ≃ₗ[ZMod 2] U) →* ((U × W) ≃ₗ[ZMod 2] (U × W)) where
  toFun g := LinearEquiv.prodCongr g (LinearEquiv.refl (ZMod 2) W)
  map_one' := by
    ext ⟨u, w⟩ <;> simp
  map_mul' g h := by
    ext ⟨u, w⟩ <;> simp

theorem prodHom_injective (U W : Type) [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W]
    [Module (ZMod 2) W] : Function.Injective (prodHom U W) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext u
  have := congrArg (fun T : (U × W) ≃ₗ[ZMod 2] (U × W) => (T (u, 0)).1) hg
  simpa [prodHom] using this

theorem neg_eq_self_of_zmod2 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (y : V) : -y = y := by
  have h2 : y + y = 0 := by
    rw [← two_smul (ZMod 2) y]
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, zero_smul]
  exact (eq_neg_of_add_eq_zero_left h2).symm

end OffNative

end CFSG.LieType.ChevTwo
