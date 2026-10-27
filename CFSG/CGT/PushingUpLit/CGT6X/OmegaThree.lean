module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAdm
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightPlus
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus
public import CFSG.CGT.PushingUpLit.CGT6X.OmegaThreeLine
public import CFSG.CGT.PushingUpLit.CGT6X.OmegaThreeCommV

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.Quasithin
  CFSG.CGT.PushingUpLit.BHS6

section Generic

variable {V : Type} [CommGroup V] [Finite V] {F L : Type} [Field F] [AddCommGroup L] [Module F L]
  [CharP F 2] [Finite F] [Finite L]

theorem commV_gt_four {X Y : Subgroup (MulAut V)} (hYX : Y ≤ X) (hY3 : Nat.card ↥Y = 3)
    (D : Data F L) (hF : 4 ≤ Nat.card F) {S : Type} [Group S] (ρ : S →* Equiv.Perm (Wd F L))
    (hρ : Function.Injective ρ) (hadd : ∀ s, IsAddPerm (ρ s)) (hQ : ∀ s w, Qt D (ρ s w) = Qt D w)
    (hsmul : ∀ (s : S) (c : F) (w : Wd F L), ρ s (c • w) = c • ρ s w) (θ : ↥X ≃* S)
    (Φ : ↥(commV X) ≃* Multiplicative (Wd F L))
    (hPX : ∀ e ∈ X, ∀ p ∈ commV X, e p ∈ commV X)
    (hΦ : ∀ (e : ↥X) (p : ↥(commV X)) (hp : (e : MulAut V) (p : V) ∈ commV X),
      Φ ⟨(e : MulAut V) (p : V), hp⟩ =
        Multiplicative.ofAdd (ρ (θ e) (Multiplicative.toAdd (Φ p)))) :
    4 < Nat.card ↥(commV Y) := by
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 h
    rw [hbot, Subgroup.card_bot] at hY3
    omega
  have hyX : y ∈ X := hYX hyY
  have hy3 : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨y, hyY⟩ : ↥Y))
    rw [hY3] at h
    exact congrArg Subtype.val h
  set e : ↥X := ⟨y, hyX⟩ with he
  have he1 : e ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have he3 : e * e * e = 1 := Subtype.ext (by
    show y * y * y = 1
    rw [← pow_three', hy3])
  set s : S := θ e with hs
  have hs1 : s ≠ 1 := fun h => he1 (θ.injective (by rw [map_one]; exact h))
  have hs3 : s * s * s = 1 := by rw [hs, ← map_mul, ← map_mul, he3, map_one]
  have h3 : ∀ w, ρ s (ρ s (ρ s w)) = w := fun w => by
    have h : (ρ s * ρ s * ρ s) w = w := by
      rw [← map_mul, ← map_mul, hs3, map_one]
      rfl
    exact h
  have h1 : ∃ w, ρ s w ≠ w := by
    by_contra h
    push Not at h
    exact hs1 (hρ (by rw [map_one]; exact Equiv.ext h))
  have hlow := four_lt_ncard_range D hF (hadd s) (hQ s) (hsmul s) h3 h1
  have hup := ncard_le_card_commV hyY (hPX y hyX) Φ (ρ s) (fun p hp => hΦ e p hp)
  have hset : {z : Wd F L | ∃ w, z = ρ s w - w} = {z : Wd F L | ∃ w, z = ρ s w + w} := by
    ext z
    have hneg : ∀ w : Wd F L, -w = w := fun w => neg_eq_of_add_eq_zero_left (wd_add_self_gen w)
    show (∃ w : Wd F L, z = ρ s w - w) ↔ ∃ w : Wd F L, z = ρ s w + w
    simp only [sub_eq_add_neg, hneg]
  rw [hset] at hup
  exact lt_of_lt_of_le hlow hup

end Generic

section Plus

variable (n : ℕ)

theorem plusHom_smul (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n) ×
    Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (c : Fq n) (w : Wd (Fq n) (Fq n × Fq n)) :
    plusHom n g (c • w) = c • plusHom n g w := by
  obtain ⟨m, rfl⟩ := (plusCoord n).surjective w
  have h1 : c • plusCoord n m = plusCoord n (c • m) := rfl
  have h2 : plusMat n g (c • m) = c • plusMat n g m := by
    simp [plusMat]
  rw [h1, plusHom_apply, plusHom_apply, h2]
  rfl

theorem four_le_card_Fq (hn : 2 ≤ n) : 4 ≤ Nat.card (Fq n) := by
  rw [GaloisField.card 2 n (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem plus_case {V : Type} [CommGroup V] [Finite V] {X Y : Subgroup (MulAut V)} (hn : 2 ≤ n)
    (hYX : Y ≤ X) (hY3 : Nat.card ↥Y = 3)
    (hplus : IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥) : 4 < Nat.card ↥(commV Y) := by
  obtain ⟨hPX, θ, β, hβ⟩ := natSection_equiv hplus
  refine commV_gt_four hYX hY3 (plusData n) (four_le_card_Fq n hn) (plusHom n)
    (plusHom_injective n) (plusHom_isAdd n) (plusHom_Q n) (plusHom_smul n) θ
    (β.trans (AddEquiv.toMultiplicative (plusCoord n))) hPX ?_
  intro e p hp
  show Multiplicative.ofAdd (plusCoord n (Multiplicative.toAdd (β ⟨(e : MulAut V) (p : V), hp⟩))) =
    Multiplicative.ofAdd (plusHom n (θ e) (plusCoord n (Multiplicative.toAdd (β p))))
  rw [hβ e p hp, plusHom_apply]
  rfl

end Plus

section Minus

variable (n : ℕ) [NeZero n]

theorem minusHom_smul (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (c : Fz n)
    (w : Wd (Fz n) (Fq (2 * n))) : minusHom n A (c • w) = c • minusHom n A w := by
  obtain ⟨p, y, s⟩ := w
  have hcs : c • ((p, y, s) : Wd (Fz n) (Fq (2 * n))) = (c * p, c • y, c * s) := rfl
  have hmat : (!![((c * p : Fz n) : Fq (2 * n)), c • y; sigR n (c • y),
      ((c * s : Fz n) : Fq (2 * n))] : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) =
      (c : Fq (2 * n)) • !![(p : Fq (2 * n)), y; sigR n y, (s : Fq (2 * n))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fz_smul, map_mul, sigR_Fz]
  obtain ⟨e1, e2, e3⟩ := minusHom_entries n A (c * p) (c * s) (c • y)
  obtain ⟨f1, f2, f3⟩ := minusHom_entries n A p s y
  rw [hcs]
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
  · show ((minusHom n A (c * p, c • y, c * s)).1 : Fq (2 * n)) =
      ((c * (minusHom n A (p, y, s)).1 : Fz n) : Fq (2 * n))
    rw [e1, hmat, MulMemClass.coe_mul, f1]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  · show (minusHom n A (c * p, c • y, c * s)).2.1 =
      (c : Fq (2 * n)) * (minusHom n A (p, y, s)).2.1
    rw [e2, hmat, f2]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  · show ((minusHom n A (c * p, c • y, c * s)).2.2 : Fq (2 * n)) =
      ((c * (minusHom n A (p, y, s)).2.2 : Fz n) : Fq (2 * n))
    rw [e3, hmat, MulMemClass.coe_mul, f3]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem four_le_card_Fz (hn : 2 ≤ n) : 4 ≤ Nat.card (Fz n) := by
  rw [card_Fz]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem minus_case {V : Type} [CommGroup V] [Finite V] {X Y : Subgroup (MulAut V)} (hn : 2 ≤ n)
    (hYX : Y ≤ X) (hY3 : Nat.card ↥Y = 3)
    (hminus : IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥) : 4 < Nat.card ↥(commV Y) := by
  obtain ⟨hPX, θ, β, hβ⟩ := natSection_equiv hminus
  refine commV_gt_four hYX hY3 (minusData n) (four_le_card_Fz n hn) (minusHom n)
    (minusHom_injective n) (minusHom_isAdd n) (minusHom_Q n) (minusHom_smul n) θ
    (β.trans (AddEquiv.toMultiplicative (minusCoord n))) hPX ?_
  intro e p hp
  show Multiplicative.ofAdd (minusCoord n (Multiplicative.toAdd (β ⟨(e : MulAut V) (p : V), hp⟩))) =
    Multiplicative.ofAdd (minusHom n (θ e) (minusCoord n (Multiplicative.toAdd (β p))))
  rw [hβ e p hp]
  exact congrArg Multiplicative.ofAdd (actPerm_apply (omegaMinusAct n) (omegaMinusAct_one n)
    (omegaMinusAct_mul n) (minusKappa n) (θ e) (β p)).symm

end Minus

theorem omega4OrderThree_holds : Omega4OrderThree := by
  intro V _ _ _ n hn X Y hX hYX hY3
  rcases hX with hplus | hminus
  · exact plus_case n hn hYX hY3 hplus
  · have : NeZero n := ⟨by omega⟩
    exact minus_case n hn hYX hY3 hminus

end CFSG.CGT.PushingUpLit.CGT6X
