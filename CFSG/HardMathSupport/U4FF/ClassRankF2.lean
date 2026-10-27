module

public import CFSG.HardMathSupport.U4FF.ClassDescent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE matRepE_apply repD
  natCard_common_ker_map natCard_E_eq natCard_eq_pow_finrank)

namespace ClassFinal

section Generic

theorem natCard_fixed_matrix {E : Type} [Field E] [Finite E] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ E) :
    Nat.card {y : κ → E // M.mulVec y = y} = Nat.card E ^ (Fintype.card κ - (M - 1).rank) := by
  have hker : {y : κ → E // M.mulVec y = y} ≃ LinearMap.ker (Matrix.mulVecLin (M - 1)) :=
    Equiv.subtypeEquivRight fun y => by
      simp [LinearMap.mem_ker, Matrix.sub_mulVec, sub_eq_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (M - 1))
  rw [Nat.card_congr hker, Module.natCard_eq_pow_finrank (K := E)]
  congr 1
  unfold Matrix.rank
  simp only [Module.finrank_fintype_fun_eq_card] at hrn ⊢
  omega

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) G W} [Fact ρ.IsIrreducible]

theorem natCard_fix_pow_base {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type}
    [Field E] [Finite E] (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : G →* Matrix κ κ E) (Φ : (matRep R).Equiv (matRepE b ιD)) (z : G) :
    Nat.card {w : W // ρ z w = w} ^ (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) =
      Nat.card {y : κ → E // (R z).mulVec y = y} := by
  have hcoord : ∀ (g : G) (w : W),
      (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).mulVec (b.equivFun w) =
        b.equivFun (ρ g w) := fun g w =>
    LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h1 : {w : W // ρ z w = w} ≃
      {x : Fin m → EndRing ρ //
        ∀ _ : Unit, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).mulVec x = 0} :=
    Equiv.subtypeEquiv b.equivFun.toEquiv (fun w => by
      change ρ z w = w ↔
        ∀ _ : Unit, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).mulVec
          (b.equivFun w) = 0
      constructor
      · intro h _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, h, sub_self]
      · intro h
        have := h ()
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hcoord, sub_eq_zero] at this
        exact b.equivFun.injective this)
  have h2 := natCard_common_ker_map ιD
    (fun _ : Unit => CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1)
  have h3 : {x : Fin m → E // ∀ _ : Unit,
      ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x = 0} ≃
      {y : κ → E // (R z).mulVec y = y} :=
    Equiv.subtypeEquiv Φ.symm.toLinearEquiv.toEquiv (fun x => by
      have hsub : ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b z - 1).map ιD).mulVec x =
          matRepE b ιD z x - x := by
        rw [matRepE_apply, Matrix.map_sub _ (fun a b => map_sub ιD a b),
          Matrix.map_one ιD (map_zero ιD) (map_one ιD), Matrix.sub_mulVec, Matrix.one_mulVec]
      have hint : Φ.symm (matRepE b ιD z x) = (R z).mulVec (Φ.symm x) :=
        CFSG.QuasithinUnique.Setup.SL2Modules.equiv_apply Φ.symm z x
      change (∀ _ : Unit, _ = 0) ↔ (R z).mulVec (Φ.symm x) = Φ.symm x
      rw [← hint, hsub]
      constructor
      · intro h
        rw [sub_eq_zero.mp (h ())]
      · intro h _
        rw [sub_eq_zero]
        exact Φ.symm.toLinearEquiv.injective h)
  rw [Nat.card_congr h1]
  rw [Nat.card_congr h3] at h2
  exact h2.symm

omit [Fact ρ.IsIrreducible] in
theorem natCard_eq_two_pow_finrank_base (U : Type) [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_range_eq_base {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E]
    (ιD : EndRing ρ →+* E) {κ : Type} [Fintype κ] [DecidableEq κ] (R : G →* Matrix κ κ E)
    (Φ : (matRep R).Equiv (matRepE b ιD))
    (hdim : Module.finrank (EndRing ρ) W = Fintype.card κ) (z : G) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = d * (R z - 1).rank := by
  classical
  let _ := ιD.toAlgebra
  have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  set e := Module.finrank (EndRing ρ) E with he
  have he0 : 0 < e := Module.finrank_pos
  set r := (R z - 1).rank with hr
  have hrle : r ≤ Fintype.card κ := by
    have h := (R z - 1).rank_le_card_height
    simpa [hr] using h
  have hfixR : Nat.card {y : κ → E // (R z).mulVec y = y} =
      Nat.card E ^ (Fintype.card κ - r) := natCard_fixed_matrix (R z)
  have hcount := natCard_fix_pow_base b ιD R Φ z
  rw [hfixR, natCard_E_eq ιD, hDcard, ← pow_mul, ← pow_mul, ← he] at hcount
  have hfixW : Nat.card {w : W // ρ z w = w} = 2 ^ (d * (Fintype.card κ - r)) := by
    have h1 : Nat.card {w : W // ρ z w = w} ^ e = (2 ^ (d * (Fintype.card κ - r))) ^ e := by
      rw [hcount, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_left_injective he0.ne' h1
  have hker : Nat.card {w : W // ρ z w = w} = Nat.card (LinearMap.ker (ρ z - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero])
  have hkerF : Module.finrank (ZMod 2) (LinearMap.ker (ρ z - 1)) =
      d * (Fintype.card κ - r) := by
    have h1 := natCard_eq_two_pow_finrank_base (LinearMap.ker (ρ z - 1))
    rw [← hker, hfixW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hWF : Module.finrank (ZMod 2) W = d * Fintype.card κ := by
    have h1 := natCard_eq_two_pow_finrank_base W
    rw [natCard_eq_pow_finrank (ρ := ρ), hDcard, hdim, ← pow_mul] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (ρ z - 1)
  rw [hkerF, hWF] at hrn
  have h4 : d * (Fintype.card κ - r) + d * r = d * Fintype.card κ := by
    rw [← mul_add, Nat.sub_add_cancel hrle]
  omega

end Generic

end ClassFinal

section Tmod

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {ρ : Representation (ZMod 2) (SU4 K n) W} [Fact ρ.IsIrreducible]

theorem finrank_range_Tmod {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E] [CharP E 2]
    [Algebra K E] (ιD : EndRing ρ →+* E) (l : Lbl n)
    (Φ : (matRep (Tmod K l E)).Equiv (matRepE b ιD))
    (hdim : Module.finrank (EndRing ρ) W = l.dim) (z : SU4 K n) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = d * (Tmod K l E z - 1).rank :=
  ClassFinal.finrank_range_eq_base hDcard b ιD (Tmod K l E) Φ (by rw [hdim, card_TIdx]) z

end Tmod

end CFSG.HardMathSupport.U4FF
