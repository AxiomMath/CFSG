module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QCore
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Subgroup

namespace GenLocL4Q

variable {F : Type} [Field F]

@[expose] def IsInnerDiag4 {F : Type} [Field F] (φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) : Prop :=
  ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
    ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

section Glue

variable {A : Type} [Group A]

theorem lift_sq_scalar (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) {e : A} (he : e * e = 1)
    {u : GL (Fin 4) F}
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α e g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∃ l : F, (u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) = l • 1 := by
  refine GenLocL4Ext.exists_scalar_of_commute_sl fun g => ?_
  have h1 : (α e) ((α e) g) = g := by
    have : α e * α e = 1 := by rw [← map_mul, he, map_one]
    exact congrArg (fun φ : MulAut _ => φ g) this
  have h2 := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) F => (z : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [hu] at h2
  have hu1 : ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) = 1 := u.inv_mul
  have hu2 : (u : Matrix (Fin 4) (Fin 4) F) * ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := u.mul_inv
  have h3 : (u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * ((u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F)) := by
    have e1 : ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F))) = 1 := by
      rw [← Matrix.mul_assoc ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (u : Matrix (Fin 4) (Fin 4) F) (u : Matrix (Fin 4) (Fin 4) F),
        hu1, one_mul, hu1]
    calc (u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)
        = ((u : Matrix (Fin 4) (Fin 4) F) * ((u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
            ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
            ((u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F)) := by
          simp only [Matrix.mul_assoc]
          rw [e1]; simp
      _ = (g : Matrix (Fin 4) (Fin 4) F) * ((u : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F)) := by rw [h2]
  exact h3.symm

theorem not_scalar_of_anticomm (h2 : (2 : F) ≠ 0) {u v : GL (Fin 4) F}
    (huv : (u : Matrix (Fin 4) (Fin 4) F) * v = -((v : Matrix (Fin 4) (Fin 4) F) * u)) :
    ¬ ∃ l : F, (u : Matrix (Fin 4) (Fin 4) F) = l • 1 := by
  rintro ⟨l, hl⟩
  have hv0 : (v : Matrix (Fin 4) (Fin 4) F) ≠ 0 := Units.ne_zero v
  have hu0 : (u : Matrix (Fin 4) (Fin 4) F) ≠ 0 := Units.ne_zero u
  rw [hl, smul_mul_assoc, one_mul, Matrix.mul_smul, Matrix.mul_one] at huv
  have h4 : l • (v : Matrix (Fin 4) (Fin 4) F) + l • (v : Matrix (Fin 4) (Fin 4) F) = 0 := by
    nth_rewrite 2 [huv]; exact add_neg_cancel _
  have h3 : (2 * l) • (v : Matrix (Fin 4) (Fin 4) F) = 0 := by rw [two_mul, add_smul]; exact h4
  rcases smul_eq_zero.1 h3 with h | h
  · have hl0 : l = 0 := (mul_eq_zero.1 h).resolve_left h2
    exact hu0 (by rw [hl, hl0, zero_smul])
  · exact hv0 h

theorem ne_one_of_lift (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) {e : A} {u : GL (Fin 4) F}
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α e g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hns : ¬ ∃ l : F, (u : Matrix (Fin 4) (Fin 4) F) = l • 1) : e ≠ 1 := by
  rintro rfl
  refine hns (GenLocL4Ext.exists_scalar_of_commute_sl fun g => ?_)
  have h1 := hu g
  rw [map_one, MulAut.one_apply] at h1
  calc (g : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F)
      = ((u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * (u : Matrix (Fin 4) (Fin 4) F) := by rw [← h1]
    _ = (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
        rw [Matrix.mul_assoc, u.inv_mul, Matrix.mul_one]

theorem adm_zpowers_of_rank_two [Finite A] (hA : IsRank23 A) (hr : pRank 2 A = 2) {e : A} (he1 : e ≠ 1) :
    pRank 2 A - 1 ≤ pRank 2 ↥(Subgroup.zpowers e) := by
  have he2 : e * e = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
  have hcardA : Nat.card A = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hr]; norm_num
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers e)
  rw [Nat.card_zpowers, hord, hcardA] at h1
  exact (GenLocBasic.adm_iff_index hA.1 _).2 (by omega)

theorem mem_gammaAct_of_commute (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) {e : A}
    {u : GL (Fin 4) F}
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α e g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hadm : pRank 2 A - 1 ≤ pRank 2 ↥(Subgroup.zpowers e)) (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) : g ∈ gammaAct α := by
  have hα : α e g = g := by
    apply Subtype.ext
    rw [hu g, ← hg, Matrix.mul_assoc, u.mul_inv, Matrix.mul_one]
  have hstab : α e ∈ MulAction.stabilizer (MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) g := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hα
  refine le_gammaAct α hadm ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro f hf
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
  have := (MulAction.stabilizer (MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) g).zpow_mem hstab n
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  rwa [map_zpow]


theorem gammaAct_quat_rank2 [Finite F] [Finite A] (hF : ringChar F ≠ 2)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A) (hr : pRank 2 A = 2)
    (x y : GL (Fin 4) F) (a b : A)
    (hax : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hby : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α b g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (y : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((y⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hanti : (x : Matrix (Fin 4) (Fin 4) F) * (y : Matrix (Fin 4) (Fin 4) F) =
      -((y : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F))) : gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have haa : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 b
  obtain ⟨c, hc⟩ := lift_sq_scalar α haa hax
  obtain ⟨m, hm⟩ := lift_sq_scalar α hbb hby
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (((x * x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hc, zero_smul]
    exact Units.ne_zero _ this
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : (((y * y : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hm, zero_smul]
    exact Units.ne_zero _ this
  have hyx : (y : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
      -((x : Matrix (Fin 4) (Fin 4) F) * (y : Matrix (Fin 4) (Fin 4) F)) := by rw [hanti]; simp
  have hxyx : ((x * y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
      -((x : Matrix (Fin 4) (Fin 4) F) * ((x * y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
    rw [Units.val_mul, Matrix.mul_assoc, hyx, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_assoc]
  have hab : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α (a * b) g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((x * y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          (((x * y)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g
    rw [map_mul, MulAut.mul_apply, hax, hby, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]
  have hnx := not_scalar_of_anticomm h2 hanti
  have hny := not_scalar_of_anticomm h2 (by rw [hyx] : (y : Matrix (Fin 4) (Fin 4) F) * x = -(x * y))
  have hnxy := not_scalar_of_anticomm h2 hxyx
  have ha1 : a ≠ 1 := ne_one_of_lift α hax hnx
  have hb1 : b ≠ 1 := ne_one_of_lift α hby hny
  have hab1 : a * b ≠ 1 := ne_one_of_lift α hab hnxy
  have hxx : (x : Matrix (Fin 4) (Fin 4) F) * x = c • 1 := hc
  have hyy : (y : Matrix (Fin 4) (Fin 4) F) * y = m • 1 := hm
  refine eq_top_of_commuting_centralizers hF hc0 hm0 hxx hyy hanti (gammaAct α) ?_ ?_ ?_
  · intro g hg
    exact mem_gammaAct_of_commute α hax (adm_zpowers_of_rank_two hA hr ha1) g hg
  · intro g hg
    exact mem_gammaAct_of_commute α hby (adm_zpowers_of_rank_two hA hr hb1) g hg
  · intro g hg
    refine mem_gammaAct_of_commute α hab (adm_zpowers_of_rank_two hA hr hab1) g ?_
    rw [Units.val_mul]; exact hg

end Glue

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
