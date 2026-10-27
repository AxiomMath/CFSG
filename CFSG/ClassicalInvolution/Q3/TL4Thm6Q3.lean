module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.U33
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.GH74.Generic.S45.LEvSporM12Spec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover

theorem conjNormal_injective {Y : Type} [Group Y] {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : Y)) (MonoidHom.mem_ker.mp hy)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

theorem index_mul_card_le_of_injective {Y T : Type} [Group Y] [Finite Y] [Group T] [Finite T]
    (ι : Y →* T) (hι : Function.Injective ι) :
    (genFittingFStar Y).index * Nat.card ↥(genFittingFStar Y) ≤ Nat.card T := by
  rw [Subgroup.index_mul_card]
  exact Nat.card_le_card_of_injective ι hι

theorem dvd_six_of_le_two {n : ℕ} (h : n ≤ 2) (h0 : n ≠ 0) : n ∣ 6 := by
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl <;> norm_num

theorem exitIdent_l33 :
    ExitIdent fun F _ => CFSG.Blueprint.LieModel F .PSL 3 3 1 := by
  intro Y _ _ _ hnab hL R S t _ _
  have := genFittingFStar_normal Y
  obtain ⟨e⟩ := L33.equiv_of_lieModel hL
  have : Finite (MulAut ↥(genFittingFStar Y)) := L33.finite_mulAut e
  have h := index_mul_card_le_of_injective _
    (conjNormal_injective (Nobq.centralizer_genFittingFStar_eq_bot hnab))
  rw [L33.card_mulAut e, Nat.card_congr e.toEquiv, card_group _ L33.QP_ok, L33.QP_valid.2] at h
  exact Or.inl ⟨3, 1, Nat.prime_three, by norm_num, Or.inr
    ⟨Or.inl (lieModel_fstarQuot hnab (Or.inl rfl) hL),
      dvd_six_of_le_two (by omega) Subgroup.index_ne_zero_of_finite⟩⟩

theorem exitIdent_u33 :
    ExitIdent fun F _ => CFSG.Blueprint.LieModel F .PSU 3 3 1 := by
  intro Y _ _ _ hnab hL R S t _ _
  have := genFittingFStar_normal Y
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  have : Finite (MulAut ↥(genFittingFStar Y)) := U33.finite_mulAut e
  have h := index_mul_card_le_of_injective _
    (conjNormal_injective (Nobq.centralizer_genFittingFStar_eq_bot hnab))
  rw [U33.card_mulAut e, Nat.card_congr e.toEquiv, card_group _ U33.QP_ok, U33.QP_valid.2] at h
  exact Or.inl ⟨3, 1, Nat.prime_three, by norm_num, Or.inr
    ⟨Or.inr (lieModel_fstarQuot hnab (Or.inr rfl) hL),
      dvd_six_of_le_two (by omega) Subgroup.index_ne_zero_of_finite⟩⟩

theorem exitIdent_m12 :
    ExitIdent TA3.SmallM12 := by
  intro Y _ _ _ hnab hM R S t _ _
  have := genFittingFStar_normal Y
  obtain ⟨e⟩ := hM
  let θ : ↥(genFittingFStar Y) ≃* ↥blockGroup := e.trans m12EquivD
  have hι := GH74.Generic.S45.EvSpor.m12_smallAutModel.embed_injective (genFittingFStar Y) θ
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  let ι : Y →* ↥autModel :=
    (GH74.Generic.S45.EvSpor.m12_smallAutModel.embed (genFittingFStar Y) θ).codRestrict _
      fun y => GH74.Generic.S45.EvSpor.m12_smallAutModel.embed_mem _ θ y
  have h := index_mul_card_le_of_injective ι fun a b hab => hι (congrArg Subtype.val hab)
  have hP : Nat.card blockGroup = 95040 := by
    rw [blockGroup, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]
  rw [Nat.card_congr θ.toEquiv, hP, card_autModel] at h
  exact Or.inr ⟨⟨(fstarQuotEquiv hnab).trans e⟩, by omega⟩

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
