module

public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint

theorem card_q8_four :
    (Finset.univ.filter fun x : QuaternionGroup 2 => x ^ 2 ≠ 1 ∧ x ^ 4 = 1).card = 6 := by
  decide

theorem card_d16_four :
    (Finset.univ.filter fun x : DihedralGroup 8 => x ^ 2 ≠ 1 ∧ x ^ 4 = 1).card = 2 := by
  decide

theorem not_injective_q8_d16 (φ : QuaternionGroup 2 →* DihedralGroup 8) :
    ¬ Function.Injective φ := by
  intro hφ
  have h := Finset.card_le_card_of_injOn φ
    (s := Finset.univ.filter fun x : QuaternionGroup 2 => x ^ 2 ≠ 1 ∧ x ^ 4 = 1)
    (t := Finset.univ.filter fun x : DihedralGroup 8 => x ^ 2 ≠ 1 ∧ x ^ 4 = 1)
    (fun x hx => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨fun h2 => hx.1 (hφ ?_), ?_⟩
      · rw [map_pow, h2, map_one]
      · rw [← map_pow, hx.2, map_one]) hφ.injOn
  rw [card_q8_four, card_d16_four] at h
  omega

variable {X : Type} [Group X] [Finite X]

theorem false_of_l32 {R : Subgroup X} {S : Sylow 2 R}
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a)
    (hL : LieModel (TL4.FStarQuot X) .PSL 3 2 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := hq
  obtain ⟨eF⟩ := nonempty_fstar_equiv (center_fstar_eq_bot hnab)
  have hn : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hE : Finite (TL4.FStarQuot X) := Finite.of_equiv _ eF.toEquiv
  have hA : Finite (MulAut (TL4.FStarQuot X)) :=
    Finite.of_injective (fun e : MulAut (TL4.FStarQuot X) => (e : TL4.FStarQuot X → _))
      fun e₁ e₂ h => MulEquiv.ext (congrFun h)
  obtain ⟨T, -, ⟨eT⟩⟩ := (CFSG.LieType.nq_Alt5_and_binary_GL3_full_automorphism_two_rank
    (TL4.FStarQuot X) (Or.inr hL)).2 hL
  let φ : X →* MulAut (TL4.FStarQuot X) :=
    (MulAut.congr eF).toMonoidHom.comp (MulAut.conjNormal (H := genFittingFStar X))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : MulAut.conjNormal (H := genFittingFStar X) x = 1 :=
      (MulAut.congr eF).injective (by rw [map_one]; exact hx)
    have hxC : x ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨h, hh⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc h * x = x * h * x⁻¹ * x := by rw [h2]
        _ = x * h := by group
    rwa [centralizer_genFittingFStar_eq_bot hnab, Subgroup.mem_bot] at hxC
  let ψ : QuaternionGroup 2 →* MulAut (TL4.FStarQuot X) :=
    φ.comp (R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom))
  have hψ : Function.Injective ψ :=
    hφ.comp (R.subtype_injective.comp (Subtype.val_injective.comp eS.symm.injective))
  have h8 : Nat.card (QuaternionGroup 2) = 2 ^ 3 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have h2 : IsPGroup 2 ψ.range :=
    (IsPGroup.of_card h8).of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨T', hT'⟩ := h2.exists_le_sylow
  let ι : QuaternionGroup 2 →* DihedralGroup 8 :=
    (eT.toMonoidHom.comp (Sylow.equiv T' T).toMonoidHom).comp
      (ψ.codRestrict (T' : Subgroup (MulAut (TL4.FStarQuot X))) fun x => hT' ⟨x, rfl⟩)
  exact not_injective_q8_d16 ι (eT.injective.comp ((Sylow.equiv T' T).injective.comp
    fun a b h => hψ (congrArg Subtype.val h)))

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2
