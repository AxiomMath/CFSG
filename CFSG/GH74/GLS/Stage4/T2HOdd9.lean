module

public import CFSG.GH74.GLS.Stage4.T2SylSL
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.IVK.Lifted

theorem t2H_ringAut_sq_nine {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (σ : F ≃+* F) : σ ^ 2 = 1 := by
  have hc : Nat.card (F ≃+* F) = 2 :=
    CFSG.GH74.GLS.IVK.card_ringAut F 3 2 Nat.prime_three (by rw [hF]; norm_num)
  have := pow_card_eq_one' (G := F ≃+* F) (x := σ)
  rwa [hc] at this

theorem t2H_pgl_odd_mem {F : Type} [Field F] [Finite F] (_hodd : Odd (Nat.card F))
    (g : CFSG.GorensteinWalter.PGL2 F) (hg : Odd (orderOf g)) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_odd_orderOf hg

theorem t2H_inner_of_odd_sl9 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) F →*
      MulAut (Matrix.SpecialLinearGroup (Fin 2) F)).range := by
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have h3 : 3 < Nat.card F := by rw [hF]; norm_num
  have hγo : orderOf (gammaOf hodd h3 α) ∣ orderOf α := orderOf_map_dvd (gammaOf hodd h3) α
  have hσ : (gammaOf hodd h3 α).right = 1 := by
    have h1 : orderOf (gammaOf hodd h3 α).right ∣ orderOf α :=
      (orderOf_map_dvd SemidirectProduct.rightHom (gammaOf hodd h3 α)).trans hγo
    have h2 : orderOf (gammaOf hodd h3 α).right ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (t2H_ringAut_sq_nine hF _)
    have hcop : Nat.Coprime (orderOf (gammaOf hodd h3 α).right) 2 :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_right.mpr hα)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)
  have hγ : gammaOf hodd h3 α = SemidirectProduct.inl (gammaOf hodd h3 α).left :=
    SemidirectProduct.ext rfl (by simpa using hσ)
  have hlo : orderOf (gammaOf hodd h3 α).left = orderOf (gammaOf hodd h3 α) := by
    conv_rhs => rw [hγ]
    exact (orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective _).symm
  have hleft : (gammaOf hodd h3 α).left ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    t2H_pgl_odd_mem hodd _ (by rw [hlo]; exact Odd.of_dvd_nat hα hγo)
  exact (mem_inn_iff hodd h3 α).2 ⟨hσ, hleft⟩

theorem t2H_oddAut_sl9 {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Sylow 2 Q)
    (ρ : MulAut Q) (hρ : Odd (orderOf ρ)) (hfix : ∀ p ∈ (P : Subgroup Q), ρ p = p) :
    ρ = 1 := by
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hαo : orderOf (MulAut.congr e ρ) = orderOf ρ := MulEquiv.orderOf_eq (MulAut.congr e) ρ
  obtain ⟨s, hs⟩ := t2H_inner_of_odd_sl9 hF (MulAut.congr e ρ) (by rw [hαo]; exact hρ)
  have hcomm : ∀ p ∈ (P : Subgroup Q), s * e p = e p * s := by
    intro p hp
    have h1 : MulAut.congr e ρ (e p) = e p := by
      show e (ρ (e.symm (e p))) = e p
      rw [MulEquiv.symm_apply_apply, hfix p hp]
    rw [← hs, MulAut.conj_apply] at h1
    calc s * e p = (s * e p * s⁻¹) * s := by group
      _ = e p * s := by rw [h1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 ↥((P : Subgroup Q).map e.toMonoidHom) := P.isPGroup'.map e.toMonoidHom
  have hidx : ¬ 2 ∣ ((P : Subgroup Q).map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact P.not_dvd_index
  have key := t2C_cent_sylow_sl2 hodd _ hP' hidx s (by
    rintro _ ⟨p, hp, rfl⟩
    exact hcomm p hp)
  have hscen : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (t2C_center_sl2 s).2 key
  have hs1 : (MulAut.conj s : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 := by
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hscen g]
    group
  exact (MulAut.congr e).injective (by rw [← hs, hs1, map_one])

end CFSG.GH74.GLS.Stage4.Rest
