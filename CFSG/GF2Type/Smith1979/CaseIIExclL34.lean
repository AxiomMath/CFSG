module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel

public section

namespace CFSG.GF2Type.Smith1979.Case2

open CFSG.ComponentClassification

theorem orderOf_ne_six_of_psl34 {X : Type} [Group X]
    (hX : CFSG.Open.StatedClassicalModel X .PSL 3 2 2) (x : X) : orderOf x ≠ 6 := by
  intro h6
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated X hX
  have hs6 : orderOf (e x) = 6 := by
    rw [MulEquiv.orderOf_eq]
    exact h6
  set uS : ↥PSL3Four.S := e x ^ 3 with huS
  set wS : ↥PSL3Four.S := e x ^ 2 with hwS
  have hu2 : orderOf uS = 2 := by
    rw [huS, orderOf_pow_of_dvd (by norm_num) (by rw [hs6]; norm_num), hs6]
  have hw3 : orderOf wS = 3 := by
    rw [hwS, orderOf_pow_of_dvd (by norm_num) (by rw [hs6]; norm_num), hs6]
  have hwu : (wS : Equiv.Perm (Fin 42)) * uS = uS * wS := by
    have h : wS * uS = uS * wS := by
      rw [huS, hwS, ← pow_add, ← pow_add, add_comm]
    exact congrArg Subtype.val h
  let uR : ↥PSL3Four.R := ⟨uS, PSL3Four.S_le_R uS.2⟩
  have hu2R : orderOf uR = 2 := by
    rw [← Subgroup.orderOf_coe uR, show (uR : Equiv.Perm (Fin 42)) = uS from rfl,
      Subgroup.orderOf_coe uS, hu2]
  have h1 : IsConj uR PSL3Four.r₁R := by
    rcases (PSL3Four.orderOf_eq_two_iff uR).1 hu2R with h | h | h | h
    · exact h
    · exact absurd uS.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₂)
    · exact absurd uS.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₃)
    · exact absurd uS.2 (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₄)
  obtain ⟨c, hcR, hcu⟩ := PSL3Four.eq_conj_of_isConj h1
  have hr1 : PSL3Four.r₁ = c⁻¹ * (uS : Equiv.Perm (Fin 42)) * c := by
    have h : (uS : Equiv.Perm (Fin 42)) = c * PSL3Four.r₁ * c⁻¹ := hcu
    rw [h]
    group
  have hvS : c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c ∈ PSL3Four.S := by
    have := PSL3Four.conj_mem_S (Subgroup.inv_mem _ hcR) wS.2
    rwa [inv_inv] at this
  have hvr : c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c * PSL3Four.r₁ =
      PSL3Four.r₁ * (c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c) := by
    rw [hr1]
    calc c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c * (c⁻¹ * (uS : Equiv.Perm (Fin 42)) * c)
        = c⁻¹ * ((wS : Equiv.Perm (Fin 42)) * uS) * c := by group
      _ = c⁻¹ * ((uS : Equiv.Perm (Fin 42)) * wS) * c := by rw [hwu]
      _ = c⁻¹ * (uS : Equiv.Perm (Fin 42)) * c * (c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c) := by
        group
  let vC : ↥PSL3Four.C₁ :=
    ⟨c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c,
      ⟨Subgroup.mem_centralizer_singleton_iff.2 hvr, hvS⟩⟩
  have hv3 : orderOf vC = 3 := by
    rw [← Subgroup.orderOf_coe vC]
    have h : (vC : Equiv.Perm (Fin 42)) = (MulAut.conj c⁻¹) (wS : Equiv.Perm (Fin 42)) := by
      change c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c = c⁻¹ * (wS : Equiv.Perm (Fin 42)) * c⁻¹⁻¹
      rw [inv_inv]
    rw [h, MulEquiv.orderOf_eq, Subgroup.orderOf_coe wS, hw3]
  have hdvd : orderOf vC ∣ Nat.card ↥PSL3Four.C₁ := orderOf_dvd_natCard vC
  rw [hv3, PSL3Four.card_C₁] at hdvd
  exact absurd hdvd (by norm_num)

end CFSG.GF2Type.Smith1979.Case2
