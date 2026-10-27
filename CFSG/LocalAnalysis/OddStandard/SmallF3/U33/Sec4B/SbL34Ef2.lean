module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ee

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {Λ : Type} [Group Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] {ι : Λ →* (E ≃ₗ[ZMod 2] E)} {P W : Subgroup Λ} {r s : Λ}

theorem card_P_eq_four (h : Crit ι P W r s) : Nat.card P = 4 := by
  haveI : P.Normal := h.normal
  obtain ⟨Z, hZP, hZn, hZcard, hZodd⟩ := exists_normal_four h
  haveI : Z.Normal := hZn
  have hZ2 : IsPGroup 2 Z :=
    IsPGroup.of_card (n := 2) (by rw [hZcard]; norm_num)
  have hZrel : Z.relIndex P = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := by
      intro hp_eq
      exact hZodd (hp_eq ▸ hpdvd)
    haveI : Fact p.Prime := ⟨hp⟩
    have hnil : Group.IsNilpotent ↥P := isNilpotent_of_fpf P r h.r_cube h.fpf
    obtain ⟨R, hRP, hRn, hRp, hRidx⟩ := exists_normal_sylow P hnil p
    haveI : R.Normal := hRn
    have h2dvdZ : 2 ∣ Nat.card ↥Z := by rw [hZcard]; norm_num
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2 h2dvdZ
    have hz2 : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rw [hz] at h
      simpa [pow_two] using h
    have ha2 : (z : Λ) * (z : Λ) = 1 := by
      have h := congrArg (fun y : ↥Z => (y : Λ)) hz2
      simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h
    have ha1 : (z : Λ) ≠ 1 := by
      intro hz1
      have hzeq : z = 1 := Subtype.ext (by simpa using hz1)
      rw [hzeq] at hz
      simp only [orderOf_one] at hz
      omega
    have hdis : Disjoint Z R := IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) Z R hZ2 hRp
    have hcomm : ∀ x ∈ R, (z : Λ) * x = x * (z : Λ) := by
      intro x hx
      exact (Subgroup.commute_of_normal_of_disjoint Z R hZn hRn hdis (z : Λ) x z.2 hx).eq
    have hRbot : R = ⊥ := eq_bot_of_odd_normal_pgroup hp2 h R hRP hRp ha2 ha1 hcomm
    have hpP : p ∣ Nat.card P :=
      hpdvd.trans (Subgroup.relIndex_dvd_card (H := Z) (K := P))
    have hnot : ¬ p ∣ Nat.card P := by
      rw [hRbot, Subgroup.relIndex_bot_left] at hRidx
      exact hRidx
    exact hnot hpP
  calc Nat.card P = Z.relIndex P * Nat.card ↥(Z ⊓ P) :=
        (Subgroup.relIndex_mul_card (H := Z) (K := P)).symm
    _ = Z.relIndex P * Nat.card Z := by rw [inf_eq_left.mpr hZP]
    _ = 1 * 4 := by rw [hZrel, hZcard]
    _ = 4 := by norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
