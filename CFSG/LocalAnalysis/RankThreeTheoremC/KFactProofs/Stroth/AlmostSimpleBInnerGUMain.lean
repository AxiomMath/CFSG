module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGUThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGLMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {E : Type} [Field E] {hE : UnitaryFieldData ℓ f E}
  {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

theorem oddPCoreInClosure_sesqUnitaryGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ = 2)
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) :
    OddPCoreInClosure p ↥(sesqUnitaryGroup Hf) := by
  haveI : Finite ↥(sesqUnitaryGroup Hf) := finite_sesqUnitaryGroup'
  haveI : CharP E 2 := hℓ ▸ hE.charP
  have hf1 := hE.one_le
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by omega : f ≠ 0) hE.prime.one_lt
    omega
  by_cases hm : 2 ≤ Module.finrank E W
  · by_cases hexc2 : Module.finrank E W = 2 ∧ ℓ ^ f = 2
    ·
      have h18 := natCard_sesqUnitaryGroup_two_two hHf hHfl hexc2.2 hexc2.1
      by_cases hp18 : p ∣ 2 * 3 ^ 2
      · have hp3 : p = 3 := by
          rcases (Nat.Prime.dvd_mul hp).1 hp18 with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
          · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
        subst hp3
        refine OddPCoreInClosure.of_odd_core fun K hK hKcop => ?_
        have hKdvd : Nat.card K ∣ 2 * 3 ^ 2 := by
          have := h18 ▸ Subgroup.card_subgroup_dvd_card K
          simpa using this
        have hKd2 : Nat.card K ∣ 2 :=
          (Nat.Coprime.pow_right 2 hKcop.symm).dvd_of_dvd_mul_right hKdvd
        rcases (Nat.dvd_prime Nat.prime_two).1 hKd2 with h1 | h2
        · rw [h1]
          exact odd_one
        · exfalso
          have hcen := le_center_of_normal_of_natCard_eq_two K h2
          have hbot : K = ⊥ := by
            rw [Subgroup.eq_bot_iff_forall]
            intro x hx
            have hx2 : x ^ 2 = 1 := by
              have := pow_card_eq_one' (G := ↥K) (x := (⟨x, hx⟩ : ↥K))
              rw [h2] at this
              simpa using congrArg Subtype.val this
            have hx2' : ((x : LinearMap.GeneralLinearGroup E W)) ^ 2 = 1 := by
              simpa using congrArg Subtype.val hx2
            refine Subtype.ext (eq_one_of_commute_special_unitary_of_sq_eq_one hℓ hHf hHfl hm
              (x : LinearMap.GeneralLinearGroup E W) hx2' fun δ hδ => ?_)
            have := Subgroup.mem_center_iff.1 (hcen hx) ⟨δ, sesqSpecialUnitaryGroup_le Hf hδ⟩
            exact congrArg Subtype.val this
          rw [hbot, Subgroup.card_bot] at h2
          omega
      · exact OddPCoreInClosure.of_not_dvd hp (by rw [h18]; simpa using hp18)
    · by_cases hexc3 : Module.finrank E W = 3 ∧ ℓ ^ f = 2
      ·
        have h648 := natCard_sesqUnitaryGroup_three_two hHf hHfl hexc3.2 hexc3.1
        by_cases hp648 : p ∣ 2 ^ 3 * 3 ^ 4
        · have hp3 : p = 3 := by
            rcases (Nat.Prime.dvd_mul hp).1 hp648 with h | h
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
                (hp.dvd_of_dvd_pow h)) hp2
            · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
          subst hp3
          refine OddPCoreInClosure.of_odd_core fun K hK hKcop => ?_
          haveI := hK
          have hKdvd : Nat.card K ∣ 2 ^ 3 * 3 ^ 4 := by
            have := h648 ▸ Subgroup.card_subgroup_dvd_card K
            simpa using this
          have hKd : Nat.card K ∣ 2 ^ 3 :=
            (Nat.Coprime.pow_right 4 hKcop.symm).dvd_of_dvd_mul_right hKdvd
          obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKd
          have hKp : IsPGroup 2 ↥K := IsPGroup.of_card hk
          have hbot := eq_bot_of_normal_isPGroup_two_sesqUnitaryGroup_three_two hℓ hHf hHfl
            hexc3.2 hexc3.1 K hKp
          rw [hbot, Subgroup.card_bot]
          exact odd_one
        · exact OddPCoreInClosure.of_not_dvd hp (by rw [h648]; simpa using hp648)
      ·
        set Q := (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) with hQ
        haveI : Q.Normal := normal_special_subgroupOf hHf hHfl (by omega)
        have hq : (Module.finrank E W = 2 → 4 ≤ ℓ ^ f) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ f) := by
          refine ⟨fun h2 => ?_, fun h3 => ?_⟩
          · have hne : ℓ ^ f ≠ 2 := fun h => hexc2 ⟨h2, h⟩
            have hf2 : 2 ≤ f := by
              by_contra hlt
              have h1 : f = 1 := by omega
              exact hne (by rw [h1, hℓ]; norm_num)
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
              _ = ℓ ^ f := by rw [hℓ]
          · have hne : ℓ ^ f ≠ 2 := fun h => hexc3 ⟨h3, h⟩
            omega
        have hQs : CFSG.IsQuasisimple ↥Q := isQuasisimple_special_subgroupOf hHf hHfl hm hq
        refine oddPCoreInClosure_of_quasisimple_normal hp Q hQs ?_ ?_
        ·
          refine odd_natCard_of_forall_sq fun x hx2 => ?_
          have hxc : ∀ δ ∈ Q, δ * (x : ↥(sesqUnitaryGroup Hf)) = x * δ :=
            Subgroup.mem_centralizer_iff.1 x.2
          have hy2 : ((x : ↥(sesqUnitaryGroup Hf))) ^ 2 = 1 := by
            simpa using congrArg Subtype.val hx2
          have hy2' :
              (((x : ↥(sesqUnitaryGroup Hf)) : LinearMap.GeneralLinearGroup E W)) ^ 2 = 1 := by
            simpa using congrArg Subtype.val hy2
          have := eq_one_of_commute_special_unitary_of_sq_eq_one hℓ hHf hHfl hm
            (((x : ↥(sesqUnitaryGroup Hf))) : LinearMap.GeneralLinearGroup E W) hy2' fun δ hδ => by
              have hmem : (⟨δ, sesqSpecialUnitaryGroup_le Hf hδ⟩ : ↥(sesqUnitaryGroup Hf)) ∈ Q :=
                Subgroup.mem_subgroupOf.2 hδ
              exact congrArg Subtype.val (hxc _ hmem)
          exact Subtype.ext (Subtype.ext this)
        ·
          intro hpG
          have h1 := dvd_card_special_of_dvd_card hHf hHfl hm hp hpG
          rw [show Nat.card Q = Nat.card (sesqSpecialUnitaryGroup Hf) from
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).toEquiv]
          exact h1
  ·
    refine OddPCoreInClosure.of_odd_core fun K _ _ => odd_natCard_of_forall_sq fun x hx2 => ?_
    have hy2 : ((x : ↥(sesqUnitaryGroup Hf))) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hx2
    have hy2' : (((x : ↥(sesqUnitaryGroup Hf)) : LinearMap.GeneralLinearGroup E W)) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hy2
    have := eq_one_of_sq_eq_one_of_finrank_le_one (by omega : Module.finrank E W ≤ 1)
      (((x : ↥(sesqUnitaryGroup Hf))) : LinearMap.GeneralLinearGroup E W) hy2'
    exact Subtype.ext (Subtype.ext this)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
