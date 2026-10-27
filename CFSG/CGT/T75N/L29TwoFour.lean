module

public import CFSG.CGT.T75N.L29TwoGroup

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups
open CFSG.LieType.Steinberg.CentralExt

theorem factorization_sixty : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem card_sl_two_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (SpecialLinearGroup (Fin 2) F) = 60 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field 2, hq]
  norm_num [Fin.prod_univ_two]

theorem ker_eq_bot_two_four
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (π : Y →* SpecialLinearGroup (Fin 2) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y) (E : Subgroup Y) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hEK : E ⊓ π.ker = ⊥) (hE4 : 4 ≤ Nat.card E) : π.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin 2) F) := Finite.of_surjective _ hπ
  have hpK : IsPGroup 2 π.ker := isPGroup_two_ker (by norm_num) π hπ hcen
  let f : E →* SpecialLinearGroup (Fin 2) F := π.comp E.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : Y) ∈ π.ker := hx
    have hx' : (x : Y) ∈ E ⊓ π.ker := ⟨x.2, hxK⟩
    rw [hEK] at hx'
    exact Subtype.ext (Subgroup.mem_bot.1 hx')
  let e : E ≃* f.range := MonoidHom.ofInjective hf
  have hcardE : Nat.card f.range = Nat.card E := (Nat.card_congr e.toEquiv).symm
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x x.2)⟩
  obtain ⟨j, hj⟩ := hEp.exists_card_eq
  have hdvd : Nat.card E ∣ 60 := by
    rw [← card_sl_two_four hF, ← hcardE]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hj2 : j = 2 := by
    by_contra hne
    rcases Nat.lt_or_ge j 2 with hlt | hge
    · have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have h3 : 3 ≤ j := by omega
      have : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 h3
      rw [← hj] at this
      have := this.trans hdvd
      omega
  have hEcard : Nat.card E = 4 := by rw [hj, hj2]; norm_num
  let P : Sylow 2 (SpecialLinearGroup (Fin 2) F) := Sylow.ofCard f.range (by
    rw [hcardE, hEcard, card_sl_two_four hF, factorization_sixty]
    norm_num)
  let s : P.toSubgroup →* Y := E.subtype.comp e.symm.toMonoidHom
  have hs : ∀ x : P.toSubgroup, π (s x) = (x : SpecialLinearGroup (Fin 2) F) := by
    intro x
    have h1 : f (e.symm x) = (x : SpecialLinearGroup (Fin 2) F) := by
      have := congrArg (fun y : f.range => (y : SpecialLinearGroup (Fin 2) F))
        (e.apply_symm_apply x)
      exact this
    exact h1
  obtain ⟨s₀, hs₀⟩ := CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_sylow 2
    Nat.prime_two π hπ hcen hpK P s hs
  exact SL2Closed.ker_eq_bot_of_section π hcen s₀ hs₀

end CFSG.CGT.T75N
