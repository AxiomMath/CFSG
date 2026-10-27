module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_no_order13 {V : Type} [Group V] [Finite V] (hV : Nat.card V = 2 ^ 8)
    (g : MulAut V) (hg : g ^ 13 = 1) : g = 1 := by
  by_contra hg1
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hdvd : orderOf g ∣ 13 := orderOf_dvd_of_pow_eq_one hg
  have horder : orderOf g = 13 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 13) (orderOf g) hdvd with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  let H : Subgroup (MulAut V) := Subgroup.zpowers g
  have hHcard : Nat.card H = 13 := by rw [Nat.card_zpowers, horder]
  have hHp : IsPGroup 13 H := IsPGroup.of_card (n := 1) (by rw [hHcard]; norm_num)
  let F : Subgroup V := FixedPoints.subgroup H V
  have hFc : Nat.card F = Nat.card (MulAction.fixedPoints H V) := rfl
  have hmod : Nat.card V ≡ Nat.card (MulAction.fixedPoints H V) [MOD 13] :=
    hHp.card_modEq_card_fixedPoints V
  have hdvdF : Nat.card F ∣ Nat.card V := F.card_subgroup_dvd_card
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hV ▸ hdvdF)
  have hmod' : 2 ^ 8 ≡ 2 ^ k [MOD 13] :=
    calc 2 ^ 8 = Nat.card V := hV.symm
      _ ≡ Nat.card (MulAction.fixedPoints H V) [MOD 13] := hmod
      _ = Nat.card F := hFc.symm
      _ = 2 ^ k := hk_eq
  have hk8 : k = 8 := by
    interval_cases k <;> first | rfl | exact absurd hmod' (by decide)
  have hcardFV : Nat.card F = Nat.card V := by rw [hk_eq, hk8, hV]
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F hcardFV
  refine hg1 ?_
  apply MulEquiv.ext
  intro v
  change g v = v
  have hv : v ∈ F := by rw [hFtop]; exact Subgroup.mem_top v
  have hfix : (⟨g, Subgroup.mem_zpowers g⟩ : H) • v = v :=
    (FixedPoints.mem_subgroup (M := H) (α := V) v).mp hv ⟨g, Subgroup.mem_zpowers g⟩
  rwa [Subgroup.smul_def, MulAut.smul_def] at hfix

end CFSG.OddStandard.SmallF3.Omega
