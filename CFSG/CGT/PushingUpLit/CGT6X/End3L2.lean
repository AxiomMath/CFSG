module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Count

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

section M3

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_eq_of_top_section {S M : Type} [Group S] [Group M] {act : S → M → M}
    {X : Subgroup (MulAut V)} (hsec : IsNatSectionBy act X ⊤ ⊥) : Nat.card V = Nat.card M := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hsec
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk, Subgroup.bot_subgroupOf, Subgroup.card_bot, Subgroup.card_top] at h1
  omega

theorem m3_cases (hM3 : L2SmallModules) (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    {f : ℕ} (hf : 2 ≤ f) (eSL : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)))
    (hLirr : ∀ A : Subgroup V, GInv L A → A = ⊥ ∨ A = ⊤)
    (hVle : Nat.card V ≤ 2 ^ (2 * (2 * f))) {c : MulAut V} (hcL : c ∈ L)
    (hodd : Odd (orderOf c)) (hgt : 1 < orderOf c) (hup : Nat.card ↥(commSub c) ≤ 2 ^ (2 * f)) :
    Nat.card V = 2 ^ (4 * f) ∧ IsNatSectionBy (omegaMinusAct f) L ⊤ ⊥ := by
  rcases hM3 (2 * f) (by omega) V hV L ⟨eSL⟩ hLirr hVle with htriv | hnat | ⟨k, hk, hΩ⟩
  · exfalso
    have hc1 : c = 1 := by
      ext v
      simpa using htriv c hcL v
    rw [hc1, orderOf_one] at hgt
    omega
  · exfalso
    have h1 := card_commSub_inf_ge_of_sl (f := 2 * f) (by omega) hnat hcL hodd hgt
    rw [inf_top_eq] at h1
    have h2 : 2 ^ (2 * f) < 2 ^ (2 * (2 * f)) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · have hkf : k = f := by omega
    subst hkf
    refine ⟨?_, hΩ⟩
    rw [card_eq_of_top_section hΩ, card_multiplicative_hermSub (by omega)]

end M3

end CFSG.CGT.PushingUpLit.CGT6X.End3
