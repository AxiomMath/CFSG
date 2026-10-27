module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Defs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotEndFieldEvenAut

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

theorem kgg_conj_range_normal (H : Type) [Group H] :
    ((MulAut.conj : H →* MulAut H).range).Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ α
  exact ⟨α y, MulEquiv.ext fun z => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩

theorem kgg_mem_of_quotient_coprime (G : Type) [Group G] (N : Subgroup G) [N.Normal] {x c d : G}
    {m k : ℕ} (hcop : Nat.Coprime (2 ^ m) k) (hx : x ^ (2 ^ m) = 1) (hd : d ^ k = 1)
    (hc : c ∈ N) (hxcd : x = c * d) : x ∈ N := by
  have hqc : QuotientGroup.mk' N c = 1 := (QuotientGroup.eq_one_iff (N := N) c).2 hc
  have hqx : QuotientGroup.mk' N x = QuotientGroup.mk' N d := by
    rw [hxcd, map_mul, hqc, one_mul]
  have hxo : QuotientGroup.mk' N x ^ (2 ^ m) = 1 := by
    rw [← map_pow (QuotientGroup.mk' N) x, hx, map_one]
  have hdo : QuotientGroup.mk' N d ^ k = 1 := by
    rw [← map_pow (QuotientGroup.mk' N) d, hd, map_one]
  have ho1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hxo
  have ho2 : orderOf (QuotientGroup.mk' N x) ∣ k := by
    rw [hqx]
    exact orderOf_dvd_of_pow_eq_one hdo
  have hcop' : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) k :=
    Nat.Coprime.coprime_dvd_left ho1 hcop
  have ho : orderOf (QuotientGroup.mk' N x) = 1 := Nat.Coprime.eq_one_of_dvd hcop' ho2
  exact (QuotientGroup.eq_one_iff (N := N) x).1 (orderOf_eq_one_iff.1 ho)


theorem e6_inner_of_ker {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (Θ : MulAut (C6 F) →* (F ≃+* F) × Multiplicative (ZMod 2))
    (hΘ : ∀ (g : C6 F) (a : Fin Tag.E6.rank → Fˣ) (ρ : F ≃+* F) (ε : ℕ),
      Θ (MulAut.conj g * exactNormalAut .E6 F a ρ ε) = (ρ, Multiplicative.ofAdd (ε : ZMod 2)))
    {x : MulAut (C6 F)} (hx : Θ x = 1) {m : ℕ} (hxm : x ^ (2 ^ m) = 1) :
    x ∈ (MulAut.conj : C6 F →* MulAut (C6 F)).range := by
  obtain ⟨g, a, ρ, ε, hxeq⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (Or.inl rfl) x
  have hΘx : Θ x = (ρ, Multiplicative.ofAdd ((ε : ℕ) : ZMod 2)) := by
    rw [hxeq]
    exact hΘ g a ρ (ε : ℕ)
  have hΘ1 : (ρ, Multiplicative.ofAdd ((ε : ℕ) : ZMod 2)) = 1 := hΘx.symm.trans hx
  have hρ : ρ = 1 := congrArg Prod.fst hΘ1
  have hε : ((ε : ℕ) : ZMod 2) = 0 := congrArg (fun y => Multiplicative.toAdd y.2) hΘ1
  have hε2 : (ε : ℕ) % 2 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).1 hε
    omega
  have hmod := exactNormalAut_mod_two_E6 a 1 (ε : ℕ)
  rw [hε2] at hmod
  have hxd : x = MulAut.conj g * diagAutHomE6 F a := by
    rw [hxeq, hρ]
    exact congrArg (fun y => MulAut.conj g * y) hmod.symm
  have hodd : Odd (Nat.card (Fin Tag.E6.rank → Fˣ)) := by
    rw [Nat.card_fun, Nat.card_units, hF]
    refine Odd.pow ?_
    have hn : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := F)
      rw [hF, pow_zero] at this
      exact lt_irrefl 1 this
    obtain ⟨r, hr⟩ : Even (2 ^ n) := (Nat.even_pow' hn).2 even_two
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact ⟨r - 1, by omega⟩
  have hd : diagAutHomE6 F a ^ Nat.card (Fin Tag.E6.rank → Fˣ) = 1 := by
    rw [← map_pow (diagAutHomE6 F) a, pow_card_eq_one', map_one]
  have hcop2 : Nat.Coprime 2 (Nat.card (Fin Tag.E6.rank → Fˣ)) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
    obtain ⟨r, hr⟩ := hodd
    omega
  have hcop : Nat.Coprime (2 ^ m) (Nat.card (Fin Tag.E6.rank → Fˣ)) :=
    Nat.Coprime.pow_left m hcop2
  haveI : ((MulAut.conj : C6 F →* MulAut (C6 F)).range).Normal :=
    kgg_conj_range_normal (C6 F)
  have hc : MulAut.conj g ∈ (MulAut.conj : C6 F →* MulAut (C6 F)).range := ⟨g, rfl⟩
  exact kgg_mem_of_quotient_coprime (MulAut (C6 F))
    (MulAut.conj : C6 F →* MulAut (C6 F)).range hcop hxm hd hc hxd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
