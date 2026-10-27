module

public import CFSG.LargeExtraspecial.AS35CS63Aut
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

theorem card_le_of_isPGroup_of_not_dvd {G : Type*} [Group G] [Finite G] {p k : ℕ}
    [hp : Fact p.Prime] (hG : ¬ p ^ (k + 1) ∣ Nat.card G) (H : Subgroup G)
    (hH : IsPGroup p H) : Nat.card H ≤ p ^ k := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn]
  refine Nat.pow_le_pow_right hp.out.pos ?_
  by_contra hlt
  exact hG ((pow_dvd_pow p (Nat.succ_le_of_lt (not_le.mp hlt))).trans
    (hn ▸ card_subgroup_dvd_card H))

theorem exists_mem_orderOf_eq_of_card_ge {G : Type*} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hbound : ∀ K : Subgroup G, IsPGroup p K → Nat.card K ≤ m)
    (H : Subgroup G) (hH : IsPGroup p H) (hm : m ≤ Nat.card H) (g : G)
    (hg : IsPGroup p (zpowers g)) : ∃ h ∈ H, orderOf h = orderOf g := by
  obtain ⟨P', hP'⟩ := hH.exists_le_sylow
  have hHP : H = P' := eq_of_le_of_card_ge hP' ((hbound _ P'.isPGroup').trans hm)
  obtain ⟨P, hP⟩ := hg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P P'
  refine ⟨MulAut.conj c g, ?_, MulEquiv.orderOf_eq _ g⟩
  rw [hHP, ← hc, Sylow.coe_subgroup_smul]
  exact smul_mem_pointwise_smul g (MulAut.conj c) (P : Subgroup G) (hP (mem_zpowers g))

theorem autL32Input : AutL32Input := by
  intro Y _ hY H hH
  obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hY
  have hcard : Nat.card (MulAut Y) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
  have : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine card_le_of_isPGroup_of_not_dvd ?_ H hH
  rw [hcard]
  decide

theorem orderOf_tMul : orderOf QuasithinUnique.A6Models.tMul = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := QuasithinUnique.A6Models.tMul)
    (by decide +kernel) (by decide +kernel)
  simpa using h

theorem autA6Input : AutA6Input := by
  intro Y _ hY H hH h32
  obtain ⟨e⟩ := hY
  have hcard : Nat.card (MulAut Y) = 1440 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
  have : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set g : MulAut Y := (MulAut.congr e).symm
    (QuasithinUnique.Setup.X3Aut.thetaEquiv ⟨_, QuasithinUnique.DoubleA3.tMul_mem⟩) with hgdef
  have hg : orderOf g = 8 := by
    rw [hgdef, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, orderOf_mk, orderOf_tMul]
  have hbound : ∀ K : Subgroup (MulAut Y), IsPGroup 2 K → Nat.card K ≤ 2 ^ 5 := by
    intro K hK
    refine card_le_of_isPGroup_of_not_dvd ?_ K hK
    rw [hcard]
    decide
  have hgp : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨h, hh, hord⟩ := exists_mem_orderOf_eq_of_card_ge hbound H hH h32 g hgp
  exact ⟨h, hh, hord.trans hg⟩

end S63

end CFSG.LargeExtraspecial
