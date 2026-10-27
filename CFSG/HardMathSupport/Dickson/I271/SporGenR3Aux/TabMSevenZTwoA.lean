module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensus
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenNoComp

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section TwoA

variable {G : Type} [Group G]

theorem isConj_of_card_twoA (hE : MonsterExistenceStatement G) {t v : G} (ht : orderOf t = 2)
    (hv : orderOf v = 2)
    (htc : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * CFSG.Open.monsterBabyOrder)
    (hvc : Nat.card ↥(Subgroup.centralizer ({v} : Set G)) = 2 * CFSG.Open.monsterBabyOrder) :
    IsConj t v := by
  obtain ⟨-, a, z, -, -, -, hcls, -, hBz, -⟩ := id hE
  have key : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(Subgroup.centralizer ({s} : Set G)) = 2 * CFSG.Open.monsterBabyOrder →
        IsConj a s := by
    intro s hs hsc
    rcases hcls s hs with h | h
    · exact h
    · exfalso
      have h2 := (hBz s h).2.2.2.2.1
      rw [hsc] at h2
      norm_num [twoBCentralizerOrder, CFSG.Open.monsterBabyOrder] at h2
  exact (key t ht htc).symm.trans (key v hv hvc)


theorem exists_conj_pow_of_twoA
    (hE : MonsterExistenceStatement G) {t d y : G}
    (ht : orderOf t = 2)
    (htc : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * CFSG.Open.monsterBabyOrder)
    (hd : orderOf d = 7) (htd : t * d = d * t) (hy : orderOf y = 7) (hty : t * y = y * t) :
    ∃ g : G, ∃ m : ℕ, g * y * g⁻¹ = d ^ m := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, -, -, -, hcls, hA, hBz, -⟩ := id hE
  haveI : Finite G := hfin
  have htA : IsConj a t := by
    rcases hcls t ht with h | h
    · exact h
    · exfalso
      have h2 := (hBz t h).2.2.2.2.1
      rw [htc] at h2
      norm_num [twoBCentralizerOrder, CFSG.Open.monsterBabyOrder] at h2
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA t htA
  set X : Subgroup G := Subgroup.centralizer ({t} : Set G) with hX
  have hZcard : Nat.card ↥(Subgroup.center ↥X) = 2 := by
    have h1 : Nat.card ↥((Subgroup.center ↥X).map X.subtype) = Nat.card ↥(Subgroup.center ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [hZ, Nat.card_zpowers, ht] at h1
    exact h1.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e.toEquiv
  have hbar : ∀ k : ↥X, orderOf k = 7 → orderOf (e (QuotientGroup.mk k)) = 7 := by
    intro k hk
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← QuotientGroup.mk_pow, ← hk, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · have hmem : k ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff k).1 h1
      have h2 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hk, hZcard] at h2
      norm_num at h2
  set y' : ↥X := ⟨y, Subgroup.mem_centralizer_singleton_iff.2 hty.symm⟩
  set d' : ↥X := ⟨d, Subgroup.mem_centralizer_singleton_iff.2 htd.symm⟩
  have hy' : orderOf y' = 7 := by rw [← Subgroup.orderOf_coe]; exact hy
  have hd' : orderOf d' = 7 := by rw [← Subgroup.orderOf_coe]; exact hd
  obtain ⟨b, hb⟩ := isConj_iff.1 (bSeven_isConj (hbar y' hy') (hbar d' hd'))
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (e.symm b)
  have hck : (QuotientGroup.mk (c * y' * c⁻¹) : ↥X ⧸ Subgroup.center ↥X) =
      (QuotientGroup.mk d' : ↥X ⧸ Subgroup.center ↥X) ^ 1 := by
    rw [pow_one]
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hc, MulEquiv.apply_symm_apply]
    exact hb
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) 7 := by rw [hZcard]; norm_num
  obtain ⟨g, m, hg⟩ := tabMSeven_isConj_zpowers_of_quot (by norm_num) hcop hy' hd' hck
  refine ⟨(g : G), m, ?_⟩
  have h := congrArg Subtype.val hg
  simpa using h

end TwoA

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
