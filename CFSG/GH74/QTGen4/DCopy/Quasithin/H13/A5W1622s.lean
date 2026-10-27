module

public import CFSG.Quasithin.H13.A5W1622s
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622r

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem msPair_data_of_plus_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : IsPSL 3 2 1 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) ∨
      IsAlt 6 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) ∨
      IsPSU 3 3 1 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K))) :
    IsRankTwoLie2Derived
        ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∧
      ¬ 64 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hqP := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  have hnt : Nontrivial ↥(S.plus K) := by
    obtain ⟨a, b, hab⟩ := hqP.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hker := ker_le_center_of_isQuasisimple hq π hπ hnt
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  let e := centerQuotEquiv π hπ hker
  refine ⟨SBc11.isRankTwoLie2Derived_of_list (isList_of_mulEquiv e.symm hlist), ?_⟩

  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hX
  have hZodd : ¬ 2 ∣ Nat.card (Subgroup.center X) := by
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2 h2
    have hzO : (z : X) ∈ CFSG.pCore 2 X := by
      have hle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := by
        refine le_sSup (show Subgroup.zpowers (z : X) ∈
          {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from ⟨⟨fun n hn g => ?_⟩, ?_⟩)
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
          rw [Subgroup.mem_center_iff.mp (zpow_mem z.2 k) g, mul_inv_cancel_right]
          exact Subgroup.zpow_mem_zpowers _ _
        · refine IsPGroup.of_card (n := 1) ?_
          rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe, hz]
      exact hle (Subgroup.mem_zpowers _)
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hzO
    have : orderOf z = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hzO
    rw [hz] at this
    norm_num at this

  have hcard : Nat.card X = Nat.card (Subgroup.center X) *
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) := by
    rw [← Nat.card_congr e.toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  intro h64
  rw [hcard] at h64
  have hcop : Nat.Coprime 64 (Nat.card (Subgroup.center X)) := by
    have : Nat.Coprime 2 (Nat.card (Subgroup.center X)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hZodd
    exact Nat.Coprime.pow_left 6 this
  have h64' := hcop.dvd_of_dvd_mul_left h64
  rcases SBc11.card_of_list hlist with h | h | h <;> rw [h] at h64' <;> norm_num at h64'

end Setting

end CFSG.Quasithin.H13.A5
