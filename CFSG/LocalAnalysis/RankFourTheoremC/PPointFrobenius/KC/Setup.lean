module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.AGLEmbedding

structure KCData (K : Type) [Group K] [Finite K] (p n : ℕ) (S : Sylow p K) (L : Subgroup K) :
    Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  n3 : 3 ≤ n
  card_S : Nat.card (S : Subgroup K) = p ^ n
  elem_S : IsElemAbelian p (S : Subgroup K)
  noncyc_S : ¬ IsCyclic (S : Subgroup K)
  dvd : p ^ n ∣ Nat.card K
  not_dvd : ¬ p ^ (n + 1) ∣ Nat.card K
  card_L : Nat.card L = p ^ n * (((p ^ n) ^ 2 - 1) / 2)
  card_L_dvd : Nat.card L ∣ Nat.card K

private theorem kcSetup_isElemAbelian_of_mulEquiv {p : ℕ} {G G' : Type} [Group G] [Group G']
    {E : Subgroup G} {F : Subgroup G'} (φ : E ≃* F) (hF : IsElemAbelian p F) :
    IsElemAbelian p E := by
  refine ⟨φ.symm.surjective.isMulCommutative hF.1, fun x hx => ?_⟩
  have h1 : ((φ ⟨x, hx⟩ : F) : G') ^ p = 1 := hF.2 _ (φ ⟨x, hx⟩).2
  have h2 : (⟨x, hx⟩ : E) ^ p = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h1)
  have h3 := congrArg Subtype.val h2
  simpa using h3

theorem kcData_of_sylow_le {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 3 ≤ n) (S : Sylow p K) (L : Subgroup K) (hSL : (S : Subgroup K) ≤ L)
    (e : L ≃* PSL2GF p n) : KCData K p n S L := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hPSL : Nat.card (PSL2GF p n) = p ^ n * (((p ^ n) ^ 2 - 1) / 2) :=
    CFSG.SectionRank.OddCover.card_psl_two hp hp2 (GaloisField.card p n hn0)
  have hLcard : Nat.card L = p ^ n * (((p ^ n) ^ 2 - 1) / 2) :=
    (Nat.card_congr e.toEquiv).trans hPSL
  have hLK : Nat.card L ∣ Nat.card K := Subgroup.card_subgroup_dvd_card L
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hsq_odd : Odd ((p ^ n) ^ 2) := (hodd.pow).pow
  have h2dvd : 2 ∣ (p ^ n) ^ 2 - 1 := (Nat.Odd.sub_odd hsq_odd odd_one).two_dvd
  have hpn1 : ¬ p ∣ (p ^ n) ^ 2 - 1 := by
    intro h
    have h1 : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p hn0) two_ne_zero
    have h3 : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos n)
    have h4 := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self h3] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
  have hpm : ¬ p ∣ ((p ^ n) ^ 2 - 1) / 2 := fun h =>
    hpn1 (dvd_trans h (Nat.div_dvd_of_dvd h2dvd))
  have hcop : Nat.Coprime p (((p ^ n) ^ 2 - 1) / 2) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hS_card_eq : Nat.card (S : Subgroup K) = p ^ (Nat.card K).factorization p :=
    Sylow.card_eq_multiplicity S
  have hpnK : p ^ n ∣ Nat.card K :=
    dvd_trans (by rw [hLcard]; exact dvd_mul_right _ _) hLK
  have hnv : n ≤ (Nat.card K).factorization p :=
    (hp.pow_dvd_iff_le_factorization hK0).1 hpnK
  have hSL_dvd : Nat.card (S : Subgroup K) ∣ Nat.card L := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hS_card_eq, hLcard] at hSL_dvd
  have hvn : (Nat.card K).factorization p ≤ n :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
      (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ hcop) hSL_dvd)
  have hv : (Nat.card K).factorization p = n := le_antisymm hvn hnv
  have hS_card : Nat.card (S : Subgroup K) = p ^ n := by rw [hS_card_eq, hv]
  have hnot : ¬ p ^ (n + 1) ∣ Nat.card K := by
    have h := Nat.pow_succ_factorization_not_dvd hK0 hp
    rwa [hv] at h
  have hSLcard : Nat.card (S.subgroupOf L) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hS_card]
  have hHcard : Nat.card ((S.subgroupOf L).map e.toMonoidHom) = p ^ n := by
    rw [← hSLcard]
    exact (Nat.card_congr
      ((S.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hHp : IsPGroup p ((S.subgroupOf L).map e.toMonoidHom) := IsPGroup.of_card hHcard
  have hHidx : ¬ p ∣ ((S.subgroupOf L).map e.toMonoidHom).index := by
    have h := ((S.subgroupOf L).map e.toMonoidHom).index_mul_card
    rw [hHcard, hPSL] at h
    have h' : ((S.subgroupOf L).map e.toMonoidHom).index * p ^ n =
        ((p ^ n) ^ 2 - 1) / 2 * p ^ n := by
      rw [h, mul_comm]
    have hidx : ((S.subgroupOf L).map e.toMonoidHom).index = ((p ^ n) ^ 2 - 1) / 2 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) h'
    rw [hidx]
    exact hpm
  have hTel : IsElemAbelian p ((S.subgroupOf L).map e.toMonoidHom) :=
    (psl2GF_sylow p n hn1 (hHp.toSylow hHidx)).1
  have hSE : IsElemAbelian p (S : Subgroup K) :=
    kcSetup_isElemAbelian_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hSL).symm.trans
        ((S.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)) hTel
  have hnoncyc : ¬ IsCyclic (S : Subgroup K) := by
    intro hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (S : Subgroup K))
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      simpa using hSE.2 (g : K) g.2
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [hg, hS_card] at hdvd
    have hle : p ^ n ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hp2' : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    nlinarith
  exact
    { prime := hp
      p5 := hp5
      n3 := hn
      card_S := hS_card
      elem_S := hSE
      noncyc_S := hnoncyc
      dvd := hpnK
      not_dvd := hnot
      card_L := hLcard
      card_L_dvd := hLK }

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
