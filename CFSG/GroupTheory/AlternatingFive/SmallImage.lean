module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory.AlternatingFive

open CFSG.Quasithin

theorem exists_orderOf_eq_three_of_oTwoQuot_mulEquiv {L : Type} [Group L] [Finite L]
    (e : oTwoQuot L ≃* alternatingGroup (Fin 5)) : ∃ x : L, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 : Nat.card (oTwoQuot L) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcard : Nat.card L = Nat.card (oTwoQuot L) * Nat.card (CFSG.pCore 2 L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L)
  have h3dvd : 3 ∣ Nat.card L := by
    rw [hcard, h60]
    exact (show (3 : ℕ) ∣ 60 by norm_num).trans (dvd_mul_right 60 _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨x, hx⟩

theorem map_eq_one_of_orderOf_eq_three_of_card_lt_sixty
    {L H : Type} [Group L] [Finite L] [Group H] [Finite H]
    (e : oTwoQuot L ≃* alternatingGroup (Fin 5))
    (φ : L →* H) (hH : Nat.card H < 60)
    {x : L} (hx : orderOf x = 3) : φ x = 1 := by
  classical
  let P : Subgroup L := CFSG.pCore 2 L
  haveI hPnormal : P.Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup (G := L) (p := 2)
  let N : Subgroup L := φ.ker
  haveI hNnormal : N.Normal := φ.normal_ker
  by_cases hNP : N ≤ P
  ·
    let ψ : L ⧸ N →* L ⧸ P :=
      QuotientGroup.map (N := N) P (MonoidHom.id L) (by simpa using hNP)
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨QuotientGroup.mk z, by simp [ψ]⟩
    have hcard_le : Nat.card (L ⧸ P) ≤ Nat.card (L ⧸ N) :=
      Nat.card_le_card_of_surjective ψ hψ
    have hLP : Nat.card (L ⧸ P) = 60 := by
      have hcarde : Nat.card (L ⧸ P) = Nat.card (alternatingGroup (Fin 5)) :=
        Nat.card_congr e.toEquiv
      rw [hcarde, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hLN : Nat.card (L ⧸ N) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hrangeH : Nat.card φ.range ≤ Nat.card H :=
      Nat.card_le_card_of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
    omega
  ·
    let q : L →* L ⧸ P := QuotientGroup.mk' P
    have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective P
    have hNmap_normal : (N.map q).Normal := hNnormal.map q hqsurj
    have hNmap_ne : N.map q ≠ ⊥ := by
      intro hbot
      apply hNP
      rw [← QuotientGroup.ker_mk' P]
      exact (Subgroup.map_eq_bot_iff (H := N) (f := q)).mp hbot
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup (L ⧸ P) := e.isSimpleGroup
    have hNmap_top : N.map q = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q) with h | h
      · exact absurd h hNmap_ne
      · exact h
    have hPmap : P.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff (H := P) (f := q), QuotientGroup.ker_mk']
    have hmap_top : (N ⊔ P).map q = ⊤ := by
      rw [Subgroup.map_sup, hNmap_top, hPmap, sup_bot_eq]
    have hNPtop : N ⊔ P = ⊤ := by
      have hcomap : ((N ⊔ P).map q).comap q = N ⊔ P :=
        Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact le_sup_right)
      rw [hmap_top] at hcomap
      simpa using hcomap.symm
    have hPquot : IsPGroup 2 (↥P ⧸ N.subgroupOf P) :=
      hPp.to_quotient (N.subgroupOf P)
    have e2 : ↥P ⧸ N.subgroupOf P ≃* L ⧸ N := by
      have h := QuotientGroup.quotientInfEquivProdNormalQuotient P N
      rw [sup_comm P N, hNPtop] at h
      let eTop : (⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
      have hmap : (N.subgroupOf ⊤).map eTop.toMonoidHom = N := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
      exact h.trans (QuotientGroup.congr (N.subgroupOf ⊤) N eTop hmap)
    have hLNp : IsPGroup 2 (L ⧸ N) := hPquot.of_equiv e2
    have hRangeP : IsPGroup 2 φ.range :=
      hLNp.of_equiv (QuotientGroup.quotientKerEquivRange φ)
    obtain ⟨k, hk⟩ := hRangeP ⟨φ x, ⟨x, rfl⟩⟩
    have hk' : (φ x) ^ (2 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hx3 : x ^ 3 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    have hφ3 : (φ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hdvd2 : orderOf (φ x) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk'
    have hdvd3 : orderOf (φ x) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hφ3
    have hcop : Nat.Coprime (2 ^ k) 3 := (by norm_num : Nat.Coprime 2 3).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd3)

end CFSG.GroupTheory.AlternatingFive
