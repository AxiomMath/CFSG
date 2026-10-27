module

public import CFSG.CGT.PushingUpLit.EightOneBlocksBasic
public import CFSG.CGT.PushingUpLit.SubnormalTwoGroup

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_prime_top {X L : Subgroup G} (hX : IsShortGroup ↥X) (hL : IsShortGroup ↥L)
    (hXL : X ≤ L) (hXnt : ¬ IsPGroup 2 ↥X) (hp : (Nat.card (↥L ⧸ pCore 2 ↥L)).Prime)
    (hU : (shortU ↥X).map X.subtype ≤ (shortU ↥L).map L.subtype) : X = L := by
  have hpX : Nat.card (↥L ⧸ pCore 2 ↥L) ∣ Nat.card ↥X := by
    by_contra hnd
    refine hXnt ?_
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (pCore_isPGroup (p := 2) (G := ↥L))
    have hLcard : Nat.card ↥L = Nat.card (↥L ⧸ pCore 2 ↥L) * 2 ^ b := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L), hb]
    have hdvd : Nat.card ↥X ∣ Nat.card (↥L ⧸ pCore 2 ↥L) * 2 ^ b :=
      hLcard ▸ Subgroup.card_dvd_of_le hXL
    have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card (↥L ⧸ pCore 2 ↥L)) :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcop.dvd_of_dvd_mul_left hdvd)
    exact IsPGroup.of_card hk
  have : Fact (Nat.card (↥L ⧸ pCore 2 ↥L)).Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) (Nat.card (↥L ⧸ pCore 2 ↥L)) hpX
  have hxo : orderOf (x : G) = Nat.card (↥L ⧸ pCore 2 ↥L) := (Subgroup.orderOf_coe x).trans hx
  have hdata := isPrimeBlockData_of hL hp rfl (hXL x.2) hxo
  have hUX : blockU X ≤ blockU L := by
    rw [← map_shortU_subtype, ← map_shortU_subtype]
    exact hU
  have heq : blockU X = blockU L := by
    rcases hdata.irr (blockU X) hUX
      (fun n hn => conj_mem_blockU (Subgroup.le_normalizer x.2) hn) with h | h
    · exact absurd h (blockU_ne_bot_of_short hX)
    · exact h
  refine le_antisymm hXL fun g hg => ?_
  obtain ⟨r, hr, k, rfl⟩ := hdata.decomp g hg
  have hrX : r ∈ X := blockU_le X (heq ▸ (hdata.oTwoIn_eq ▸ hr))
  exact mul_mem hrX (pow_mem x.2 k)

theorem eq_of_le_normalizer_of_not_le_oTwoIn {L Y : Subgroup G} (hL : IsShortGroup ↥L)
    (hsimple : IsSimpleGroup (↥L ⧸ pCore 2 ↥L)) (hYL : Y ≤ L)
    (hnorm : L ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ Y ≤ oTwoIn L) : Y = L := by
  have hn : (Y.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYL).2 hnorm
  have : ((Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    ((Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) with h | h
  · exfalso
    refine hY fun y hy => ?_
    have h1 : (Y.subgroupOf L) ≤ (QuotientGroup.mk' (pCore 2 ↥L)).ker :=
      (Subgroup.map_eq_bot_iff _).1 h
    rw [QuotientGroup.ker_mk'] at h1
    exact ⟨⟨y, hYL hy⟩, h1 hy, rfl⟩
  · have hdec : ∀ b ∈ L, ∃ y ∈ Y, ∃ q ∈ oTwoIn L, q ∈ L ∧ y * q = b := by
      intro b hb
      have hmem : QuotientGroup.mk' (pCore 2 ↥L) ⟨b, hb⟩ ∈
          (Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) := by
        rw [h]
        trivial
      obtain ⟨y', hy', hyy⟩ := hmem
      have hc : y'⁻¹ * ⟨b, hb⟩ ∈ pCore 2 ↥L := QuotientGroup.eq.1 hyy
      refine ⟨(y' : G), hy', ((y'⁻¹ * ⟨b, hb⟩ : ↥L) : G), ⟨_, hc, rfl⟩, (y'⁻¹ * ⟨b, hb⟩).2, ?_⟩
      simp
    exact SubTwo.noTwoQuotient_of_oResidualTwo hL.residual_eq Y hYL hnorm
      (fun b hb => SubTwo.exists_pow_mem_of_decomp hnorm (isPGroup_oTwoIn L) hdec b hb)

theorem EightOneBlocks.not_le_oTwoIn_of_inClassX {X Y L : Subgroup G} (hX : InClassX ↥X)
    (hXY : X ≤ Y) : ¬ Y ≤ oTwoIn L := fun h =>
  InClassX.not_isPGroup hX ((isPGroup_oTwoIn L).to_le (hXY.trans h))

theorem arrow_top_simple {X L : Subgroup G} (hX : InClassX ↥X) (hL : InClassX ↥L) (hXL : X ≤ L)
    (hne : X ≠ L) (harrow : Arrow X L) :
    IsSimpleGroup (↥L ⧸ pCore 2 ↥L) ∧ ∃ a b : ↥L ⧸ pCore 2 ↥L, a * b ≠ b * a := by
  rcases harrow with rfl | ⟨n, m, -, φ, F, -, hU, -, -⟩
  · exact absurd rfl hne
  rcases hL.1.quotient_type with ⟨hperf, -, a, b, hab⟩ | hp
  · obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hnab : ∃ a b : ↥L ⧸ pCore 2 ↥L, a * b ≠ b * a :=
      ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
    refine ⟨?_, hnab⟩
    by_cases h5 : 5 ≤ m
    · have : IsSimpleGroup (alternatingGroup (Fin m)) :=
        alternatingGroup.isSimpleGroup (by simpa using h5)
      exact φ.isSimpleGroup
    · exfalso
      have : Group.IsSolvable (alternatingGroup (Fin m)) :=
        alternatingGroup.isSolvable (by simp; omega)
      have : Group.IsSolvable (↥L ⧸ pCore 2 ↥L) :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have : Nontrivial (↥L ⧸ pCore 2 ↥L) := by
        obtain ⟨c, d, hcd⟩ := hnab
        exact ⟨⟨c, d, fun h => hcd (by rw [h])⟩⟩
      have := hperf
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ pCore 2 ↥L) inferInstance
  · exact absurd (eq_of_prime_top hX.1 hL.1 hXL (InClassX.not_isPGroup hX) hp hU) hne

end CFSG.CGT.PushingUpLit
