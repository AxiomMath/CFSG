module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem eq_one_or_eq_of_mem_zpowers {Y : Type*} [Group Y] {t x : Y} (ht : orderOf t = 2)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [h, zpow_zero])
  · exact Or.inr (by rw [h, zpow_one])

theorem quotient_facts_of_centralizer_eq {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X)) :
    IsSimpleGroup (H.map (QuotientGroup.mk' (fusionOddCore X))) ∧
      center (H.map (QuotientGroup.mk' (fusionOddCore X))) = ⊥ ∧
      Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) = Nat.card H ∧
      orderOf (QuotientGroup.mk' (fusionOddCore X) z) = 2 ∧
      QuotientGroup.mk' (fusionOddCore X) z ∈
        centralizer ((H.map (QuotientGroup.mk' (fusionOddCore X)) : Subgroup _) :
          Set (X ⧸ fusionOddCore X)) ∧
      centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) =
        H.map (QuotientGroup.mk' (fusionOddCore X)) ⊔
          zpowers (QuotientGroup.mk' (fusionOddCore X) z) := by
  obtain ⟨hHq, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨eH⟩ := nonempty_map_fusionOddCore_mulEquiv (disjoint_fusionOddCore hHq hZ)
  have hs : IsSimpleGroup (H.map (QuotientGroup.mk' (fusionOddCore X))) := eH.isSimpleGroup
  have hnab' : ∃ a b : H.map (QuotientGroup.mk' (fusionOddCore X)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eH.symm a, eH.symm b, fun h => hab (by simpa using congrArg eH h)⟩
  have hz1 : QuotientGroup.mk' (fusionOddCore X) z ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    intro hzO
    have h2 := Subgroup.orderOf_dvd_natCard (fusionOddCore X) hzO
    rw [hz] at h2
    exact Nat.not_even_iff_odd.2 (odd_natCard_fusionOddCore X) (even_iff_two_dvd.2 h2)
  refine ⟨hs, (isQuasisimple_center_eq_bot_of_isSimpleGroup hnab').2, Nat.card_congr eH.toEquiv,
    orderOf_eq_prime (by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]) hz1, ?_,
    centralizer_mk_fusionOddCore_eq hz hC hz'⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hz' h hh]

theorem map_le_of_two_lt_card_inf_centralizer {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {E : Subgroup (X ⧸ fusionOddCore X)} (hE : E.Normal)
    (h2 : 2 < Nat.card (E ⊓ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
      Set (X ⧸ fusionOddCore X)) : Subgroup (X ⧸ fusionOddCore X))) :
    H.map (QuotientGroup.mk' (fusionOddCore X)) ≤ E := by
  obtain ⟨hs, -, -, ho, ht', hC'⟩ := quotient_facts_of_centralizer_eq hnab hz hC hz'
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by rw [← ho, pow_orderOf_eq_one]
  rcases card_inf_centralizer_le_two_or ht hC' ht' hE with h | ⟨hle, -⟩
  · omega
  · exact hle

theorem centralizer_inf_centralizer_mk_le_zpowers {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {E : Subgroup (X ⧸ fusionOddCore X)} (hHE : H.map (QuotientGroup.mk' (fusionOddCore X)) ≤ E) :
    centralizer (E : Set (X ⧸ fusionOddCore X)) ⊓
        centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) ≤
      zpowers (QuotientGroup.mk' (fusionOddCore X) z) := by
  obtain ⟨-, hZ, -, -, ht', hC'⟩ := quotient_facts_of_centralizer_eq hnab hz hC hz'
  exact (inf_le_inf_right _ (centralizer_le (SetLike.coe_subset_coe.2 hHE))).trans
    (centralizer_inf_centralizer_le_zpowers hZ hC' ht')

theorem eq_zpowers_of_inf_centralizer_le_zpowers {Y : Type*} [Group Y] [Finite Y]
    (hO : fusionOddCore Y = ⊥) {Q : Subgroup Y} (hQ : Q.Normal) {t : Y} (ht : orderOf t = 2)
    (htQ : t ∈ Q) (hCQ : Q ⊓ centralizer ({t} : Set Y) ≤ zpowers t) : Q = zpowers t := by
  set t' : Q := ⟨t, htQ⟩ with ht'def
  have ht' : orderOf t' = 2 := by rw [ht'def, orderOf_mk, ht]
  have hcomm : ∀ x : Q, x * t' = t' * x → x ∈ zpowers t' := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hCQ (mem_inf.2 ⟨x.2,
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx)⟩))
    exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)⟩
  have hP2 : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  obtain ⟨P, hP⟩ := hP2.exists_le_sylow
  have htP : t' ∈ (P : Subgroup Q) := hP (mem_zpowers t')
  have hPle : (P : Subgroup Q) ≤ zpowers t' := by
    have : Nontrivial (P : Subgroup Q) := by
      refine (nontrivial_iff_ne_bot _).2 fun hb => ?_
      rw [hb, mem_bot] at htP
      rw [htP, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    have : Nontrivial (center (P : Subgroup Q)) := P.2.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : center (P : Subgroup Q))
    have hcz : ((c : (P : Subgroup Q)) : Q) * t' = t' * ((c : (P : Subgroup Q)) : Q) :=
      (congrArg Subtype.val (mem_center_iff.1 c.2 ⟨t', htP⟩)).symm
    have hct : ((c : (P : Subgroup Q)) : Q) = t' := by
      rcases eq_one_or_eq_of_mem_zpowers ht' (hcomm _ hcz) with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hc
      · exact h
    intro x hx
    apply hcomm
    have h1 : x * ((c : (P : Subgroup Q)) : Q) = ((c : (P : Subgroup Q)) : Q) * x :=
      congrArg Subtype.val (mem_center_iff.1 c.2 ⟨x, hx⟩)
    rw [hct] at h1
    exact h1
  have hPcard : Nat.card (P : Subgroup Q) = 2 := by
    rw [le_antisymm hPle hP, Nat.card_zpowers, ht']
  have hPcyc : IsCyclic (P : Subgroup Q) := isCyclic_of_prime_card hPcard
  have hmin : (Nat.card Q).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).2 (ht' ▸ _root_.orderOf_dvd_natCard t')
  have hcompl := IsCyclic.isComplement' hmin hPcyc
  set N := (MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hmin)).ker with hN
  have hNodd : Odd (Nat.card N) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (MonoidHom.not_dvd_card_ker_transferSylow P _))
  have hNindex : N.index = 2 := by rw [hcompl.symm.index_eq_card, hPcard]
  have hoddN : ∀ x : Q, Odd (orderOf x) → x ∈ N := by
    intro x hx
    have h1 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
      rw [index_eq_card]
      exact _root_.orderOf_dvd_natCard _
    rw [hNindex] at h1
    have h2 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ _
    have h3 : orderOf (QuotientGroup.mk' N x) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hx)
    rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  have hNY : (N.map Q.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n', hn', rfl⟩ := mem_map.1 hn
    have hgQ : g * (n' : Y) * g⁻¹ ∈ Q := hQ.conj_mem _ n'.2 g
    refine mem_map.2 ⟨⟨_, hgQ⟩, hoddN _ ?_, rfl⟩
    rw [orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_coe]
    exact Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn')
  have hNle : N.map Q.subtype ≤ fusionOddCore Y :=
    le_sSup ⟨hNY, by rwa [card_map_of_injective Q.subtype_injective]⟩
  rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ Q.subtype_injective] at hNle
  have hQcard : Nat.card Q = 2 := by
    rw [← hcompl.card_mul_card, hNle, card_bot, one_mul, hPcard]
  refine (eq_of_le_of_card_ge (zpowers_le.2 htQ) ?_).symm
  rw [hQcard, Nat.card_zpowers, ht]

end CFSG.EvenSporadicStandard.M24Std
