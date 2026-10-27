module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.FixLargeSylow
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Out
public import CFSG.LieType.Multipliers.U62Bridge

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Fischer CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Certified


theorem center_T46_eq_bot_of_simple : center T46 = ⊥ := by
  haveI := isSimpleGroup_T46
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T46) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : T46, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    haveI : IsMulCommutative T46 := ⟨⟨hc⟩⟩
    have hp := (Group.is_simple_iff_prime_card (α := T46)).1 isSimpleGroup_T46
    rw [card_T46] at hp
    exact absurd hp (by norm_num)

theorem fixLarge_T46 : FixLarge T46 := by
  intro σ hσ
  have hA : uA.subgroupOf T46 ≤ uS.subgroupOf T46 := fun x hx =>
    Subgroup.mem_subgroupOf.2 (uA_le_uS (Subgroup.mem_subgroupOf.1 hx))
  have hcardA : Nat.card (uA.subgroupOf T46) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe uA_le_T46).toEquiv, card_uA]
  refine four_lt_card_fixedSubgroup_of_unique_abelian (S₀ := uS.subgroupOf T46)
    (A₀ := uA.subgroupOf T46) uS_isPGroup not_two_dvd_index_uS hA ?_ ?_
    (by rw [hcardA]; norm_num) ?_ σ hσ
  · intro x hx y hy
    exact Subtype.ext (uA_comm _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
  · intro x hx
    apply Subtype.ext
    have h := uA_sq _ (Subgroup.mem_subgroupOf.1 hx)
    rw [sq] at h
    exact h
  · intro B hB hBc hBcard
    have hB'S : B.map T46.subtype ≤ uS := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hB hb)
    have hB'c : ∀ x ∈ B.map T46.subtype, ∀ y ∈ B.map T46.subtype, x * y = y * x := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      exact congrArg Subtype.val (hBc b hb c hc)
    have hcard' : Nat.card (B.map T46.subtype) = Nat.card B :=
      Subgroup.card_map_of_injective T46.subtype_injective
    obtain ⟨-, h512⟩ := abelian_le_uS hB'S hB'c
    have hB'eq : B.map T46.subtype = uA := h512 (by rw [hcard', hBcard, hcardA])
    have hle : B ≤ uA.subgroupOf T46 := fun b hb =>
      Subgroup.mem_subgroupOf.2 (hB'eq ▸ ⟨b, hb, rfl⟩)
    exact Subgroup.eq_of_le_of_card_ge hle hBcard.symm.le

theorem eight_dvd_card_centralizerIn_uK {j : Equiv.Perm (Fin 693)}
    (hj : j = j1 ∨ j = j2 ∨ j = j3) : 8 ∣ Nat.card (centralizerIn uK j) := by
  have h := ncard_conjClass_mul_card uK j
  rw [card_uK] at h
  obtain ⟨-, h1, h2, h3⟩ := korbits
  rcases hj with rfl | rfl | rfl
  · rw [h1] at h; omega
  · rw [h2] at h; omega
  · rw [h3] at h; omega

theorem two_pow_dvd_card_inf_centralizer {j : Equiv.Perm (Fin 693)} (hjA : j ∈ uA)
    (hj : j = j1 ∨ j = j2 ∨ j = j3) :
    2 ^ 12 ∣ Nat.card ↥(T46 ⊓ Subgroup.centralizer ({j} : Set (Equiv.Perm (Fin 693)))) := by
  set D := centralizerIn uK j with hD
  have hDK : D ≤ uK := inf_le_left
  have hnorm : D ≤ Subgroup.normalizer (uA : Set (Equiv.Perm (Fin 693))) :=
    hDK.trans uK_le_normalizer
  have hdisj : Disjoint uA D := by
    rw [disjoint_iff, eq_bot_iff]
    exact le_trans (inf_le_inf_left uA hDK) uA_inf_uK.le
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer uA D hnorm
    hdisj
  have hle : uA ⊔ D ≤ T46 ⊓ Subgroup.centralizer ({j} : Set (Equiv.Perm (Fin 693))) := by
    refine sup_le ?_ ?_
    · refine le_inf uA_le_T46 ?_
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact uA_comm a ha j hjA
    · exact le_inf (hDK.trans uK_le_T46) inf_le_right
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
  rw [hcard, card_uA]
  obtain ⟨m, hm⟩ := eight_dvd_card_centralizerIn_uK hj
  rw [hm]
  exact ⟨m, by ring⟩

theorem two_pow_dvd_card_centralizer_T46 (q : T46) (hq2 : q * q = 1) (hq1 : q ≠ 1) :
    2 ^ 12 ∣ Nat.card (centralizer ({q} : Set T46)) := by
  have ho : orderOf (q : Equiv.Perm (Fin 693)) = 2 := by
    apply orderOf_eq_prime
    · rw [sq]; exact congrArg Subtype.val hq2
    · intro h; exact hq1 (Subtype.ext h)
  obtain ⟨g, hg, hcl⟩ := involution_classes q.2 ho
  set c : T46 := ⟨g, hg⟩ with hc
  have hq' : ((MulAut.conj c q : T46) : Equiv.Perm (Fin 693)) = g * (q : Equiv.Perm (Fin 693)) * g⁻¹ :=
    rfl
  rw [← card_centralizer_mulEquiv (MulAut.conj c) q,
    card_centralizer_subtype_eq_card_inf T46 (MulAut.conj c q), hq']
  rcases hcl with h | h | h
  · rw [h]; exact two_pow_dvd_card_inf_centralizer j1_mem (Or.inl rfl)
  · rw [h]; exact two_pow_dvd_card_inf_centralizer j2_mem (Or.inr (Or.inl rfl))
  · rw [h]; exact two_pow_dvd_card_inf_centralizer j3_mem (Or.inr (Or.inr rfl))

theorem excQuot_u62 {Q : Type} [Group Q] (hQ : LieModel Q .PSU 6 2 1) : ExcQuot Q := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hQ
  have hcQ : center Q = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, center_T46_eq_bot_of_simple, Subgroup.map_bot]
  have hout : Nat.card (Outer Q) = 6 :=
    CFSG.RankThree.PartOne.F106.card_outer_psu6 (CFSG.Blueprint.LieModel.statedClassicalModel hQ
      (by decide))
  refine ⟨hcQ, dvd_of_eq (card_mulAut_eq_of_card_outer hcQ hout),
    FixLarge.of_mulEquiv e.symm fixLarge_T46, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, card_T46]
    norm_num
  · intro q hq2 hq1
    left
    rw [← card_centralizer_mulEquiv e q]
    exact two_pow_dvd_card_centralizer_T46 (e q) (by rw [← map_mul, hq2, map_one])
      (fun h => hq1 (e.injective (by rw [h, map_one])))

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
