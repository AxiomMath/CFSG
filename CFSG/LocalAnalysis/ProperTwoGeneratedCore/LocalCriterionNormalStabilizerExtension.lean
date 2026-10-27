module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import Mathlib.GroupTheory.NoncommCoprod

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

variable {A : Type*} [Group A] [Finite A]

theorem normal_two_involution_quotient_card (M : Subgroup A) [M.Normal]
    (z t : A) (hz : orderOf z = 2) (ht : t ^ 2 = 1) (hzM : z ∉ M)
    (hgen : (⊤ : Subgroup A) = M ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers t)
    (hodd : Odd (orderOf (z * t))) :
    let q := QuotientGroup.mk' M
    Nat.card (A ⧸ M) = 2 * orderOf (q (z * t)) ∧ Odd (orderOf (q (z * t))) ∧
      (Subgroup.zpowers (q z)).index = orderOf (q (z * t)) := by
  let q := QuotientGroup.mk' M
  have hqz : orderOf (q z) = 2 := by
    apply orderOf_eq_prime
    · simpa only [map_pow, map_one] using congrArg q ((orderOf_eq_prime_iff.mp hz).1)
    · intro hone
      apply hzM
      exact (QuotientGroup.eq_one_iff z).mp hone
  have hqt : (q t) ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg q ht
  have hqgen : (⊤ : Subgroup (A ⧸ M)) =
      Subgroup.zpowers (q z) ⊔ Subgroup.zpowers (q t) := by
    have himage := congrArg (fun K : Subgroup A => K.map q) hgen
    have hqM : M.map q = ⊥ := QuotientGroup.map_mk'_self M
    simpa only [Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective M),
      Subgroup.map_sup, MonoidHom.map_zpowers, hqM, bot_sup_eq] using himage
  have hqodd : Odd (orderOf (q (z * t))) :=
    hodd.of_dvd_nat (orderOf_map_dvd q (z * t))
  have hqodd' : Odd (orderOf (q z * q t)) := by simpa only [map_mul] using hqodd
  refine ⟨?_, hqodd, ?_⟩
  · simpa only [map_mul] using two_involution_odd_product_card (q z) (q t)
      hqz hqt hqgen hqodd'
  · simpa only [map_mul] using two_involution_odd_product_reflection_index (q z) (q t)
      hqz hqt hqgen hqodd'

omit [Finite A] in
theorem commuting_involution_sup_cases (U : Subgroup A) (z : A)
    (hz : orderOf z = 2) (hc : ∀ s ∈ U, Commute z s) {x : A}
    (hx : x ∈ U ⊔ Subgroup.zpowers z) :
    ∃ s ∈ U, x = s ∨ x = s * z := by
  let Z := Subgroup.zpowers z
  have comm : ∀ s : U, ∀ w : Z, Commute (U.subtype s) (Z.subtype w) := by
    intro s w
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.property
    change Commute (s : A) (w : A)
    rw [← hn]
    exact (hc s s.property).symm.zpow_right n
  let f := U.subtype.noncommCoprod Z.subtype comm
  have hrange : f.range = U ⊔ Z := by
    simpa only [Subgroup.subtype_range] using
      MonoidHom.noncommCoprod_range U.subtype Z.subtype comm
  have hxf : x ∈ f.range := hrange.symm ▸ hx
  obtain ⟨⟨s, w⟩, rfl⟩ := hxf
  have hcard : Nat.card Z = 2 := (Nat.card_zpowers z).trans hz
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hcard
  have hz1 : (⟨z, Subgroup.mem_zpowers z⟩ : Z) ≠ 1 := by
    intro heq
    have hzone := congrArg Subtype.val heq
    exact (orderOf_eq_prime_iff.mp hz).2 hzone
  refine ⟨s, s.property, ?_⟩
  by_cases hw : w = 1
  · left
    simp only [f, MonoidHom.noncommCoprod_apply, hw, map_one, mul_one,
      Subgroup.subtype_apply]
  · right
    have hwz : (w : A) = z := congrArg Subtype.val
      ((ha w hw).trans (ha ⟨z, Subgroup.mem_zpowers z⟩ hz1).symm)
    simp only [f, MonoidHom.noncommCoprod_apply, hwz, Subgroup.subtype_apply]

theorem normal_two_involution_extension_sylow (M : Subgroup A) [M.Normal]
    (z t : A) (hz : orderOf z = 2) (ht : t ^ 2 = 1) (hzM : z ∉ M)
    (hgen : (⊤ : Subgroup A) = M ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers t)
    (hodd : Odd (orderOf (z * t))) (S : Sylow 2 M)
    (hc : ∀ s ∈ (S : Subgroup M).map M.subtype, Commute z s) :
    ∃ P : Sylow 2 A,
      (P : Subgroup A) = (S : Subgroup M).map M.subtype ⊔ Subgroup.zpowers z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup A := (S : Subgroup M).map M.subtype
  let Z := Subgroup.zpowers z
  let K := U ⊔ Z
  let B := M ⊔ Z
  let q := QuotientGroup.mk' M
  have hUM : U ≤ M := Subgroup.map_subtype_le _
  have hKB : K ≤ B := sup_le_sup hUM le_rfl
  have hzU : z ∉ U := fun hzU => hzM (hUM hzU)
  have hzC : z ∈ Subgroup.centralizer (U : Set A) := by
    exact Subgroup.mem_centralizer_iff.mpr (fun s hs => (hc s hs).symm.eq)
  have hUnorm : Z ≤ Subgroup.normalizer (U : Set A) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzC)
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1)
    (by simpa only [pow_one] using (Nat.card_zpowers z).trans hz)
  have hKtwo : IsPGroup 2 K := (S.isPGroup'.map M.subtype).to_sup_of_normal_left'
    hZtwo hUnorm
  have hUrel : U.relIndex K = 2 := by
    apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z), hzU, ?_⟩
    intro x hx
    obtain ⟨s, hs, hxs | hxs⟩ := commuting_involution_sup_cases U z hz hc hx
    · exact Or.inr (hxs ▸ hs)
    · left
      rw [hxs, mul_assoc, ← pow_two, (orderOf_eq_prime_iff.mp hz).1, mul_one]
      exact hs
  have hqz : orderOf (q z) = 2 := by
    apply orderOf_eq_prime
    · simpa only [map_pow, map_one] using congrArg q ((orderOf_eq_prime_iff.mp hz).1)
    · exact fun hone => hzM ((QuotientGroup.eq_one_iff z).mp hone)
  have hqB : B.map q = Subgroup.zpowers (q z) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, MonoidHom.map_zpowers, bot_sup_eq]
  have hMrel : M.relIndex B = 2 := by
    have hrel := Subgroup.relIndex_ker B q
    rw [QuotientGroup.ker_mk', hqB, Nat.card_zpowers, hqz] at hrel
    exact hrel
  have hSindex : U.relIndex M = (S : Subgroup M).index := by
    change (U.comap M.subtype).index = (S : Subgroup M).index
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKrel : K.relIndex B = (S : Subgroup M).index := by
    have h₁ := Subgroup.relIndex_mul_relIndex U K B le_sup_left hKB
    have h₂ := Subgroup.relIndex_mul_relIndex U M B hUM le_sup_left
    rw [hUrel] at h₁
    rw [hMrel, hSindex] at h₂
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    exact h₁.trans (h₂.symm.trans (Nat.mul_comm _ _))
  have hBpre : (Subgroup.zpowers (q z)).comap q = B := by
    rw [← MonoidHom.map_zpowers, QuotientGroup.comap_map_mk']
  have hBindex : Odd B.index := by
    rw [← hBpre, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective M)]
    rw [(normal_two_involution_quotient_card M z t hz ht hzM hgen hodd).2.2]
    exact (normal_two_involution_quotient_card M z t hz ht hzM hgen hodd).2.1
  have hKindex : ¬ 2 ∣ K.index := by
    rw [← Subgroup.relIndex_mul_index hKB, hKrel]
    exact Nat.prime_two.not_dvd_mul S.not_dvd_index hBindex.not_two_dvd_nat
  exact ⟨hKtwo.toSylow hKindex, rfl⟩

end CFSG.ProperTwoGeneratedCore
