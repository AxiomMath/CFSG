module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3T

open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem commutator_mem_of_mod {L F : Subgroup Y} [hL : L.Normal]
    (hFL : ∀ f ∈ F, ∀ y : Y, ⁅f, y⁆ ∈ L) {a b : Y} (hab : a ∈ F ∨ b ∈ F ∨ a⁻¹ * b ∈ F) :
    ⁅a, b⁆ ∈ L := by
  rcases hab with ha | hb | hf
  · exact hFL a ha b
  · rw [← commutatorElement_inv]
    exact L.inv_mem (hFL b hb a)
  · have h1 : ⁅a, b⁆ = a * ⁅a⁻¹ * b, a⁆⁻¹ * a⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact hL.conj_mem _ (L.inv_mem (hFL _ hf a)) a

theorem commutator_mem_of_le_sup_center {L F : Subgroup Y} [hL : L.Normal]
    (hF : F ≤ L ⊔ Subgroup.center Y) : ∀ f ∈ F, ∀ y : Y, ⁅f, y⁆ ∈ L := by
  intro f hf y
  have h1 : f ∈ ((L ⊔ Subgroup.center Y : Subgroup Y) : Set Y) := hF hf
  rw [Subgroup.mul_normal L (Subgroup.center Y)] at h1
  obtain ⟨l, hl, z, hz, rfl⟩ := h1
  have hzc : ∀ g : Y, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have h2 : ⁅l * z, y⁆ = l * (y * l⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    calc l * z * y * (l * z)⁻¹ * y⁻¹ = l * (z * y) * z⁻¹ * l⁻¹ * y⁻¹ := by group
      _ = l * (y * z) * z⁻¹ * l⁻¹ * y⁻¹ := by rw [hzc y]
      _ = l * (y * l⁻¹ * y⁻¹) := by group
  rw [h2]
  exact L.mul_mem hl (hL.conj_mem _ (L.inv_mem hl) y)

theorem eq_one_or_eq_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2)
    (x y : G) : x = 1 ∨ y = 1 ∨ x = y := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hx, hy, hxy⟩ := hne
  have := Fintype.ofFinite G
  have h3 : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]), Finset.card_pair hxy]
  have h4 := Finset.card_le_univ ({1, x, y} : Finset G)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem card_le_two_of_forall {G : Type*} [Group G] [Finite G]
    (h : ∀ x y : G, x = 1 ∨ y = 1 ∨ x = y) : Nat.card G ≤ 2 := by
  classical
  have := Fintype.ofFinite G
  by_contra hlt
  push Not at hlt
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hlt
  rcases h a b with ha | hb | e
  · rcases h b c with hb | hc | e'
    · exact hab (ha.trans hb.symm)
    · exact hac (ha.trans hc.symm)
    · exact hbc e'
  · rcases h a c with ha | hc | e'
    · exact hab (ha.trans hb.symm)
    · exact hbc (hb.trans hc.symm)
    · exact hac e'
  · exact hab e

variable [Finite Y]

theorem center_inf_commutator_le {L H : Subgroup Y} (hodd : Odd H.index) (hHL : ⁅H, H⁆ ≤ L)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center Y)) : Subgroup.center Y ⊓ commutator Y ≤ L := by
  intro z hz
  obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.mp hz
  have hkey : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : g₀ * z ^ k = z ^ k * g₀ :=
      Subgroup.mem_center_iff.mp ((Subgroup.center Y).pow_mem hzZ k) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have h1 : MonoidHom.transfer (Abelianization.of : ↥H →* Abelianization ↥H) z = 1 :=
    Abelianization.commutator_subset_ker _ hzC
  rw [MonoidHom.transfer_eq_pow _ z hkey] at h1
  have h2 : z ^ H.index ∈ ⁅H, H⁆ := by
    rw [← H.map_subtype_commutator]
    refine ⟨⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z hkey⟩, ?_, rfl⟩
    rw [← Abelianization.ker_of]
    exact h1
  have h3 : z ^ H.index ∈ L := hHL h2
  obtain ⟨k, hk⟩ := hZ2 ⟨z, hzZ⟩
  have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : H.index.Coprime (orderOf z) :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hzk)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact L.pow_mem h3 m

theorem center_le_of_le_commutator {L F : Subgroup Y} [L.Normal] [F.Normal]
    (hFL : ∀ f ∈ F, ∀ y : Y, ⁅f, y⁆ ∈ L) (h4 : ¬ 4 ∣ F.index)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center Y)) (hZc : Subgroup.center Y ≤ commutator Y) :
    Subgroup.center Y ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (Y ⧸ F)))
  set H : Subgroup Y := (T : Subgroup (Y ⧸ F)).comap (QuotientGroup.mk' F) with hH
  have hHi : H.index = (T : Subgroup (Y ⧸ F)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective F)
  have hodd : Odd H.index := by
    rw [hHi, Nat.odd_iff]
    have := T.not_dvd_index
    omega
  have hT2 : Nat.card (T : Subgroup (Y ⧸ F)) ≤ 2 := by
    rw [T.card_eq_multiplicity]
    set e := (Nat.card (Y ⧸ F)).factorization 2 with he
    have hdvd : 2 ^ e ∣ Nat.card (Y ⧸ F) := Nat.ordProj_dvd _ 2
    have he1 : e ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h44 : 2 ^ 2 ∣ Nat.card (Y ⧸ F) := (pow_dvd_pow 2 hlt).trans hdvd
      exact h4 (by rw [Subgroup.index]; simpa using h44)
    interval_cases e <;> norm_num
  have hHL : ⁅H, H⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    apply commutator_mem_of_mod hFL
    have ha' : QuotientGroup.mk' F a ∈ (T : Subgroup (Y ⧸ F)) := ha
    have hb' : QuotientGroup.mk' F b ∈ (T : Subgroup (Y ⧸ F)) := hb
    rcases eq_one_or_eq_of_card_le_two hT2 ⟨_, ha'⟩ ⟨_, hb'⟩ with h | h | h
    · left
      have h1 : QuotientGroup.mk' F a = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff a).mp h1
    · right; left
      have h1 : QuotientGroup.mk' F b = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff b).mp h1
    · right; right
      have h1 : QuotientGroup.mk' F a = QuotientGroup.mk' F b := congrArg Subtype.val h
      exact QuotientGroup.eq.mp h1
  intro z hz
  exact center_inf_commutator_le hodd hHL hZ2 (Subgroup.mem_inf.mpr ⟨hz, hZc hz⟩)

theorem exists_index_two {F : Subgroup Y} [F.Normal] (h : F.index = 2 ∨ F.index = 6) :
    ∃ N : Subgroup Y, F ≤ N ∧ N.index = 2 := by
  rcases h with h | h
  · exact ⟨F, le_rfl, h⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 (Y ⧸ F)))
    have hcard : Nat.card (Y ⧸ F) = 6 := by rw [← h, Subgroup.index]
    have hP3 : Nat.card (P : Subgroup (Y ⧸ F)) = 3 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      have hdvd : Nat.card (P : Subgroup (Y ⧸ F)) ∣ 6 :=
        hcard ▸ Subgroup.card_subgroup_dvd_card _
      have h3 : 3 ∣ Nat.card (P : Subgroup (Y ⧸ F)) :=
        P.dvd_card_of_dvd_card (by rw [hcard]; norm_num)
      rw [hn] at hdvd h3 ⊢
      rcases n with _ | _ | n
      · norm_num at h3
      · rfl
      · exfalso
        have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega : 2 ≤ n + 1 + 1)).trans hdvd
        norm_num at h9
    have hPi : (P : Subgroup (Y ⧸ F)).index = 2 := by
      have := (P : Subgroup (Y ⧸ F)).card_mul_index
      rw [hP3, hcard] at this
      omega
    refine ⟨(P : Subgroup (Y ⧸ F)).comap (QuotientGroup.mk' F), fun f hf => ?_, ?_⟩
    · have h1 : QuotientGroup.mk' F f = 1 := (QuotientGroup.eq_one_iff f).mpr hf
      show QuotientGroup.mk' F f ∈ (P : Subgroup (Y ⧸ F))
      rw [h1]
      exact one_mem _
    · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective F), hPi]

theorem false_of_index {L F : Subgroup Y} [L.Normal] [F.Normal]
    (hFL : ∀ f ∈ F, ∀ y : Y, ⁅f, y⁆ ∈ L) (hZF : Subgroup.center Y ≤ F)
    (hZL : ¬ Subgroup.center Y ≤ L) (hZ2 : IsPGroup 2 ↥(Subgroup.center Y))
    (hi : F.index = 2 ∨ F.index = 6) (hc : (commutator Y).index ≤ 2) : False := by
  obtain ⟨N, hFN, hN2⟩ := exists_index_two hi
  have hcN : commutator Y ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group,
      Subgroup.mul_mem_iff_of_index_two hN2, Subgroup.mul_mem_iff_of_index_two hN2,
      Subgroup.mul_mem_iff_of_index_two hN2, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  have hNc : N ≤ commutator Y := by
    have hle := Subgroup.relIndex_mul_index hcN
    rw [hN2] at hle
    have hpos : (commutator Y).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (commutator Y).relIndex N = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  apply hZL
  refine center_le_of_le_commutator hFL ?_ hZ2 ((hZF.trans hFN).trans hNc)
  rcases hi with h | h <;> rw [h] <;> norm_num

omit [Finite Y] in
theorem false_of_top {L : Subgroup Y} (hFL : ∀ f : Y, ∀ y : Y, ⁅f, y⁆ ∈ L)
    (hZL : ¬ Subgroup.center Y ≤ L) (hc : commutator Y = ⊤) : False := by
  apply hZL
  have hle : commutator Y ≤ L := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hFL a b
  intro z _
  exact hle (hc ▸ Subgroup.mem_top z)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3T
