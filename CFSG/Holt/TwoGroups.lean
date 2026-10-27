module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Holt

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit

section RankOne

variable {P : Type*} [Group P] [Finite P]

theorem exists_le_isElemAbelian_card_four {E : Subgroup P} (hE : IsElemAbelian 2 E) {k : ℕ}
    (hk : 2 ≤ k) (hcard : Nat.card E = 2 ^ k) :
    ∃ F : Subgroup P, F ≤ E ∧ IsElemAbelian 2 F ∧ Nat.card F = 4 := by
  have := hE.1
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2)
    (show 2 ^ 2 ∣ Nat.card E from hcard ▸ pow_dvd_pow 2 hk)
  refine ⟨F₀.map E.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    have h := congrArg Subtype.val (mul_comm' (⟨a, Subgroup.map_subtype_le F₀ a.2⟩ : E)
      ⟨b, Subgroup.map_subtype_le F₀ b.2⟩)
    simpa using h
  · exact hE.2 x (Subgroup.map_subtype_le F₀ hx)
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF₀]
    norm_num

theorem twoRank_le_one_of_forall_card_ne_four
    (h : ∀ E : Subgroup P, IsElemAbelian 2 E → Nat.card E ≠ 4) : twoRank P ≤ 1 := by
  apply csSup_le'
  rintro k ⟨E, -, hE, hcard⟩
  by_contra hk
  obtain ⟨F, -, hF, hF4⟩ := exists_le_isElemAbelian_card_four hE (by omega) hcard
  exact h F hF hF4

theorem card_ne_four_of_atMostOneInvolution (h : AtMostOneInvolution P) (E : Subgroup P)
    (hE : IsElemAbelian 2 E) : Nat.card E ≠ 4 := by
  classical
  intro h4
  have : Fintype E := Fintype.ofFinite E
  have h2 : 2 < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, h4]
    norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  have key : ∀ x y : E, x ≠ 1 → y ≠ 1 → x = y := fun x y hx hy =>
    Subtype.ext (h _ _ (orderOf_eq_prime (hE.2 _ x.2) fun h1 => hx (Subtype.ext h1))
      (orderOf_eq_prime (hE.2 _ y.2) fun h1 => hy (Subtype.ext h1)))
  by_cases ha : a = 1
  · exact hbc (key b c (ha ▸ hab.symm) (ha ▸ hac.symm))
  · by_cases hb : b = 1
    · exact hac (key a c ha (hb ▸ hbc.symm))
    · exact hab (key a b ha hb)

theorem isCyclic_or_quaternion_of_atMostOneInvolution (hP : IsPGroup 2 P)
    (h : AtMostOneInvolution P) :
    IsCyclic P ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))) :=
  CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P hP
    (twoRank_le_one_of_forall_card_ne_four (card_ne_four_of_atMostOneInvolution h))

end RankOne

section Suzuki

variable {G : Type*} [Group G] [Finite G]

theorem isCyclic_or_dihedral_of_hasDihedralGenerators {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (h : HasDihedralGenerators P) :
    IsCyclic P ∨ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨x, y, hgen, hy2, hrel, hy⟩ := h
  have he := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem x y hgen.symm hy2 hrel hy
  obtain ⟨r, hr⟩ := IsPGroup.iff_orderOf.mp hP x
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · left
    have hx : x = 1 := orderOf_eq_one_iff.mp (by simpa using hr)
    rw [hx, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hgen
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y, hgen⟩
  · exact Or.inr ⟨r, hr0, hr ▸ he⟩

theorem suzuki_index_two {S T : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T)
    (hidx : S.relIndex T = 2) {t : G} (htT : t ∈ T) (htS : t ∉ S) (ht : orderOf t = 2)
    (hC : Nat.card ↥(S ⊓ centralizer {t}) = 2) :
    (IsCyclic S ∨ (∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
        ∃ n : ℕ, 3 ≤ n ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (n - 2)))) ∧
      ((∃ m : ℕ, 1 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ m))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (T ≃* SemidihedralGroup n)) := by
  set S' := S.subgroupOf T
  set t' : T := ⟨t, htT⟩
  have hS'idx : S'.index = 2 := hidx
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have ht'S : t' ∉ S' := htS
  set C' := centralizer ({t'} : Set T)
  have htC : t' ∈ C' := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hCS : Nat.card ↥(S' ⊓ C') = 2 := by
    have e : S' ⊓ C' = (S ⊓ centralizer {t}).subgroupOf T := by
      ext y
      simp only [S', C', t', Subgroup.mem_inf, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul]
    rw [e, ← hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hST)).toEquiv
  have hrel : S'.relIndex C' = 2 := by
    have := Subgroup.normal_of_index_eq_two hS'idx
    have hdvd : S'.relIndex C' ∣ 2 := hS'idx ▸ Subgroup.relIndex_dvd_index_of_normal S' C'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h htC) ht'S
    · exact h
  have hC4 : Nat.card C' = 4 := by rw [← Subgroup.relIndex_mul_card S' C', hrel, hCS]
  have hA2 : ∀ y ∈ S' ⊓ C', y ^ 2 = 1 := fun y hy => by
    have h := pow_card_eq_one' (x := (⟨y, hy⟩ : ↥(S' ⊓ C')))
    rw [hCS] at h
    simpa using congrArg Subtype.val h
  have hexp : ∀ y ∈ C', y ^ 2 = 1 := by
    intro y hy
    by_cases hyS : y ∈ S'
    · exact hA2 y ⟨hyS, hy⟩
    · have h1 : t'⁻¹ * y ∈ S' := (Subgroup.mul_mem_iff_of_index_two hS'idx).mpr
        ⟨fun h => absurd (inv_mem_iff.mp h) ht'S, fun h => absurd h hyS⟩
      have h2 : t'⁻¹ * y ∈ C' := mul_mem (inv_mem htC) hy
      have hcomm : y * t' = t' * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have hc : Commute t' (t'⁻¹ * y) := by
        change t' * (t'⁻¹ * y) = t'⁻¹ * y * t'
        rw [mul_assoc, hcomm, inv_mul_cancel_left, mul_inv_cancel_left]
      have ht2 : t' ^ 2 = 1 := by rw [← ht']; exact pow_orderOf_eq_one t'
      calc y ^ 2 = (t' * (t'⁻¹ * y)) ^ 2 := by rw [mul_inv_cancel_left]
        _ = 1 := by rw [hc.mul_pow, ht2, hA2 _ ⟨h1, h2⟩, one_mul]
  refine ⟨?_, ?_⟩
  · have hS2 : IsPGroup 2 S := hT.to_le hST
    have e : ↥S' ≃* ↥S := Subgroup.subgroupOfEquivOfLe hST
    rcases index_two_small_centralizer_shape hT S' hS'idx ht' ht'S hCS.le with h | h
    · rcases isCyclic_or_quaternion_of_atMostOneInvolution hS2 (h.of_mulEquiv e) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases isCyclic_or_dihedral_of_hasDihedralGenerators hS2 (h.of_mulEquiv e) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  · rcases suzuki_two_group hT hC4 hexp with ⟨n, hn, he⟩ | h
    · exact Or.inl ⟨n - 1, by omega, he⟩
    · exact Or.inr h

end Suzuki

section NoNormalFour

theorem cyclic_or_dihedral_or_semidihedral_or_quaternion_of_no_normal_four {P : Type}
    [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h : ∀ V : Subgroup P, V.Normal → IsElemAbelian 2 V → Nat.card V ≠ 4) :
    IsCyclic P ∨ (∃ m : ℕ, 1 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) ∨
      ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))) := by
  by_cases hrank : ∃ E : Subgroup P, IsElemAbelian 2 E ∧ Nat.card E = 4
  · obtain ⟨E, hE, hE4⟩ := hrank
    rcases CFSG.GH74.Uniqueness.SU.SU1.dihedral_or_semidihedral_of_no_normal_four hP (Q := ⊤)
        (fun V hV _ hVe hV4 => h V hV hVe (hV4.trans (by norm_num)))
        ⟨E, le_top, hE, hE4.trans (by norm_num)⟩ with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨m, hm, ⟨Subgroup.topEquiv.symm.trans e⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨Subgroup.topEquiv.symm.trans e⟩⟩))
  · push Not at hrank
    rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P hP
        (twoRank_le_one_of_forall_card_ne_four hrank) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr h'))

end NoNormalFour

end CFSG.Holt
