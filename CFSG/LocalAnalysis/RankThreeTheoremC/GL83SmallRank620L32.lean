module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp

open Subgroup CFSG.QuasithinUnique.Setup.Family

private theorem pow_three_eq_one_of_orderOf {l : GL32} (hl : orderOf l = 3) : l ^ 3 = 1 := by
  have := pow_orderOf_eq_one l
  rwa [hl] at this

private theorem exists_conj_zpowers_eq {l : GL32} (hl : orderOf l = 3) :
    ∃ g : GL32, zpowers (g * l * g⁻¹) = zpowers l₀ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers (pow_three_eq_one_of_orderOf hl)
  refine ⟨g, Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg) ?_⟩
  have hord : orderOf (g * l * g⁻¹) = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective l).trans hl
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_l₀, hord]

private theorem eq_one_of_commute_of_orderOf_eq_three {l s : GL32} (hl : orderOf l = 3)
    (hs : s * l = l * s) (hs2 : s ^ 2 = 1) : s = 1 := by
  obtain ⟨g, hg⟩ := exists_conj_zpowers_eq hl
  have hc : Commute (g * s * g⁻¹) (g * l * g⁻¹) := by
    show g * s * g⁻¹ * (g * l * g⁻¹) = g * l * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * l * g⁻¹) = g * (s * l) * g⁻¹ := by group
      _ = g * (l * s) * g⁻¹ := by rw [hs]
      _ = g * l * g⁻¹ * (g * s * g⁻¹) := by group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ▸ mem_zpowers l₀ : l₀ ∈ zpowers (g * l * g⁻¹))
  have hc0 : g * s * g⁻¹ * l₀ = l₀ * (g * s * g⁻¹) := by
    rw [← hk]
    exact (hc.zpow_right k).eq
  have h1 : g * s * g⁻¹ = 1 :=
    eq_one_of_commute_l₀ hc0 (by rw [conj_pow, hs2]; group)
  calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

private theorem card_modEq_three_of_iterate {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f (f a)) = a) : Nat.card α ≡ Nat.card {a // f a = a} [MOD 3] := by
  classical
  have := Fintype.ofFinite α
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    funext a
    exact hf a)
  rw [Nat.card_eq_fintype_card]
  have h : Nat.card {a // f a = a} = Fintype.card (Function.fixedPoints f) :=
    (Nat.card_eq_fintype_card (α := Function.fixedPoints f))
  rw [h]
  exact key

private theorem eq_one_of_commute_of_isPGroup {N : Subgroup GL32} (hN : IsPGroup 2 N) {l v : GL32}
    (hl : orderOf l = 3) (hv : v ∈ N) (hc : v * l = l * v) : v = 1 := by
  by_contra h1
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hN ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := fun h => h1 (orderOf_eq_one_iff.1 (by rw [hk, h, pow_zero]))
  have hdvd : 2 ∣ orderOf v := hk ▸ dvd_pow_self 2 hk0
  have hs := orderOf_pow_orderOf_div (x := v) (n := 2) (by rw [hk]; exact pow_ne_zero _ two_ne_zero)
    hdvd
  have hs2 : (v ^ (orderOf v / 2)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (v ^ (orderOf v / 2))
    rwa [hs] at this
  have hs1 := eq_one_of_commute_of_orderOf_eq_three hl
    (Commute.pow_left (show Commute v l from hc) _) hs2
  rw [hs1, orderOf_one] at hs
  exact absurd hs (by norm_num)

private theorem card_modEq_one_of_normalized {N : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hN : IsPGroup 2 N) (hlN : l ∈ normalizer (N : Set GL32)) : Nat.card N ≡ 1 [MOD 3] := by
  have h3 : l * l * l = 1 := by
    rw [← pow_three']
    exact pow_three_eq_one_of_orderOf hl
  let f : N → N := fun v => ⟨l * v * l⁻¹, (mem_normalizer_iff.1 hlN v).1 v.2⟩
  have hf : ∀ v, f (f (f v)) = v := fun v => by
    apply Subtype.ext
    show l * (l * (l * v * l⁻¹) * l⁻¹) * l⁻¹ = v
    calc _ = (l * l * l) * v * (l * l * l)⁻¹ := by group
      _ = v := by rw [h3]; simp
  have hfix1 : ∀ a : N, f a = a → a = 1 := fun a ha =>
    Subtype.ext (eq_one_of_commute_of_isPGroup hN hl a.2 (by
      have := congrArg Subtype.val ha
      calc (a : GL32) * l = (l * a * l⁻¹) * l := by rw [show l * a * l⁻¹ = a from this]
        _ = l * a := by group))
  have hcard : Nat.card {a // f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ((hfix1 x x.2).trans (hfix1 y y.2).symm)⟩, ⟨⟨1, ?_⟩⟩⟩
    exact Subtype.ext (by show l * 1 * l⁻¹ = 1; group)
  have hmod := card_modEq_three_of_iterate f hf
  rwa [hcard] at hmod

private theorem isSimpleGroup_GL32_of_psl : IsSimpleGroup GL32 := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
      (Or.inl le_rfl)).2.1
  exact pslEquiv.symm.isSimpleGroup

private theorem normalizer_ne_top_of_card_four {V : Subgroup GL32} (hcard : Nat.card V = 4) :
    normalizer (V : Set GL32) ≠ ⊤ := fun h => by
  have := isSimpleGroup_GL32_of_psl
  have : V.Normal := normalizer_eq_top_iff.1 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  · rw [ht, Subgroup.card_top, card_GL] at hcard
    exact absurd hcard (by norm_num)

private theorem eight_dvd_card_normalizer {V : Subgroup GL32} (hV : IsPGroup 2 V)
    (hcard : Nat.card V = 4) : 8 ∣ Nat.card (normalizer (V : Set GL32)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hVS⟩ := hV.exists_le_sylow
  have h8 : 2 ^ 3 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by rw [card_GL]; norm_num)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 S.isPGroup'
  have hSdvd : Nat.card S ∣ 168 := card_GL ▸ (S : Subgroup GL32).card_subgroup_dvd_card
  have hS8 : Nat.card S = 8 := by
    rw [hk] at h8 hSdvd ⊢
    have : k < 8 := by
      by_contra hk8
      have := Nat.le_of_dvd (by norm_num) hSdvd
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> revert h8 hSdvd <;> norm_num
  have hrel : V.relIndex S = 2 := by
    have := relIndex_mul_card V S
    rw [inf_eq_left.2 hVS, hcard, hS8] at this
    omega
  have : (V.subgroupOf S).Normal := normal_of_index_eq_two hrel
  exact hS8 ▸ card_dvd_of_le (le_normalizer_of_normal_subgroupOf hVS)

theorem index_normalizer_eq_seven {V : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 4) (hlV : l ∈ normalizer (V : Set GL32)) :
    (normalizer (V : Set GL32)).index = 7 := by
  have h8N := eight_dvd_card_normalizer hV hcard
  have h3N : 3 ∣ Nat.card (normalizer (V : Set GL32)) := by
    have := orderOf_dvd_natCard (⟨l, hlV⟩ : normalizer (V : Set GL32))
    rwa [Subgroup.orderOf_mk, hl] at this
  have hNdvd : Nat.card (normalizer (V : Set GL32)) ∣ 168 :=
    card_GL ▸ card_subgroup_dvd_card _
  have hNne : Nat.card (normalizer (V : Set GL32)) ≠ 168 := fun h =>
    normalizer_ne_top_of_card_four hcard ((card_eq_iff_eq_top _).1 (h.trans card_GL.symm))
  obtain ⟨m, hm⟩ : 24 ∣ Nat.card (normalizer (V : Set GL32)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8N h3N
  have hm7 : m ∣ 7 := by
    rw [hm, show (168 : ℕ) = 24 * 7 by norm_num] at hNdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hNdvd
  have h24 : Nat.card (normalizer (V : Set GL32)) = 24 := by
    rcases (Nat.dvd_prime (by norm_num)).1 hm7 with rfl | rfl <;> omega
  have := card_mul_index (normalizer (V : Set GL32))
  rw [h24, card_GL] at this
  omega

set_option linter.unusedVariables false in
theorem le_of_normal_two_subgroup {V N : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hcard : Nat.card V = 4) (hV : IsPGroup 2 V) (hlV : l ∈ normalizer (V : Set GL32))
    (hVN : V ≤ N) (hN : IsPGroup 2 N) (hlN : l ∈ normalizer (N : Set GL32)) : N ≤ V := by
  have hmod := card_modEq_one_of_normalized hl hN hlN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hN
  have hdvd : Nat.card N ∣ 168 := card_GL ▸ card_subgroup_dvd_card N
  have h4 : Nat.card V ∣ Nat.card N := card_dvd_of_le hVN
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans (hn ▸ hdvd)
    norm_num at this
  have hN4 : Nat.card N = 4 := by
    rw [hn] at hmod h4 ⊢
    rw [hcard] at h4
    interval_cases n
    · norm_num at h4
    · norm_num at h4
    · norm_num
    · exact absurd hmod (by decide)
  exact (eq_of_le_of_card_ge hVN (by rw [hN4, hcard])).ge

end CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
