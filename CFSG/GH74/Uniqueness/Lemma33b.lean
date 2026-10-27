module

public import CFSG.GH74.Uniqueness.ProductDisconnected
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

@[expose] def IsZStarIn {X : Type*} [Group X] (M : Subgroup X) (z : X) : Prop :=
  z ∈ M ∧ ∃ N : Subgroup X, N ≤ M ∧ (N.subgroupOf M).Normal ∧ Odd (Nat.card N) ∧
    ∀ m ∈ M, m * z * m⁻¹ * z⁻¹ ∈ N

section Isolated

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem twoRank_le_one_of_isolated (hZ : IsInvariantInvolutionSet Z)
    (hgen : Subgroup.closure Z = ⊤) {z : X} (hz : z ∈ Z) (hcl : ∀ a ∈ Z, IsConj a z)
    (hiso : ∀ y ∈ Z, y * z = z * y → y = z) : Open.twoRank X ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
  have hz1 : z ≠ 1 := by
    intro h1
    have := hZ.1 z hz
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X z hz1 hz2 (fun g hg => by
    apply hiso _ _ hg
    have := hZ.2 z hz g⁻¹
    rwa [inv_inv] at this)
  have hZq : Z ⊆ (((Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N)).comap
      (QuotientGroup.mk' N) : Subgroup X) : Set X) := by
    intro a ha
    obtain ⟨c, hc⟩ := isConj_iff.mp (hcl a ha)
    have h1 : c⁻¹ * z * (c⁻¹)⁻¹ * z⁻¹ ∈ N := hN c⁻¹
    have h2 : a * z⁻¹ ∈ N := by
      have : a = c⁻¹ * z * (c⁻¹)⁻¹ := by
        rw [inv_inv, ← hc]
        group
      rw [this]
      exact h1
    have h3 : (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk z :=
      QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
    show QuotientGroup.mk' N a ∈ Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N)
    rw [QuotientGroup.mk'_apply, h3]
    exact Subgroup.mem_zpowers _
  have hall : ∀ x : X, (QuotientGroup.mk x : X ⧸ N) ∈
      Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N) := by
    intro x
    have : x ∈ (Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N)).comap (QuotientGroup.mk' N) := by
      have hle : Subgroup.closure Z ≤
          (Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N)).comap (QuotientGroup.mk' N) :=
        (Subgroup.closure_le _).mpr hZq
      rw [hgen] at hle
      exact hle (Subgroup.mem_top x)
    exact this
  have htop : Subgroup.zpowers (QuotientGroup.mk z : X ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hall x
  have hcard : Nat.card (X ⧸ N) ≤ 2 := by
    have h1 : Nat.card (X ⧸ N) = orderOf (QuotientGroup.mk z : X ⧸ N) := by
      rw [← Nat.card_zpowers, htop, Subgroup.card_top]
    have h2 : orderOf (QuotientGroup.mk z : X ⧸ N) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two, ← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
    rw [h1]
    exact Nat.le_of_dvd (by norm_num) h2
  have hNodd' : ¬ 2 ∣ Nat.card N := by
    intro h2
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 2) N hNodd'
  have hle : Open.pRank 2 (⊤ : Subgroup (X ⧸ N)) ≤ 1 := by
    apply CFSG.SectionRank.pRank_le Nat.one_lt_two
    intro E _ _
    calc Nat.card E ≤ Nat.card (X ⧸ N) := Subgroup.card_le_card_group E
      _ ≤ 2 := hcard
      _ = 2 ^ 1 := by norm_num
  unfold Open.twoRank
  rw [← hq]
  exact hle

omit [Finite X] in
theorem eq_of_isZStarIn_commute (hZ : IsInvariantInvolutionSet Z) {z y : X} (hz : z ∈ Z)
    (hy : y ∈ Z) (hyz : y * z = z * y) {N : Subgroup X} (hNodd : Odd (Nat.card N))
    (hn : y * z⁻¹ ∈ N) : y = z := by
  have hz2 := hZ.mul_self_eq_one hz
  have hy2 := hZ.mul_self_eq_one hy
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [hzi] at hn
  have hn2 : (y * z) * (y * z) = 1 := by
    calc (y * z) * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [hyz]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy2, hz2, one_mul]
  have hord : orderOf (⟨y * z, hn⟩ : N) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hn2
  have hodd : Odd (orderOf (⟨y * z, hn⟩ : N)) :=
    Odd.of_dvd_nat hNodd (orderOf_dvd_natCard _)
  have h1 : orderOf (⟨y * z, hn⟩ : N) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have : (⟨y * z, hn⟩ : N) = 1 := orderOf_eq_one_iff.mp h1
  have hyz1 : y * z = 1 := congrArg Subtype.val this
  calc y = y * (z * z) := by rw [hz2, mul_one]
    _ = (y * z) * z := by rw [mul_assoc]
    _ = z := by rw [hyz1, one_mul]

end Isolated

section Lemma33b

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.exists_commuting_ne (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hrank : 2 ≤ Open.twoRank X) {z : X} (hz : z ∈ Z) :
    ∃ y ∈ Z, y ≠ z ∧ y * z = z * y := by
  by_contra hno
  push Not at hno
  have := twoRank_le_one_of_isolated hZ hgen hz (fun a ha => h.isConj_of_mem hZ ha hz)
    (fun y hy hyz => by_contra fun hne => hno y hy hne hyz)
  omega

theorem IsProductDisconnected.not_isZStarIn (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hrank : 2 ≤ Open.twoRank X) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) : ¬ IsZStarIn M z := by
  rintro ⟨-, N, -, -, hNodd, hN⟩
  obtain ⟨y, hy, hne, hyz⟩ := h.exists_commuting_ne hZ hgen hrank hz
  have hyM : y ∈ M := h.centralizer_le_of_mem hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  obtain ⟨m, hm, hmy⟩ := h.exists_conj_mem hZ hz hzM hy hyM
  have h1 := hN m⁻¹ (M.inv_mem hm)
  rw [inv_inv, hmy] at h1
  exact hne (eq_of_isZStarIn_commute hZ hz hy hyz hNodd h1)

theorem IsProductDisconnected.two_le_pRank_zHull (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hrank : 2 ≤ Open.twoRank X) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    2 ≤ Open.pRank 2 (zHull Z M) := by
  obtain ⟨y, hy, hne, hyz⟩ := h.exists_commuting_ne hZ hgen hrank hz
  have hyM : y ∈ M := h.centralizer_le_of_mem hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have hzz : z ∈ zHull Z M := Subgroup.subset_closure ⟨hz, hzM⟩
  have hyy : y ∈ zHull Z M := Subgroup.subset_closure ⟨hy, hyM⟩
  have h2 : 2 ≤ Open.twoRank ↥(zHull Z M) :=
    CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions _ ⟨z, hzz⟩ ⟨y, hyy⟩
      (by rw [Subgroup.orderOf_mk]; exact hZ.1 z hz) (by rw [Subgroup.orderOf_mk]; exact hZ.1 y hy)
      (fun hh => hne (congrArg Subtype.val hh).symm) (Subtype.ext hyz.symm)
  have h3 := CFSG.SectionRank.pRank_le_map Nat.one_lt_two (zHull Z M).subtype
    Subtype.val_injective (⊤ : Subgroup ↥(zHull Z M))
  have h4 : (⊤ : Subgroup ↥(zHull Z M)).map (zHull Z M).subtype = zHull Z M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h4] at h3
  exact h2.trans h3

end Lemma33b

end CFSG.GH74.Uniqueness
