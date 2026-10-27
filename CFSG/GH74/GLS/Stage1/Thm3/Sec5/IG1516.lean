module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup MulAction CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

section Extremal

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem exists_extremal_conj {P : Subgroup Y} (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.index) {u : Y}
    (hu : ∃ n, orderOf u = p ^ n) :
    ∃ g : Y, g⁻¹ * u * g ∈ P ∧ IsExtremalIn p P (g⁻¹ * u * g) := by
  obtain ⟨D, hDC, hDp, hDsyl, huD⟩ := exists_sylow_centralizer (p := p) hu
  have hcard : ¬ p ∣ Nat.card (fixedPoints D (Y ⧸ P)) := by
    have hmod := hDp.card_modEq_card_fixedPoints (Y ⧸ P)
    rw [← Nat.ModEq.dvd_iff hmod dvd_rfl, ← Subgroup.index_eq_card]
    exact hPidx
  have hne : (fixedPoints D (Y ⧸ P)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hcard
    rw [h]
    simp
  obtain ⟨x, hx⟩ := hne
  exact ⟨x.out, extremal_of_fixed hP hDC hDsyl huD hx⟩

end Extremal

section IndexTwo

variable {Y : Type*} [Group Y]

omit [Group Y] in
theorem inv_mul_mem_of_relIndex_two {Y : Type*} [Group Y] {P Q : Subgroup Y} (h : Q.relIndex P = 2) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (haQ : a ∉ Q) (hbQ : b ∉ Q) : a⁻¹ * b ∈ Q := by
  have h2 : (Q.subgroupOf P).index = 2 := h
  have hiff := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : ↥P)⁻¹) (b := ⟨b, hb⟩)
  have hmem : ((⟨a, ha⟩ : ↥P)⁻¹ * ⟨b, hb⟩) ∈ Q.subgroupOf P := by
    rw [hiff]
    constructor
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h1)) haQ
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.mp h1) hbQ
  simpa [Subgroup.mem_subgroupOf] using hmem

end IndexTwo

section Main

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_extremal_conj_in_index_two {P Q : Subgroup Y} (hP : IsPGroup 2 ↥P) (hPidx : ¬ 2 ∣ P.index) (hQP : Q ≤ P)
    (hidx : Q.relIndex P ≤ 2) {u : Y} (hu2 : orderOf u = 2)
    (hnorm : ∀ (M : Subgroup Y) [M.Normal], IsCyclic (Y ⧸ M) → IsPGroup 2 (Y ⧸ M) → u ∈ M) :
    ∃ g : Y, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn 2 P (g⁻¹ * u * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀P, hg₀ext⟩ := exists_extremal_conj hP hPidx (u := u) ⟨1, by simpa using hu2⟩
  by_cases hq : g₀⁻¹ * u * g₀ ∈ Q
  · exact ⟨g₀, hq, hg₀ext⟩
  have hrel : Q.relIndex P = 2 := by
    have hpos : Q.relIndex P ≠ 0 := by
      have : Finite (↥P ⧸ Q.subgroupOf P) := inferInstance
      exact Subgroup.index_ne_zero_of_finite
    have h1 : Q.relIndex P ≠ 1 := by
      intro h1
      have hle : P ≤ Q := Subgroup.relIndex_eq_one.mp h1
      exact hq (hle hg₀P)
    omega
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2, pow_two] at h
    exact h
  have hu₀2 : (g₀⁻¹ * u * g₀) ^ 2 = 1 := by
    calc (g₀⁻¹ * u * g₀) ^ 2 = g₀⁻¹ * (u * u) * g₀ := by rw [pow_two]; group
      _ = 1 := by rw [huu]; group
  have hnormQ : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hrel
  have hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq'
    have h := hnormQ.conj_mem ⟨q, hQP hq'⟩ (Subgroup.mem_subgroupOf.mpr hq') ⟨t, ht⟩
    simpa [Subgroup.mem_subgroupOf] using h
  have hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
    refine ⟨g₀⁻¹ * u * g₀, hg₀P, fun t ht => ?_⟩
    by_cases htQ : t ∈ Q
    · exact ⟨0, by simp [htQ]⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_relIndex_two hrel hg₀P ht hq htQ⟩
  have hb : ∀ (g : Y) (k : ℕ), g⁻¹ * (g₀⁻¹ * u * g₀) ^ (2 * k) * g ∈ P →
      g⁻¹ * (g₀⁻¹ * u * g₀) ^ (2 * k) * g ∈ Q := by
    intro g k _
    rw [pow_mul, hu₀2, one_pow]
    simp
  have hc : ∀ g : Y, g⁻¹ * (g₀⁻¹ * u * g₀) * g ∈ P → IsExtremalIn 2 P (g⁻¹ * (g₀⁻¹ * u * g₀) * g) →
      g⁻¹ * (g₀⁻¹ * u * g₀) * g ∈ Q ∨ (g₀⁻¹ * u * g₀)⁻¹ * (g⁻¹ * (g₀⁻¹ * u * g₀) * g) ∈ Q := by
    intro g hgP _
    by_cases hw : g⁻¹ * (g₀⁻¹ * u * g₀) * g ∈ Q
    · exact Or.inl hw
    · exact Or.inr (inv_mul_mem_of_relIndex_two hrel hg₀P hgP hq hw)
  rcases thompson_transfer_1515 (p := 2) hP hPidx hQn hcyc hg₀P hq hb hc with
    ⟨M, hMn, hMcyc, hMp, hM⟩ | ⟨g, hgQ, hgext, -⟩
  · exfalso
    apply hM
    have h := hMn.conj_mem u (hnorm M hMcyc hMp) g₀⁻¹
    simpa using h
  · refine ⟨g₀ * g, ?_, ?_⟩
    · have e : (g₀ * g)⁻¹ * u * (g₀ * g) = g⁻¹ * (g₀⁻¹ * u * g₀) * g := by group
      rw [e]
      exact hgQ
    · have e : (g₀ * g)⁻¹ * u * (g₀ * g) = g⁻¹ * (g₀⁻¹ * u * g₀) * g := by group
      rw [e]
      exact hgext

end Main

section Transport

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_centralizer (X : Subgroup G) (v : ↥X) :
    (centralizer ({v} : Set ↥X)).map X.subtype = X ⊓ centralizer ({(v : G)} : Set G) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy v (Set.mem_singleton v))
  · rintro ⟨hz, hzc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, rfl⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc _ (Set.mem_singleton _))

theorem isSylowOf_of_isExtremalIn {X P : Subgroup G} (hPX : P ≤ X) {v : ↥X}
    (h : IsExtremalIn 2 (P.subgroupOf X) v) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ centralizer ({(v : G)} : Set G))
      (X ⊓ centralizer ({(v : G)} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (P.subgroupOf X ⊓ centralizer ({v} : Set ↥X)) (centralizer ({v} : Set ↥X)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr h
  have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) X).mpr h1
  rw [Subgroup.map_inf _ _ _ X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hPX,
    map_subtype_centralizer, ← inf_assoc, inf_eq_left.mpr hPX] at h2
  exact h2

end Transport

theorem ig_15_16_ext_thm : IG_15_16_ext := by
  intro G _ _ X P Q₀ N u hSyl hQP hidx hNX _ hNodd huP hu2 huc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : P ≤ X := hSyl.le
  have huX : u ∈ X := hPX huP
  obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hPp : IsPGroup 2 ↥(P.subgroupOf X) := by
    rw [← hS]
    exact S.isPGroup'
  have hPidx : ¬ 2 ∣ (P.subgroupOf X).index := by
    rw [← hS]
    exact S.not_dvd_index
  have hQP' : Q₀.subgroupOf X ≤ P.subgroupOf X := fun x hx => hQP hx
  have hidx' : (Q₀.subgroupOf X).relIndex (P.subgroupOf X) ≤ 2 := by
    rwa [Subgroup.relIndex_subgroupOf hPX]
  have hu2' : orderOf (⟨u, huX⟩ : ↥X) = 2 := by
    rw [← hu2]
    exact Subgroup.orderOf_mk u huX
  have hnorm : ∀ (M : Subgroup ↥X) [M.Normal], IsCyclic (↥X ⧸ M) → IsPGroup 2 (↥X ⧸ M) →
      (⟨u, huX⟩ : ↥X) ∈ M := by
    intro M _ hcyc hp
    let _ : CommGroup (↥X ⧸ M) := IsCyclic.commGroup
    have hcomm : ⁅X, X⁆ ≤ M.map X.subtype := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      refine ⟨⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆, ?_, rfl⟩
      show ⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆ ∈ M
      have h := map_commutatorElement (QuotientGroup.mk' M) (⟨a, ha⟩ : ↥X) ⟨b, hb⟩
      have h1 : ⁅QuotientGroup.mk' M (⟨a, ha⟩ : ↥X), QuotientGroup.mk' M ⟨b, hb⟩⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
      rw [← QuotientGroup.eq_one_iff (N := M)]
      exact h.trans h1
    have hN : N ≤ M.map X.subtype := by
      intro n hn
      refine ⟨⟨n, hNX hn⟩, ?_, rfl⟩
      show (⟨n, hNX hn⟩ : ↥X) ∈ M
      rw [← QuotientGroup.eq_one_iff (N := M)]
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hp (QuotientGroup.mk (s := M) ⟨n, hNX hn⟩)
      have h1 : orderOf (QuotientGroup.mk (s := M) (⟨n, hNX hn⟩ : ↥X)) ∣ orderOf n := by
        have := orderOf_map_dvd (QuotientGroup.mk' M) (⟨n, hNX hn⟩ : ↥X)
        rwa [Subgroup.orderOf_mk] at this
      have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
      have h3 : 2 ^ k ∣ Nat.card N := by
        rw [← hk]
        exact h1.trans h2
      have hk0 : k = 0 := by
        by_contra hk0
        have : 2 ∣ Nat.card N := (dvd_pow_self 2 hk0).trans h3
        exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    obtain ⟨m, hm, hmu⟩ := (sup_le hcomm hN : ⁅X, X⁆ ⊔ N ≤ M.map X.subtype) huc
    have : m = ⟨u, huX⟩ := Subtype.ext hmu
    rwa [this] at hm
  obtain ⟨g, hgQ, hgext⟩ :=
    exists_extremal_conj_in_index_two hPp hPidx hQP' hidx' hu2' hnorm
  have e : ((g⁻¹ * ⟨u, huX⟩ * g : ↥X) : G) = (g : G)⁻¹ * u * g := by simp
  refine ⟨(g : G), g.2, ?_, ?_⟩
  · have h := Subgroup.mem_subgroupOf.mp hgQ
    rwa [e] at h
  · have h := isSylowOf_of_isExtremalIn hPX hgext
    rwa [e] at h

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
