module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem perm3_of_card_six {Y : Type} [Group Y] [Finite Y] (hcard : Nat.card Y = 6)
    (hnc : ∃ a b : Y, a * b ≠ b * a) : Nonempty (Y ≃* Equiv.Perm (Fin 3)) := by
  classical
  have h2 : 2 ∣ Nat.card Y := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' Y _ _ 2 ⟨Nat.prime_two⟩ h2
  set P : Subgroup Y := Subgroup.zpowers x with hP
  have hPcard : Nat.card P = 2 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 3 := by
    have := Subgroup.card_mul_index P
    rw [hPcard, hcard] at this
    omega
  have hQcard : Nat.card (Y ⧸ P) = 3 := hidx
  let φ : Y →* Equiv.Perm (Y ⧸ P) := MulAction.toPermHom Y (Y ⧸ P)
  have hker : φ.ker ≤ P := by
    intro g hg
    have h1 : φ g = 1 := hg
    have h2 : g • (QuotientGroup.mk (1 : Y) : Y ⧸ P) = QuotientGroup.mk 1 := by
      have := congrArg (fun σ : Equiv.Perm (Y ⧸ P) => σ (QuotientGroup.mk (1 : Y))) h1
      exact this
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h2
    have h3 := QuotientGroup.eq.mp h2
    rw [mul_one] at h3
    simpa using P.inv_mem h3
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hne
    have hgP : g ∈ P := hker hg
    have hkerP : φ.ker = P := by
      refine le_antisymm hker ?_
      have hle : φ.ker ≤ P := hker
      have hcard1 : Nat.card φ.ker ∣ Nat.card P := by
        have := Subgroup.card_dvd_of_le hle
        simpa using this
      have hne1 : Nat.card φ.ker ≠ 1 := by
        intro h1
        have hmem : g ∈ φ.ker := hg
        rw [Subgroup.eq_bot_of_card_eq _ h1] at hmem
        exact hne (Subgroup.mem_bot.mp hmem)
      have hcard2 : Nat.card φ.ker = 2 := by
        rw [hPcard] at hcard1
        rcases (Nat.dvd_prime Nat.prime_two).mp hcard1 with h | h
        · exact absurd h hne1
        · exact h
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hPcard])).ge
    have hPn : P.Normal := hkerP ▸ φ.normal_ker
    have hcentral : P ≤ Subgroup.center Y := by
      intro p hp
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      rw [Subgroup.mem_center_iff]
      intro y
      have hyx : y * x * y⁻¹ ∈ P := hPn.conj_mem x (Subgroup.mem_zpowers x) y
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyx
      have hm' : x ^ (m % 2) = y * x * y⁻¹ := by
        have := zpow_mod_orderOf x m
        rw [hx] at this
        simpa using this.trans hm
      have hxne : x ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hx
        omega
      have hyx' : y * x * y⁻¹ = x := by
        rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with h | h
        · rw [h, zpow_zero] at hm'
          exact absurd (by simpa using (conj_eq_one_iff.mp hm'.symm)) hxne
        · rw [h, zpow_one] at hm'
          exact hm'.symm
      have hyk : y * x ^ k * y⁻¹ = x ^ k := by
        have := conj_zpow (a := y) (b := x) (i := k)
        rw [← this, hyx']
      calc y * x ^ k = (y * x ^ k * y⁻¹) * y := by group
        _ = x ^ k * y := by rw [hyk]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (Y ⧸ P) := isCyclic_of_prime_card hQcard
    have hf : (QuotientGroup.mk' P).ker ≤ Subgroup.center Y := by
      rw [QuotientGroup.ker_mk']; exact hcentral
    obtain ⟨a, b, hab⟩ := hnc
    haveI := (QuotientGroup.mk' P).isMulCommutative_of_isCyclic_of_ker_le_center hf
    exact hab (IsMulCommutative.is_comm.comm a b)
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_perm, hQcard]
    decide
  haveI : Fintype (Y ⧸ P) := Fintype.ofFinite _
  let e : Y ⧸ P ≃ Fin 3 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hQcard)
  exact ⟨(MulEquiv.ofBijective φ hbij).trans (Equiv.permCongrHom e)⟩

theorem quotShape_sym3 [Finite G] {M N : Subgroup G} (hNM : N ≤ M)
    (hnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hcard : Nat.card M = 6 * Nat.card N)
    {m₁ m₂ : G} (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) (hc : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∉ N) :
    QuotShape M N (Sym 3) := by
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNM).mpr fun h m hh hm => hnorm m hm h hh
  refine ⟨hN, ?_⟩
  have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hq : Nat.card (↥M ⧸ N.subgroupOf M) = 6 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)
    rw [hcardN, hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  let q₁ : ↥M ⧸ N.subgroupOf M := QuotientGroup.mk ⟨m₁, h₁⟩
  let q₂ : ↥M ⧸ N.subgroupOf M := QuotientGroup.mk ⟨m₂, h₂⟩
  refine perm3_of_card_six hq ⟨q₁, q₂, fun h => hc ?_⟩
  have hmem : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem h₁ h₂) (M.inv_mem h₁)) (M.inv_mem h₂)
  have h1 : (QuotientGroup.mk (⟨m₁ * m₂ * m₁⁻¹ * m₂⁻¹, hmem⟩ : ↥M) :
      ↥M ⧸ N.subgroupOf M) = 1 := by
    have e : (⟨m₁ * m₂ * m₁⁻¹ * m₂⁻¹, hmem⟩ : ↥M) =
        ⟨m₁, h₁⟩ * ⟨m₂, h₂⟩ * ⟨m₁, h₁⟩⁻¹ * ⟨m₂, h₂⟩⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    change q₁ * q₂ * q₁⁻¹ * q₂⁻¹ = 1
    rw [h]
    group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
