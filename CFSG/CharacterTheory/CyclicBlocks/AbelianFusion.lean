module

public import CFSG.CharacterTheory.CyclicBlocks.Fusion

public section

namespace CFSG.CyclicBlocks

variable {G : Type*} [Group G] {p : ℕ}

structure InvertedAbelianSylow (P : Sylow p G) (τ : G) : Prop where
  comm : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x
  index : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2
  mem_normalizer : τ ∈ Subgroup.normalizer (P : Set G)
  conj_eq_inv : ∀ x ∈ (P : Subgroup G), τ * x * τ⁻¹ = x⁻¹

variable [Finite G] [Fact p.Prime]

theorem orderOf_dvd_of_mem_sylow (P : Sylow p G) {x : G} (hx : x ∈ (P : Subgroup G)) :
    orderOf x ∣ p ^ (Nat.card G).factorization p := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup G))
  rwa [Subgroup.orderOf_mk, Sylow.card_eq_multiplicity] at h

theorem card_sylow_odd_three_le_of_relIndex (hp2 : p ≠ 2) (P : Sylow p G)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2) :
    Nat.card P % 2 = 1 ∧ 3 ≤ Nat.card P := by
  have hp : p.Prime := Fact.out
  have hcard := P.card_eq_multiplicity
  generalize (Nat.card G).factorization p = k at hcard
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have hbot := Subgroup.eq_bot_of_card_eq _ hcard
    have hle : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact hh
      rw [Subgroup.mem_bot.mp hh', one_mul, mul_one]
    rw [← Subgroup.relIndex_eq_one] at hle
    omega
  refine ⟨?_, ?_⟩
  · rw [hcard]
    exact Nat.odd_iff.mp (hp.eq_two_or_odd'.resolve_left hp2).pow
  · rw [hcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hk)

namespace InvertedAbelianSylow

variable {P : Sylow p G} {τ : G}

omit [Finite G] [Fact p.Prime] in
theorem isMulCommutative (hP : InvertedAbelianSylow P τ) :
    IsMulCommutative (P : Subgroup G) :=
  ⟨⟨fun a b => Subtype.ext (hP.comm a a.2 b b.2)⟩⟩

theorem not_mem_centralizer (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ) :
    τ ∉ Subgroup.centralizer (P : Set G) := by
  have hp : p.Prime := Fact.out
  intro hτC
  obtain ⟨-, h3⟩ := card_sylow_odd_three_le_of_relIndex hp2 P hP.index
  have hall : ∀ x ∈ (P : Subgroup G), x = 1 := by
    intro x hx
    have h1 : τ * x * τ⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_iff.mp hτC x hx]
      group
    have hinv : x⁻¹ = x := by rw [← hP.conj_eq_inv x hx, h1]
    exact eq_one_of_inv_eq_self_of_odd
      (odd_orderOf_of_dvd_prime_pow hp hp2 (orderOf_dvd_of_mem_sylow P hx)) hinv
  have h1 : Nat.card (P : Subgroup G) = 1 := by
    rw [Subgroup.card_eq_one]
    exact (Subgroup.eq_bot_iff_forall _).mpr hall
  have h1' : Nat.card P = 1 := h1
  omega

theorem conj_eq_or_inv (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ) {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    (∀ x ∈ (P : Subgroup G), n * x * n⁻¹ = x) ∨ (∀ x ∈ (P : Subgroup G), n * x * n⁻¹ = x⁻¹) := by
  by_cases hnC : n ∈ Subgroup.centralizer (P : Set G)
  · left
    intro x hx
    rw [← Subgroup.mem_centralizer_iff.mp hnC x hx]
    group
  · right
    have hτC := hP.not_mem_centralizer hp2
    have hmul : τ⁻¹ * n ∈ Subgroup.centralizer (P : Set G) := by
      have h2 := Subgroup.mul_mem_iff_of_index_two hP.index
        (a := ⟨τ⁻¹, Subgroup.inv_mem _ hP.mem_normalizer⟩) (b := ⟨n, hn⟩)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h2
      have hτinvC : τ⁻¹ ∉ Subgroup.centralizer (P : Set G) := fun h =>
        hτC (by simpa using Subgroup.inv_mem _ h)
      exact h2.mpr (iff_of_false hτinvC hnC)
    intro x hx
    have hc := Subgroup.mem_centralizer_iff.mp hmul x hx
    calc n * x * n⁻¹ = τ * ((τ⁻¹ * n) * x * (τ⁻¹ * n)⁻¹) * τ⁻¹ := by group
      _ = τ * x * τ⁻¹ := by rw [← hc]; group
      _ = x⁻¹ := hP.conj_eq_inv x hx

theorem eq_or_eq_inv_of_isConj (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ) {x y : G}
    (hx : x ∈ (P : Subgroup G)) (hy : y ∈ (P : Subgroup G)) (hxy : IsConj x y) :
    y = x ∨ y = x⁻¹ := by
  have := hP.isMulCommutative
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hyP : c⁻¹⁻¹ * x * c⁻¹ ∈ P := by
    rw [inv_inv, hc]
    exact hy
  obtain ⟨m, hm, hmeq⟩ := P.conj_eq_normalizer_conj_of_mem x c⁻¹ hx hyP
  rw [inv_inv, hc] at hmeq
  rcases hP.conj_eq_or_inv hp2 (Subgroup.inv_mem _ hm) with h | h
  · left
    have h' := h x hx
    rwa [inv_inv, ← hmeq] at h'
  · right
    have h' := h x hx
    rwa [inv_inv, ← hmeq] at h'

theorem conj_eq_of_mem_normalizer_of_commute (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hgx : Commute g x) :
    ∀ y ∈ (P : Subgroup G), g * y * g⁻¹ = y := by
  have hp : p.Prime := Fact.out
  rcases hP.conj_eq_or_inv hp2 hg with h | h
  · exact h
  · exfalso
    apply hx1
    have hc : g * x * g⁻¹ = x := by rw [hgx.eq, mul_inv_cancel_right]
    refine eq_one_of_inv_eq_self_of_odd
      (odd_orderOf_of_dvd_prime_pow hp hp2 (orderOf_dvd_of_mem_sylow P hx)) ?_
    rw [← h x hx, hc]

omit [Finite G] [Fact p.Prime] in
theorem le_centralizer_zpowers (hP : InvertedAbelianSylow P τ) {x : G}
    (hx : x ∈ (P : Subgroup G)) :
    (P : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact hP.comm _ (Subgroup.zpow_mem _ hx k) z hz

theorem exists_normal_complement_centralizer (hp2 : p ≠ 2) (hP : InvertedAbelianSylow P τ)
    {x : G} (hx : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) :
    ∃ (R : Subgroup (Subgroup.centralizer (Subgroup.zpowers x : Set G))) (_ : R.Normal),
      Nat.Coprime p (Nat.card R) ∧
        IsPGroup p (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⧸ R) := by
  set C := Subgroup.centralizer (Subgroup.zpowers x : Set G) with hC
  have hle : (P : Subgroup G) ≤ C := hP.le_centralizer_zpowers hx
  let S : Sylow p C := P.subtype hle
  have hS : (S : Subgroup C) ≤ CFSG.centerIn (Subgroup.normalizer (S : Subgroup C)) := by
    intro s hs
    refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : (g : G) ∈ Subgroup.normalizer (P : Set G) := by
      have h : g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf C := by
        rw [Subgroup.subgroupOf_normalizer_eq hle]
        exact hg
      rwa [Subgroup.mem_subgroupOf] at h
    have hgx : Commute (g : G) x :=
      ((Subgroup.mem_centralizer_iff.mp g.2 x (Subgroup.mem_zpowers x))).symm
    have hsP : (s : G) ∈ (P : Subgroup G) := by
      have h : s ∈ (P : Subgroup G).subgroupOf C := hs
      rwa [Subgroup.mem_subgroupOf] at h
    have hgs := hP.conj_eq_of_mem_normalizer_of_commute hp2 hx hx1 hg' hgx _ hsP
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g : G) * s = ((g : G) * s * (g : G)⁻¹) * g := by group
      _ = s * g := by rw [hgs]
  exact CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S hS

end InvertedAbelianSylow

end CFSG.CyclicBlocks
