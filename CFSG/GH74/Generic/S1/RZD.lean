module

public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.GH74.Generic.S1

open Subgroup CFSG.GH74.Uniqueness

variable {G : Type} [Group G]

theorem mem_of_orderOf_two_of_odd_relIndex {G₁ M : Subgroup G} (hle : G₁ ≤ M)
    (hn : M ≤ normalizer (G₁ : Set G)) (hodd : Odd (G₁.relIndex M)) {m : G} (hm : m ∈ M)
    (h2 : orderOf m = 2) : m ∈ G₁ := by
  have hnorm : (G₁.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hn
  let q : M →* M ⧸ G₁.subgroupOf M := QuotientGroup.mk' _
  have hcard : Nat.card (M ⧸ G₁.subgroupOf M) = G₁.relIndex M := by
    rw [← Subgroup.index_eq_card]; rfl
  have hord : orderOf (q ⟨m, hm⟩) ∣ 2 := by
    rw [← h2]
    have := orderOf_map_dvd q ⟨m, hm⟩
    rwa [Subgroup.orderOf_mk] at this
  have hodd' : Odd (Nat.card (M ⧸ G₁.subgroupOf M)) := hcard ▸ hodd
  have hdvd : orderOf (q ⟨m, hm⟩) ∣ Nat.card (M ⧸ G₁.subgroupOf M) := orderOf_dvd_natCard _
  have hone : orderOf (q ⟨m, hm⟩) = 1 := by
    have h1 : orderOf (q ⟨m, hm⟩) ∣ 2 := hord
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · exfalso
      rw [h] at hdvd
      exact (Nat.not_even_iff_odd.2 hodd') (even_iff_two_dvd.2 hdvd)
  have : q ⟨m, hm⟩ = 1 := orderOf_eq_one_iff.1 hone
  have hmem : (⟨m, hm⟩ : M) ∈ G₁.subgroupOf M := (QuotientGroup.eq_one_iff _).1 this
  exact hmem

theorem isSolvable_normalizer_sylow [Finite G] (S : Sylow 2 G) :
    Group.IsSolvable (normalizer ((S : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer ((S : Subgroup G) : Set G) with hM
  have hle : (S : Subgroup G) ≤ M := Subgroup.le_normalizer
  have hnorm : ((S : Subgroup G).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 le_rfl
  have hp : IsPGroup 2 ↥((S : Subgroup G).subgroupOf M) :=
    S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hSsolv : Group.IsSolvable ↥((S : Subgroup G).subgroupOf M) := by
    have hnil := hp.isNilpotent
    exact inferInstance
  have hqodd : Odd (Nat.card (M ⧸ (S : Subgroup G).subgroupOf M)) := by
    rw [← Subgroup.index_eq_card]
    have hcard : Nat.card M = ((S : Subgroup G).subgroupOf M).index *
        Nat.card ↥((S : Subgroup G).subgroupOf M) := (Subgroup.index_mul_card _).symm
    have hcardS : Nat.card ↥((S : Subgroup G).subgroupOf M) = Nat.card ↥(S : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcardS, Sylow.card_eq_multiplicity] at hcard
    by_contra hnodd
    have h2 : 2 ∣ ((S : Subgroup G).subgroupOf M).index := by
      rcases Nat.even_or_odd ((S : Subgroup G).subgroupOf M).index with h | h
      · exact even_iff_two_dvd.1 h
      · exact absurd h hnodd
    have hdvd : 2 ^ ((Nat.card G).factorization 2 + 1) ∣ Nat.card M := by
      rw [hcard, pow_succ, mul_comm (2 ^ (Nat.card G).factorization 2) 2]
      rcases h2 with ⟨k, hk⟩
      rw [hk]
      exact ⟨k, by ring⟩
    exact Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := G)).ne' Nat.prime_two
      (hdvd.trans (Subgroup.card_subgroup_dvd_card M))
  have hqsolv : Group.IsSolvable (M ⧸ (S : Subgroup G).subgroupOf M) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hqodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup G).subgroupOf M).subtype
    (QuotientGroup.mk' ((S : Subgroup G).subgroupOf M)) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem eq_top_of_zd
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (G₁ : Subgroup G) (hperf : ⁅G₁, G₁⁆ = G₁) (hne : G₁ ≠ ⊥) (hodd : Odd G₁.index) {x y : G}
    (hxG : x ∈ G₁) (hyG : y ∈ G₁) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : ¬ IsConj x y)
    (hcl : ∀ z ∈ G₁, orderOf z = 2 → ∃ g ∈ G₁, g⁻¹ * z * g = x ∨ g⁻¹ * z * g = y)
    (hCx : centralizer ({x} : Set G) ≤ normalizer (G₁ : Set G))
    (hCy : centralizer ({y} : Set G) ≤ normalizer (G₁ : Set G)) : G₁ = ⊤ := by
  by_contra hG₁top
  set M : Subgroup G := normalizer (G₁ : Set G) with hMdef
  have hle : G₁ ≤ M := Subgroup.le_normalizer
  have hMtop : M ≠ ⊤ := by
    intro hM
    have hnormal : G₁.Normal := Subgroup.normalizer_eq_top_iff.1 hM
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal G₁ with h | h
    · exact hne h
    · exact hG₁top h
  have hrel : Odd (G₁.relIndex M) := by
    have := Subgroup.relIndex_mul_index hle
    rw [← this] at hodd
    exact (Nat.odd_mul.1 hodd).1
  have hinv : ∀ m ∈ M, orderOf m = 2 → m ∈ G₁ := fun m hm h2 =>
    mem_of_orderOf_two_of_odd_relIndex hle le_rfl hrel hm h2
  have hcentral : ∀ z ∈ G₁, orderOf z = 2 → centralizer ({z} : Set G) ≤ M := by
    intro z hz hz2 g hg
    obtain ⟨a, ha, h | h⟩ := hcl z hz hz2
    · have hga : a⁻¹ * g * a ∈ centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        rw [← h]
        calc a⁻¹ * g * a * (a⁻¹ * z * a) = a⁻¹ * (g * z) * a := by group
          _ = a⁻¹ * (z * g) * a := by rw [hg]
          _ = a⁻¹ * z * a * (a⁻¹ * g * a) := by group
      have := hCx hga
      have h2 : g = a * (a⁻¹ * g * a) * a⁻¹ := by group
      rw [h2]
      exact M.mul_mem (M.mul_mem (hle ha) this) (M.inv_mem (hle ha))
    · have hga : a⁻¹ * g * a ∈ centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        rw [← h]
        calc a⁻¹ * g * a * (a⁻¹ * z * a) = a⁻¹ * (g * z) * a := by group
          _ = a⁻¹ * (z * g) * a := by rw [hg]
          _ = a⁻¹ * z * a * (a⁻¹ * g * a) := by group
      have := hCy hga
      have h2 : g = a * (a⁻¹ * g * a) * a⁻¹ := by group
      rw [h2]
      exact M.mul_mem (M.mul_mem (hle ha) this) (M.inv_mem (hle ha))
  let Z : Set G := {z | orderOf z = 2}
  have hconj2 : ∀ z : G, orderOf z = 2 → ∀ g : G, orderOf (g⁻¹ * z * g) = 2 := by
    intro z hz g
    have := (MulAut.conj g⁻¹).orderOf_eq z
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this]
    exact hz
  have hZ : IsInvariantInvolutionSet Z := ⟨fun z hz => hz, fun z hz g => hconj2 z hz g⟩
  have hPD : IsProductDisconnected Z M := by
    refine ⟨hMtop, ⟨x, hx2, hle hxG⟩, ?_, ?_⟩
    · intro z hz hzM g
      constructor
      · intro hgz
        have hzG : z ∈ G₁ := hinv z hzM hz
        have hw2 : orderOf (g⁻¹ * z * g) = 2 := hconj2 z hz g
        have hwG : g⁻¹ * z * g ∈ G₁ := hinv _ hgz hw2
        obtain ⟨a, ha, hza⟩ := hcl z hzG hz
        obtain ⟨b, hb, hwb⟩ := hcl _ hwG hw2
        have key : ∀ {t : G}, a⁻¹ * z * a = t → b⁻¹ * (g⁻¹ * z * g) * b = t →
            centralizer ({t} : Set G) ≤ M → g ∈ M := by
          intro t h1 h2 hC
          have hc : b⁻¹ * g⁻¹ * a ∈ centralizer ({t} : Set G) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            calc b⁻¹ * g⁻¹ * a * t = b⁻¹ * g⁻¹ * a * (a⁻¹ * z * a) := by rw [h1]
              _ = b⁻¹ * (g⁻¹ * z) * a := by group
              _ = (b⁻¹ * (g⁻¹ * z * g) * b) * (b⁻¹ * g⁻¹ * a) := by group
              _ = t * (b⁻¹ * g⁻¹ * a) := by rw [h2]
          have hcM := hC hc
          have : g⁻¹ = b * (b⁻¹ * g⁻¹ * a) * a⁻¹ := by group
          have hginv : g⁻¹ ∈ M := by
            rw [this]
            exact M.mul_mem (M.mul_mem (hle hb) hcM) (M.inv_mem (hle ha))
          simpa using M.inv_mem hginv
        rcases hza with hza | hza <;> rcases hwb with hwb | hwb
        · exact key hza hwb (hcentral x hxG hx2)
        · exfalso
          apply hxy
          rw [isConj_iff]
          refine ⟨b⁻¹ * g⁻¹ * a, ?_⟩
          have hz : z = a * x * a⁻¹ := by rw [← hza]; group
          rw [← hwb, hz]
          group
        · exfalso
          apply hxy
          rw [isConj_iff]
          refine ⟨a⁻¹ * g * b, ?_⟩
          have hz' : g⁻¹ * z * g = b * x * b⁻¹ := by rw [← hwb]; group
          have hz : z = g * (b * x * b⁻¹) * g⁻¹ := by
            rw [← hz']; group
          have hy : y = a⁻¹ * z * a := hza.symm
          rw [hy, hz]
          group
        · exact key hza hwb (hcentral y hyG hy2)
      · intro hg
        exact M.mul_mem (M.mul_mem (M.inv_mem hg) hzM) hg
    · intro u hu huM
      have huG : u ∈ G₁ := hinv u huM hu.1
      exact hcentral u huG hu.1
  obtain ⟨-, S, hS⟩ := S_CorZD_unconditional G inferInstance hnab Z M hZ hPD
  have hsolv : Group.IsSolvable M := hS ▸ isSolvable_normalizer_sylow S
  have hG₁solv : Group.IsSolvable G₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have : Nontrivial G₁ := (Subgroup.nontrivial_iff_ne_bot G₁).2 hne
  have : Group.IsPerfect G₁ := Subgroup.isPerfect_iff.2 hperf
  exact Group.IsPerfect.not_isSolvable G₁ hG₁solv

end CFSG.GH74.Generic.S1
