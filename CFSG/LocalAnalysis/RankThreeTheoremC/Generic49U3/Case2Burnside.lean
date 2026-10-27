module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem burnside_normalizer_le_centralizer {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y) (hQc : IsCyclic (Q : Subgroup Y)) {x : Y}
    (hxQ : x ∈ (Q : Subgroup Y)) (hxo : orderOf x = p) (hxc : ∀ y : Y, y * x = x * y) :
    Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y) := by
  haveI := hQc
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  set Qs : Subgroup Y := (Q : Subgroup Y) with hQs
  set φ : Subgroup.normalizer (Qs : Set Y) →* MulAut Qs := Qs.normalizerMonoidHom with hφ
  set s : ℕ := φ.ker.index with hs
  have hQN : Qs ≤ Subgroup.normalizer (Qs : Set Y) := Subgroup.le_normalizer
  have hle : Qs.subgroupOf (Subgroup.normalizer (Qs : Set Y)) ≤ φ.ker := by
    intro n hn
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Subgroup.le_centralizer Qs hn
  have hcop : Nat.Coprime p s := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    apply Q.not_dvd_index
    refine hdvd.trans ?_
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    exact Subgroup.relIndex_dvd_index_of_le hQN
  have hgD : ∀ d ∈ Qs, g * d * g⁻¹ ∈ Qs := fun d hd => ((Subgroup.mem_normalizer_iff.mp hg) d).mp hd
  have hgx : g * x * g⁻¹ = x := by rw [hxc g, mul_assoc, mul_inv_cancel, mul_one]
  have hDp : ∀ d ∈ Qs, ∃ k : ℕ, d ^ (p ^ k) = 1 := by
    intro d hd
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨d, hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hgs : ∀ d ∈ Qs, (g ^ s) * d * (g ^ s)⁻¹ = d := by
    intro d hd
    have h1 : (⟨g, hg⟩ : Subgroup.normalizer (Qs : Set Y)) ^ s ∈ φ.ker := Subgroup.pow_index_mem _ _
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    have h2 := h1 d hd
    simp only [Subgroup.coe_pow] at h2
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  have key := cyclic_coprime_aut_trivial hp (D := Qs) hDp hxQ hxo hgD hgx hcop hgs
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have := key d hd
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

private theorem burnside_exists_complement {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y)
    (hQ : Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤
      Subgroup.centralizer ((Q : Subgroup Y) : Set Y)) :
    ∃ N : Subgroup Y, (∀ n ∈ N, Nat.Coprime p (orderOf n)) ∧
      (∀ y : Y, Nat.Coprime p (orderOf y) → y ∈ N) ∧
      (∀ y : Y, ∃ n ∈ N, ∃ d ∈ (Q : Subgroup Y), y = n * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨(MonoidHom.transferSylow Q hQ).ker, ?_, ?_, ?_⟩
  · intro n hn
    have h1 : orderOf n ∣ Nat.card (MonoidHom.transferSylow Q hQ).ker := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : (MonoidHom.transferSylow Q hQ).ker)
      simpa using this
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow Q hQ)).coprime_dvd_right h1
  · intro y hy
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := Q.isPGroup' (MonoidHom.transferSylow Q hQ y)
    have h2 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ orderOf y := orderOf_map_dvd _ y
    have h4 : Nat.Coprime (p ^ k) (orderOf y) := Nat.Coprime.pow_left k hy
    have h5 : orderOf (MonoidHom.transferSylow Q hQ y) = 1 := Nat.eq_one_of_dvd_coprimes h4 h2 h3
    exact orderOf_eq_one_iff.mp h5
  · intro y
    have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hQ
    obtain ⟨⟨a, d⟩, h, -⟩ := hcomp.existsUnique y
    exact ⟨a.1, a.2, d.1, d.2, h.symm⟩

theorem u3_K0_pComplement_core {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J)) (hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J)
    (hxo' : orderOf x = p) :
    ∃ N₀ : Subgroup G, N₀ ≤ u3K0 p x J ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀) ∧
      (∀ n ∈ N₀, Nat.Coprime p (orderOf n)) ∧
      ∀ k ∈ u3K0 p x J, ∃ n ∈ N₀, ∃ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, k = n * d := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm := u3K0_conj_gen hc
  have hK₀C : u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) := fun k hk => hk.1
  have hK₀N : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer ((u3K0 p x J : Subgroup G) : Set G) := by
    intro c hcC
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hnorm c hcC k hk
    · intro hk
      have := hnorm c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hcC) _ hk
      simpa [mul_assoc] using this
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G)) := hc.generic.2.2.1
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ u3K0 p x J) (u3K0 p x J) := by
    have := hsyl.inf_of_le_normalizer hK₀C hK₀N
    rwa [inf_assoc, inf_eq_right.mpr hK₀C] at this
  obtain ⟨Q, hQ⟩ := hsyl'.exists_sylow_eq_subgroupOf
  have hxK : x ∈ u3K0 p x J := hxD.2
  have hQc : IsCyclic (Q : Subgroup (u3K0 p x J)) := by
    have hcyc := hDcyc
    rw [hQ]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe (inf_le_right : (P : Subgroup G) ⊓ u3K0 p x J ≤ u3K0 p x J))).mpr hcyc
  have hxQ : (⟨x, hxK⟩ : u3K0 p x J) ∈ (Q : Subgroup (u3K0 p x J)) := by
    rw [hQ, Subgroup.mem_subgroupOf]
    exact hxD
  have hxo : orderOf (⟨x, hxK⟩ : u3K0 p x J) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxo'
  have hxc : ∀ y : u3K0 p x J, y * ⟨x, hxK⟩ = ⟨x, hxK⟩ * y := by
    intro y
    apply Subtype.ext
    exact (y.2.1 x (Set.mem_singleton x)).symm
  have hQN := burnside_normalizer_le_centralizer hp Q hQc hxQ hxo hxc
  obtain ⟨N, hN1, hN2, hN3⟩ := burnside_exists_complement hp Q hQN
  refine ⟨N.map (u3K0 p x J).subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · intro c hcC n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have hmem : c * (n' : G) * c⁻¹ ∈ u3K0 p x J := hnorm c hcC n' n'.2
    have hm : (⟨c * (n' : G) * c⁻¹, hmem⟩ : u3K0 p x J) ∈ N := by
      apply hN2
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (c * (n' : G) * c⁻¹) = orderOf (n' : G) := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective (n' : G)
        simpa using this
      rw [h1, Subgroup.orderOf_coe]
      exact hN1 n' hn'
    exact ⟨_, hm, rfl⟩
  · rintro n ⟨n', hn', rfl⟩
    have := hN1 n' hn'
    rwa [← Subgroup.orderOf_coe] at this
  · intro k hk
    obtain ⟨n', hn', d', hd', hkd⟩ := hN3 ⟨k, hk⟩
    rw [hQ, Subgroup.mem_subgroupOf] at hd'
    exact ⟨n', ⟨n', hn', rfl⟩, d', hd', congrArg Subtype.val hkd⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
