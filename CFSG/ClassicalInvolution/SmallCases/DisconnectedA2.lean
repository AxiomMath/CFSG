module

public import CFSG.Adapters.Involutions
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedControl

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def UniqueInvolutionNormal (K : Subgroup G) (z : G) : Prop :=
  orderOf z = 2 ∧ z ∈ K ∧ (∀ t ∈ K, orderOf t = 2 → t = z) ∧
    K ≤ Subgroup.centralizer ({z} : Set G) ∧
    (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal

@[expose] def SingleMemberControl (K : Subgroup G) : Prop :=
  ∀ t : G, t ≠ 1 → IsPGroup 2 (Subgroup.zpowers t) →
    ∀ A ∈ conjugateSet K, ∀ B ∈ conjugateSet K,
      A ≤ Subgroup.centralizer ({t} : Set G) → B ≤ Subgroup.centralizer ({t} : Set G) → A = B

theorem isPGroup_two_zpowers_of_orderOf_two {H : Type} [Group H] {b : H}
    (hb : orderOf b = 2) : IsPGroup 2 (Subgroup.zpowers b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)

theorem mem_normalizer_of_mem_centralizer_of_normal {K : Subgroup G} {z : G}
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal) {s : G}
    (hs : s ∈ Subgroup.centralizer ({z} : Set G)) : s ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ t ∈ Subgroup.centralizer ({z} : Set G), ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro t ht k hk
    have h := hKn.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨t, ht⟩
    exact Subgroup.mem_subgroupOf.mp h
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact key s hs k
  · intro hk
    have := key s⁻¹ (inv_mem hs) _ hk
    simpa [mul_assoc] using this

section ZStar

variable [Finite G]

theorem exists_conj_mem_sylow_ne (hodd : CFSG.oddCore G = ⊥) (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz : orderOf z = 2)
    (hnc : (z : G) ∉ Subgroup.center G) :
    ∃ g : G, g * (z : G) * g⁻¹ ∈ (S : Subgroup G) ∧ g * (z : G) * g⁻¹ ≠ (z : G) := by
  by_contra hne
  push Not at hne
  have hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z := by
    intro g hg
    have := hne g⁻¹
    rw [inv_inv] at this
    exact this hg
  obtain ⟨hfrat, -⟩ := CFSG.Adapters.glauberman_zStar S z hzZ hz hwc
  apply hnc
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, hc, k, hk, hgk⟩ := hfrat g
  rw [hodd, Subgroup.mem_bot] at hk
  subst hk
  rw [mul_one] at hgk
  subst hgk
  exact Subgroup.mem_centralizer_singleton_iff.mp hc

end ZStar

section Pair

variable {K : Subgroup G} {z : G}

theorem UniqueInvolutionNormal.conj_unique (hK : UniqueInvolutionNormal K z) (g : G) :
    ∀ t ∈ conjSubgroup g K, orderOf t = 2 → t = g * z * g⁻¹ := by
  intro t ht ho
  have h1 : g⁻¹ * t * g ∈ K := mem_conjSubgroup_iff.mp ht
  have h2 : orderOf (g⁻¹ * t * g) = 2 := by
    have := (MulAut.conj g⁻¹).orderOf_eq t
    simpa [MulAut.conj_apply, ho] using this
  have h3 := hK.2.2.1 _ h1 h2
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [h3]

theorem UniqueInvolutionNormal.conj_le_centralizer (hK : UniqueInvolutionNormal K z) (g : G) :
    conjSubgroup g K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  intro x hx
  have h1 : g⁻¹ * x * g ∈ K := mem_conjSubgroup_iff.mp hx
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hK.2.2.2.1 h1)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
    _ = g * z * g⁻¹ * x := by group

theorem mem_centralizer_conj_iff (g k : G) :
    k ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ↔
      g⁻¹ * k * g ∈ Subgroup.centralizer ({z} : Set G) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * k * g * z = g⁻¹ * (k * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * k) * g := by rw [h]
      _ = z * (g⁻¹ * k * g) := by group
  · intro h
    calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * k := by group

theorem a2_pair_of_tight (hK : UniqueInvolutionNormal K z) (hT : SingleMemberControl K)
    {S : Subgroup G} (hzS : z ∈ S) (hSC : S ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (hgS : g * z * g⁻¹ ∈ S) (hgz : g * z * g⁻¹ ≠ z) :
    conjSubgroup g K ≠ K ∧ g * z * g⁻¹ ∈ Subgroup.normalizer (K : Set G) ∧
      ¬ K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ∧
      z ∈ Subgroup.normalizer (conjSubgroup g K : Set G) ∧
      ¬ conjSubgroup g K ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∀ k ∈ K, k ∈ Subgroup.normalizer (conjSubgroup g K : Set G) ↔
        k ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  obtain ⟨hzo, hzK, huniq, hKC, hKn⟩ := hK
  have hK' : UniqueInvolutionNormal K z := ⟨hzo, hzK, huniq, hKC, hKn⟩
  set z' := g * z * g⁻¹ with hz'
  have hz'o : orderOf z' = 2 := by
    have := (MulAut.conj g).orderOf_eq z
    simpa [MulAut.conj_apply, hz', hzo] using this
  have hz'C : z' ∈ Subgroup.centralizer ({z} : Set G) := hSC hgS
  have hne : conjSubgroup g K ≠ K := by
    intro h
    have : z' ∈ K := by
      rw [← h]
      exact mem_conjSubgroup_of_mem hzK
    exact hgz (huniq _ this hz'o)
  have hz'N : z' ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_mem_centralizer_of_normal hKC hKn hz'C
  have hzz' : z * z' = z' * z := (Subgroup.mem_centralizer_singleton_iff.mp hz'C).symm
  have hinvC : g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * z = g⁻¹ * (z * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * z) * g := by rw [hzz']
      _ = z * (g⁻¹ * z * g) := by group
  have hzN : z ∈ Subgroup.normalizer (conjSubgroup g K : Set G) :=
    mem_normalizer_conjSubgroup_iff.mpr
      (mem_normalizer_of_mem_centralizer_of_normal hKC hKn hinvC)
  have hK2 : K ∈ conjugateSet K := self_mem_conjugateSet K
  have hK'2 : conjSubgroup g K ∈ conjugateSet K := conjSubgroup_mem_conjugateSet g hK2
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hzo
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h] at hz'o
    simp at hz'o
  refine ⟨hne, hz'N, ?_, hzN, ?_, ?_⟩
  · intro hKz'
    exact hne (hT z' hz'1 (isPGroup_two_zpowers_of_orderOf_two hz'o) _ hK'2 _ hK2
      (hK'.conj_le_centralizer g) hKz')
  · intro hKz
    exact hne (hT z hz1 (isPGroup_two_zpowers_of_orderOf_two hzo) _ hK'2 _ hK2 hKz hKC)
  · intro k hk
    constructor
    · intro hkN
      have hz'K' : z' ∈ conjSubgroup g K := mem_conjSubgroup_of_mem hzK
      have h1 : k * z' * k⁻¹ ∈ conjSubgroup g K := by
        have := (Subgroup.mem_normalizer_iff.mp hkN z').mp hz'K'
        exact this
      have h2 : orderOf (k * z' * k⁻¹) = 2 := by
        have := (MulAut.conj k).orderOf_eq z'
        simpa [MulAut.conj_apply, hz'o] using this
      have h3 := hK'.conj_unique g _ h1 h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * z' = (k * z' * k⁻¹) * k := by group
        _ = z' * k := by rw [h3]
    · intro hkC
      exact mem_normalizer_conjSubgroup_iff.mpr
        (mem_normalizer_of_mem_centralizer_of_normal hKC hKn
          ((mem_centralizer_conj_iff g k).mp hkC))

end Pair

section Existence

variable [Finite G] {K : Subgroup G} {z : G}

theorem exists_a2_pair (hodd : CFSG.oddCore G = ⊥) (hK : UniqueInvolutionNormal K z)
    (hT : SingleMemberControl K) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hnc : z ∉ Subgroup.center G) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z ∧
      conjSubgroup g K ≠ K ∧ g * z * g⁻¹ ∈ Subgroup.normalizer (K : Set G) ∧
      ¬ K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ∧
      z ∈ Subgroup.normalizer (conjSubgroup g K : Set G) ∧
      ¬ conjSubgroup g K ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∀ k ∈ K, k ∈ Subgroup.normalizer (conjSubgroup g K : Set G) ↔
        k ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  have hzc : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSC s.2)
  have hzo : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hK.1
  obtain ⟨g, hgS, hgz⟩ := exists_conj_mem_sylow_ne hodd S ⟨z, hzS⟩ hzc hzo hnc
  exact ⟨g, hgS, hgz, a2_pair_of_tight hK hT hzS hSC hgS hgz⟩

theorem a2Configuration_of_tight (hodd : CFSG.oddCore G = ⊥) (hK : UniqueInvolutionNormal K z)
    (hT : SingleMemberControl K) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hnc : z ∉ Subgroup.center G) : A2Configuration z K := by
  obtain ⟨g, hgS, hgz, hne, -, hKz', -, -, -⟩ := exists_a2_pair hodd hK hT S hzS hSC hnc
  have hzz' : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hSC hgS)
  refine ⟨1, g⁻¹, ?_, ?_, ?_, ?_⟩
  · change conjSubgroup (1 : G)⁻¹ K ≠ conjSubgroup (g⁻¹)⁻¹ K
    rw [inv_one, inv_inv, conjSubgroup_one]
    exact fun h => hne h.symm
  · simpa using hgz.symm
  · simpa using hzz'.symm
  · intro hc
    apply hKz'
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz'K' : g * z * g⁻¹ ∈ K.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom := by
      rw [inv_inv]
      exact mem_conjSubgroup_of_mem hK.2.1
    have hx' : x ∈ K.map (MulAut.conj (1 : G)⁻¹).toMonoidHom := by
      change x ∈ conjSubgroup (1 : G)⁻¹ K
      rw [inv_one, conjSubgroup_one]
      exact hx
    exact hc x hx' _ hz'K'

end Existence

end CFSG.ClassicalInvolution
