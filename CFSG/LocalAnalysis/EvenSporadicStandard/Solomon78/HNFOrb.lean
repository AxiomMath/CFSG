module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHPrim

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

@[expose] def conjOrb (H : Subgroup G) (x : G) : Set G := {y | ∃ h ∈ H, h * x * h⁻¹ = y}

theorem mem_conjOrb_self (H : Subgroup G) (x : G) : x ∈ conjOrb H x :=
  ⟨1, one_mem _, by simp⟩

theorem conjOrb_mono {H H' : Subgroup G} (h : H ≤ H') (x : G) : conjOrb H x ⊆ conjOrb H' x :=
  fun _ ⟨k, hk, e⟩ => ⟨k, h hk, e⟩

theorem ncard_conjOrb_mul (H : Subgroup G) (x : G) :
    (conjOrb H x).ncard * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) = Nat.card H :=
  ncard_conj_orbit_mul_card_inf_centralizer H x

theorem conj_mem_conjOrb {H : Subgroup G} {x y : G} (hy : y ∈ conjOrb H x) {h : G} (hh : h ∈ H) :
    h * y * h⁻¹ ∈ conjOrb H x := by
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨h * k, mul_mem hh hk, by simp [mul_assoc]⟩

theorem conjOrb_subset_of_mem {H : Subgroup G} {x y : G} (hy : y ∈ conjOrb H x) :
    conjOrb H y ⊆ conjOrb H x := by
  rintro _ ⟨h, hh, rfl⟩
  exact conj_mem_conjOrb hy hh

theorem mem_conjOrb_symm {H : Subgroup G} {x y : G} (hy : y ∈ conjOrb H x) :
    x ∈ conjOrb H y := by
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨k⁻¹, inv_mem hk, by simp [mul_assoc]⟩

theorem conjOrb_eq_of_mem {H : Subgroup G} {x y : G} (hy : y ∈ conjOrb H x) :
    conjOrb H y = conjOrb H x :=
  Set.Subset.antisymm (conjOrb_subset_of_mem hy) (conjOrb_subset_of_mem (mem_conjOrb_symm hy))

theorem disjoint_conjOrb_of_not_mem {H : Subgroup G} {x y : G} (hy : y ∉ conjOrb H x) :
    Disjoint (conjOrb H x) (conjOrb H y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  apply hy
  have h1 := conjOrb_eq_of_mem hzx
  have h2 := conjOrb_eq_of_mem hzy
  have h3 : conjOrb H x = conjOrb H y := h1.symm.trans h2
  rw [h3]
  exact mem_conjOrb_self H y

@[expose] def conjSet (x : G) (S : Set G) : Set G := (fun y => x * y * x⁻¹) '' S

theorem ncard_conjSet (x : G) (S : Set G) : (conjSet x S).ncard = S.ncard :=
  Set.ncard_image_of_injective _ fun a b h => by simpa using h

section IndexTwo

variable {C K : Subgroup G}

theorem exists_mem_not_mem_of_index_two (hidx : (K.subgroupOf C).index = 2) :
    ∃ x ∈ C, x ∉ K := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  refine ⟨(a : G), a.2, fun h => ?_⟩
  have h1 := ha 1
  have h2 : a ∈ K.subgroupOf C := mem_subgroupOf.2 h
  simp only [one_mul] at h1
  rcases h1 with ⟨_, h3⟩ | ⟨_, h3⟩
  · exact absurd (one_mem _) h3
  · exact h3 h2

theorem mem_of_not_mem_of_not_mem (hidx : (K.subgroupOf C).index = 2) {x c : G} (hx : x ∈ C)
    (hc : c ∈ C) (hxK : x ∉ K) (hcK : c ∉ K) : x⁻¹ * c ∈ K := by
  have h := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x⁻¹, inv_mem hx⟩ : ↥C))
    (b := (⟨c, hc⟩ : ↥C))
  have hx' : (⟨x⁻¹, inv_mem hx⟩ : ↥C) ∉ K.subgroupOf C := fun h' => hxK (by
    have := mem_subgroupOf.1 h'
    simpa using inv_mem this)
  have hc' : (⟨c, hc⟩ : ↥C) ∉ K.subgroupOf C := fun h' => hcK (mem_subgroupOf.1 h')
  have : (⟨x⁻¹, inv_mem hx⟩ * ⟨c, hc⟩ : ↥C) ∈ K.subgroupOf C :=
    h.2 (iff_of_false hx' hc')
  exact mem_subgroupOf.1 this

theorem conj_mem_of_normal (hidx : (K.subgroupOf C).index = 2) {x k : G} (hx : x ∈ C) (hk : k ∈ K)
    (hKC : K ≤ C) : x * k * x⁻¹ ∈ K := by
  have : (K.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have := (inferInstance : (K.subgroupOf C).Normal).conj_mem ⟨k, hKC hk⟩
    (mem_subgroupOf.2 hk) ⟨x, hx⟩
  exact mem_subgroupOf.1 this

theorem ncard_kinvariant_subset [Finite G] (hKC : K ≤ C) (hidx : (K.subgroupOf C).index = 2)
    {β : G} {S : Set G} (hS : S ⊆ conjOrb C β)
    (hinv : ∀ k ∈ K, ∀ y ∈ S, k * y * k⁻¹ ∈ S) :
    S.ncard = 0 ∨ S.ncard + S.ncard = (conjOrb C β).ncard ∨ S.ncard = (conjOrb C β).ncard := by
  obtain ⟨x, hxC, hxK⟩ := exists_mem_not_mem_of_index_two hidx
  have hx2 : x * x ∈ K := by
    have h := Subgroup.mul_self_mem_of_index_two hidx (⟨x, hxC⟩ : ↥C)
    exact mem_subgroupOf.1 h
  set S' : Set G := conjSet x S with hS'
  have hS'inv : ∀ k ∈ K, ∀ y ∈ S', k * y * k⁻¹ ∈ S' := by
    rintro k hk _ ⟨s, hs, rfl⟩
    have hk' : x⁻¹ * k * x ∈ K := by
      have := conj_mem_of_normal hidx (inv_mem hxC) hk hKC
      simpa using this
    exact ⟨(x⁻¹ * k * x) * s * (x⁻¹ * k * x)⁻¹, hinv _ hk' _ hs, by simp [mul_assoc]⟩
  have hL1 : ∀ c ∈ C, ∀ y ∈ S, (c ∈ K → c * y * c⁻¹ ∈ S) ∧ (c ∉ K → c * y * c⁻¹ ∈ S') := by
    intro c hc y hy
    refine ⟨fun h => hinv _ h _ hy, fun hcK => ?_⟩
    have h := mem_of_not_mem_of_not_mem hidx hxC hc hxK hcK
    exact ⟨(x⁻¹ * c) * y * (x⁻¹ * c)⁻¹, hinv _ h _ hy, by simp [mul_assoc]⟩
  have hL2 : ∀ c ∈ C, ∀ y ∈ S', (c ∈ K → c * y * c⁻¹ ∈ S') ∧ (c ∉ K → c * y * c⁻¹ ∈ S) := by
    intro c hc y hy
    refine ⟨fun h => hS'inv _ h _ hy, fun hcK => ?_⟩
    have h := mem_of_not_mem_of_not_mem hidx hxC hc hxK hcK
    obtain ⟨s, hs, hse⟩ := hS'inv _ h _ hy
    have h2 := hinv _ hx2 _ hs
    have e : c * y * c⁻¹ = (x * x) * s * (x * x)⁻¹ := by
      have hc' : c = x * (x⁻¹ * c) := by simp
      have hy2 : (x⁻¹ * c) * y * (x⁻¹ * c)⁻¹ = x * s * x⁻¹ := hse.symm
      calc c * y * c⁻¹ = x * ((x⁻¹ * c) * y * (x⁻¹ * c)⁻¹) * x⁻¹ := by
            conv_lhs => rw [hc']
            simp [mul_assoc]
        _ = (x * x) * s * (x * x)⁻¹ := by rw [hy2]; simp [mul_assoc]
    rw [e]
    exact h2
  have hΓ : ∀ T : Set G, T ⊆ conjOrb C β → (∀ c ∈ C, ∀ y ∈ T, c * y * c⁻¹ ∈ T) → T.Nonempty →
      T = conjOrb C β := by
    intro T hT hinvT hne
    refine Set.Subset.antisymm hT ?_
    obtain ⟨t, ht⟩ := hne
    obtain ⟨c₀, hc₀, rfl⟩ := hT ht
    rintro _ ⟨c, hc, rfl⟩
    have h1 := hinvT c₀⁻¹ (inv_mem hc₀) _ ht
    have h2 : c₀⁻¹ * (c₀ * β * c₀⁻¹) * c₀⁻¹⁻¹ = β := by simp [mul_assoc]
    rw [h2] at h1
    exact hinvT c hc _ h1
  have hS'sub : S' ⊆ conjOrb C β := by
    rintro _ ⟨s, hs, rfl⟩
    exact conj_mem_conjOrb (hS hs) hxC
  by_cases hne : S.Nonempty
  · right
    have hU : S ∪ S' = conjOrb C β := by
      refine hΓ _ (Set.union_subset hS hS'sub) ?_ (hne.mono Set.subset_union_left)
      intro c hc y hy
      by_cases hcK : c ∈ K
      · rcases hy with hy | hy
        · exact Or.inl ((hL1 c hc y hy).1 hcK)
        · exact Or.inr ((hL2 c hc y hy).1 hcK)
      · rcases hy with hy | hy
        · exact Or.inr ((hL1 c hc y hy).2 hcK)
        · exact Or.inl ((hL2 c hc y hy).2 hcK)
    by_cases hI : (S ∩ S').Nonempty
    · right
      have hI' : S ∩ S' = conjOrb C β := by
        refine hΓ _ (Set.inter_subset_left.trans hS) ?_ hI
        rintro c hc y ⟨hy1, hy2⟩
        by_cases hcK : c ∈ K
        · exact ⟨(hL1 c hc y hy1).1 hcK, (hL2 c hc y hy2).1 hcK⟩
        · exact ⟨(hL2 c hc y hy2).2 hcK, (hL1 c hc y hy1).2 hcK⟩
      have : S = conjOrb C β := Set.Subset.antisymm hS (hI'.symm.subset.trans Set.inter_subset_left)
      rw [this]
    · left
      have hd : Disjoint S S' :=
        Set.not_nonempty_iff_eq_empty.1 hI |> Set.disjoint_iff_inter_eq_empty.2
      have h1 := Set.ncard_union_eq hd
      rw [hU, ncard_conjSet] at h1
      exact h1.symm
  · left
    rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

end IndexTwo

end CFSG.EvenSporadicStandard.Solomon78
