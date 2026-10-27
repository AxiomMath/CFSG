module

public import CFSG.ClassicalInvolution.Q3.Q3PBranch
public import CFSG.ClassicalInvolution.Q3.Generation

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure IsEdge3 (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  comm : Commutes K₁ K₂
  ne : z₁ ≠ z₂

namespace IsEdge3

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem comm_involutions (h : IsEdge3 Ω K₁ K₂ z₁ z₂) : z₁ * z₂ = z₂ * z₁ :=
  h.comm z₁ h.cls₁.mem z₂ h.cls₂.mem

theorem le_centralizer_right (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₁ ≤ Subgroup.centralizer ({z₂} : Set G) := fun k hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm k hk z₂ h.cls₂.mem)

theorem le_centralizer_left (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₂ ≤ Subgroup.centralizer ({z₁} : Set G) := fun k hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm z₁ h.cls₁.mem k hk).symm

theorem le_centralizer_pair (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₁ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.cls₁.subnormal hk)).symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (h.comm k hk _ h.cls₂.mem).symm

theorem symm (h : IsEdge3 Ω K₁ K₂ z₁ z₂) : IsEdge3 Ω K₂ K₁ z₂ z₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  cls₁ := h.cls₂
  cls₂ := h.cls₁
  comm x hx y hy := (h.comm y hy x hx).symm
  ne := h.ne.symm

theorem le_centralizer_pair' (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₂ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  have := h.symm.le_centralizer_pair
  rwa [Set.pair_comm] at this

end IsEdge3

section Class

variable [Finite G] {K : Subgroup G} {z : G}

theorem conjClass3_involution (hz : IsClassicalMember3 K z) {L : Subgroup G} {w : G}
    (hL : L ∈ conjClass3 K) (hw : IsClassicalMember3 L w) :
    ∃ g : G, L = conjSub g K ∧ w = g * z * g⁻¹ := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨g, rfl, involution_unique3 hw (hz.conj g)⟩

theorem commutes_of_not_a2Configuration3 (hz : IsClassicalMember3 K z)
    (hA2 : ¬ A2Configuration z K) {L M : Subgroup G} {a b : G} (hL : L ∈ conjClass3 K)
    (hM : M ∈ conjClass3 K) (ha : IsClassicalMember3 L a) (hb : IsClassicalMember3 M b)
    (hab : a ≠ b) (hc : a * b = b * a) : Commutes L M := by
  obtain ⟨g, rfl, rfl⟩ := conjClass3_involution hz hL ha
  obtain ⟨h, rfl, rfl⟩ := conjClass3_involution hz hM hb
  by_contra hn
  apply hA2
  refine ⟨g⁻¹, h⁻¹, ?_, ?_, ?_, ?_⟩
  · intro heq
    apply hab
    have hz1 := hz.conj g
    have hz2 : IsClassicalMember3 (conjSub g K) (h * z * h⁻¹) := by
      have : conjSub g K = conjSub h K := by simpa [conjSub] using heq
      rw [this]
      exact hz.conj h
    exact involution_unique3 hz1 hz2
  · simpa using hab
  · simpa using hc
  · simpa [conjSub] using hn

theorem exists_edge3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) :
    ∃ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ B : Subgroup G, Relation.ReflTransGen (commutingAdj K) K B →
      ∀ y : G, IsClassicalMember3 B y → y = z := by
    intro B hB
    induction hB with
    | refl => exact fun y hy => involution_unique3 hy hz
    | @tail B C _ hBC ih =>
      intro y hy
      obtain ⟨hBmem, hCmem, hne, hcomm⟩ := hBC
      obtain ⟨g, hg⟩ := hBmem
      obtain ⟨h, hh⟩ := hCmem
      have hBcls : IsClassicalMember3 B (g⁻¹ * z * g⁻¹⁻¹) := by
        rw [hg]
        simpa [conjSub] using hz.conj g⁻¹
      have hCcls : IsClassicalMember3 C (h⁻¹ * z * h⁻¹⁻¹) := by
        rw [hh]
        simpa [conjSub] using hz.conj h⁻¹
      have hBz := ih _ hBcls
      by_contra hyz
      have hCy : y = h⁻¹ * z * h⁻¹⁻¹ := involution_unique3 hy hCcls
      have hne' : g⁻¹ * z * g⁻¹⁻¹ ≠ y := by
        intro e
        apply hyz
        rw [← e, hBz]
      refine hcon B C (g⁻¹ * z * g⁻¹⁻¹) y ⟨?_, ?_, hBcls, hy, hcomm, hne'⟩
      · exact ⟨g⁻¹, by rw [hg]; rfl⟩
      · exact ⟨h⁻¹, by rw [hh]; rfl⟩
  have hall : ∀ g : G, g * z * g⁻¹ = z := by
    intro g
    have hmem : conjSub g K ∈ conjugateSet K := ⟨g⁻¹, by simp [conjSub]⟩
    have hK : K ∈ conjugateSet K := ⟨1, by rw [inv_one]; exact (conjSub_one K).symm⟩
    exact (key _ (hΔ K hK _ hmem) _ (hz.conj g))
  have hcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hall g
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [this]
  exact Balance.not_subset_center_of_ne_one hnab hz.ne_one (Set.singleton_subset_iff.mpr hcen)

end Class

end CFSG.ClassicalInvolution.Q3
