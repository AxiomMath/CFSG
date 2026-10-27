module

public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

abbrev UinS (Ω : Set (Subgroup G)) (S : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ USet Ω ∧ U ≤ S}

theorem UinS.conj (hΩ : ConjInvariant Ω) {S U : Subgroup G} (hU : U ∈ UinS Ω S) {g : G}
    (hg : g ∈ S) : conjSub g U ∈ UinS Ω S := by
  refine ⟨USet.conj hΩ hU.1 g, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : g⁻¹ * x * g ∈ S := hU.2 hx
  have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [h2]
  exact S.mul_mem (S.mul_mem hg h1) (S.inv_mem hg)

theorem inDistinctMembers_image_conj (hΩ : ConjInvariant Ω) {η : Set (Subgroup G)}
    (h : InDistinctMembers Ω η) (g : G) : InDistinctMembers Ω (conjSub g '' η) := by
  rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne J hJ ⟨h1, h2⟩
  have hne' : U ≠ U' := fun h' => hne (by rw [h'])
  refine h U hU U' hU' hne' (conjSub g⁻¹ J) (hΩ g⁻¹ J hJ) ⟨?_, ?_⟩
  · exact (conjSub_le_iff g).mp h1
  · exact (conjSub_le_iff g).mp h2

omit [Fact p.Prime] in
theorem ncard_le_of_mem_etaSet_conj (hΩ : ConjInvariant Ω) {S₁ S₂ : Subgroup G} {g : G}
    (hg : conjSub g S₁ = S₂) {η η' : Set (Subgroup G)} (h : η ∈ etaSet Ω S₁)
    (hη' : η' ⊆ UinS Ω S₂) (hd : InDistinctMembers Ω η') : η'.ncard ≤ η.ncard := by
  have hsub : conjSub g⁻¹ '' η' ⊆ UinS Ω S₁ := by
    rintro _ ⟨U, hU, rfl⟩
    refine ⟨USet.conj hΩ (hη' hU).1 g⁻¹, ?_⟩
    have := conjSub_mono (n := g⁻¹) (hη' hU).2
    rwa [← hg, conjSub_inv_conjSub] at this
  have h1 := h.2.2 _ hsub (inDistinctMembers_image_conj hΩ hd g⁻¹)
  rwa [Set.ncard_image_of_injective _ (conjSub_injective g⁻¹)] at h1

section Finite

variable [Finite G]

theorem exists_conjSub_eq_of_sylow (S₁ S₂ : Sylow 2 G) :
    ∃ g : G, conjSub g (S₁ : Subgroup G) = (S₂ : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S₂
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext x
  simp [conjSub, Subgroup.pointwise_smul_def]

theorem mem_etaSet_of_le (hΩ : ConjInvariant Ω) {S₁ S₂ : Sylow 2 G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω (S₁ : Subgroup G)) (hsub : ∀ V ∈ η, V ≤ (S₂ : Subgroup G)) :
    η ∈ etaSet Ω (S₂ : Subgroup G) := by
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S₂
  refine ⟨fun V hV => ⟨(h.1 hV).1, hsub V hV⟩, h.2.1, fun η' hη' hd => ?_⟩
  exact ncard_le_of_mem_etaSet_conj hΩ hg h hη' hd

variable (hp : p ≠ 2)

include hp in
theorem exists_mem_of_mem_etaSet (hΩ : HypOmegaMod p f Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) {K : Subgroup G} (hK : K ∈ Ω) {U : Subgroup G} (hU : U ∈ UinS Ω S)
    (hUK : U ≤ K) : ∃ V ∈ η, V ≤ K := by
  by_contra hno
  push Not at hno
  have hUη : U ∉ η := fun hh => hno U hh hUK
  have hsub' : insert U η ⊆ UinS Ω S := Set.insert_subset hU h.1
  have hd' : InDistinctMembers Ω (insert U η) := by
    intro V₁ hV₁ V₂ hV₂ hne J hJ hVJ
    rcases hV₁ with rfl | hV₁ <;> rcases hV₂ with rfl | hV₂
    · exact hne rfl
    · have hJK : J = K := hΩ.eq_of_mem_USet hp hU.1 hJ hK hVJ.1 hUK
      exact hno V₂ hV₂ (hJK ▸ hVJ.2)
    · have hJK : J = K := hΩ.eq_of_mem_USet hp hU.1 hJ hK hVJ.2 hUK
      exact hno V₁ hV₁ (hJK ▸ hVJ.1)
    · exact h.2.1 V₁ hV₁ V₂ hV₂ hne J hJ hVJ
  have hcard : (insert U η).ncard = η.ncard + 1 :=
    Set.ncard_insert_of_notMem hUη (Set.toFinite η)
  have := h.2.2 (insert U η) hsub' hd'
  omega

include hp in
theorem mem_etaSet_of_cover (hΩ : HypOmegaMod p f Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (hsub : η ⊆ UinS Ω S) (hd : InDistinctMembers Ω η)
    (hcov : ∀ K ∈ Ω, (∃ U ∈ UinS Ω S, U ≤ K) → ∃ V ∈ η, V ≤ K) : η ∈ etaSet Ω S := by
  classical
  refine ⟨hsub, hd, fun η' hη' hd' => ?_⟩
  have hex : ∀ U' ∈ η', ∃ V ∈ η, ∃ K ∈ Ω, U' ≤ K ∧ V ≤ K := by
    intro U' hU'
    obtain ⟨K, hK, hU'K⟩ := hΩ.exists_member_of_mem_USet hp (hη' hU').1
    obtain ⟨V, hV, hVK⟩ := hcov K hK ⟨U', hη' hU', hU'K⟩
    exact ⟨V, hV, K, hK, hU'K, hVK⟩
  choose! g hgη hgK using hex
  refine Set.ncard_le_ncard_of_injOn g hgη ?_ (Set.toFinite η)
  intro U₁ h₁ U₂ h₂ heq
  by_contra hne
  obtain ⟨K₁, hK₁, hU₁K₁, hgK₁⟩ := hgK U₁ h₁
  obtain ⟨K₂, hK₂, hU₂K₂, hgK₂⟩ := hgK U₂ h₂
  have hV : g U₁ ∈ USet Ω := (hsub (hgη U₁ h₁)).1
  have hK12 : K₁ = K₂ := hΩ.eq_of_mem_USet hp hV hK₁ hK₂ hgK₁ (heq ▸ hgK₂)
  exact hd' U₁ h₁ U₂ h₂ hne K₁ hK₁ ⟨hU₁K₁, hK12 ▸ hU₂K₂⟩

include hp in
theorem HypOmegaMod.natCard_eq_of_mem_USet (hΩ : HypOmegaMod p f Ω) {K U V : Subgroup G}
    (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) :
    Nat.card U = Nat.card V := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  obtain ⟨R', -, J', hJ', hRJ', hVR', -, hRV, -⟩ := hΩ.exists_data_of_mem_USet hp hV
  have h1 : J = K := hΩ.eq_of_mem_USet hp hU hJ hK (hUR.trans hRJ.1) hUK
  have h2 : J' = K := hΩ.eq_of_mem_USet hp hV hJ' hK (hVR'.trans hRJ'.1) hVK
  subst h1
  subst h2
  have := hRJ.natCard_eq hRJ'
  omega

include hp in
theorem HypOmegaMod.eq_or_sup_mem_RSet (hΩ : HypOmegaMod p f Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K)
    (hT : IsPGroup 2 ↥(U ⊔ V)) : U = V ∨ (U ⊔ V ∈ RSet Ω ∧ IsSylow2In (U ⊔ V) K) := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  have hJK : J = K := hΩ.eq_of_mem_USet hp hU hJ hK (hUR.trans hRJ.1) hUK
  subst hJK
  have hTK : U ⊔ V ≤ J := sup_le hUK hVK
  obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT hTK
  have hR₁card : Nat.card R₁ = 2 * Nat.card U := by rw [← hRU, hR₁.natCard_eq hRJ]
  rcases eq_or_eq_of_natCard_eq_two_mul le_sup_left hTR₁ hR₁card with h | h
  · left
    have hVU : V ≤ U := h ▸ le_sup_right
    have hcard := hΩ.natCard_eq_of_mem_USet hp hK hU hV hUK hVK
    exact (Subgroup.eq_of_le_of_card_ge hVU hcard.le).symm
  · right
    rw [h]
    exact ⟨mem_RSet_of_isSylow2In hJ hR₁, hR₁⟩

end Finite

end CFSG.ClassicalInvolution.Asc77
