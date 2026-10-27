module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem le_normalizer_of_twin [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) := by
  have hc := comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ
  have key : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have h1 : ⁅k, j⁆ ∈ oddCoreOf J := (hc (Subgroup.commutator_mem_commutator hk hj)).2
    have h2 : ⁅k, j⁆ ∈ J := oddCoreOf_le_self J h1
    have e : k * j * k⁻¹ = ⁅k, j⁆ * j := by rw [commutatorElement_def]; group
    rw [e]
    exact J.mul_mem h2 hj
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key k hk h hh, fun hh => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hh
  have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem commutes_of_twin_of_isPGroup [Finite G] (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) {A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ J)
    (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B := by
  intro a ha b hb
  have hc := comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ
  have h1 : ⁅a, b⁆ ∈ oddCoreOf K := (hc (Subgroup.commutator_mem_commutator (hA ha) (hB hb))).1
  have ha' : a ∈ A ⊔ B := Subgroup.mem_sup_left ha
  have hb' : b ∈ A ⊔ B := Subgroup.mem_sup_right hb
  have h2 : ⁅a, b⁆ ∈ A ⊔ B := by
    rw [commutatorElement_def]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem ha' hb') ((A ⊔ B).inv_mem ha'))
      ((A ⊔ B).inv_mem hb')
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅a, b⁆) := hAB.to_le (Subgroup.zpowers_le.mpr h2)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)

section Finite

variable [Finite G]

theorem exists_data_of_mem_USet (hΩ : HypOmegaGen Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, hidx] at h1
  have h8 := eight_le_of_mem_RSet hΩ hR
  exact ⟨R, hR, J, hJ, hRJ, hUR, hcyc, h1.symm, by omega⟩

theorem isPGroup_of_mem_USet (hΩ : HypOmegaGen Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    IsPGroup 2 U := by
  obtain ⟨R, -, J, -, hRJ, hUR, -⟩ := exists_data_of_mem_USet hΩ hU
  exact hRJ.2.1.to_le hUR

theorem exists_member_of_mem_USet (hΩ : HypOmegaGen Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ K ∈ Ω, U ≤ K := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -⟩ := exists_data_of_mem_USet hΩ hU
  exact ⟨J, hJ, hUR.trans hRJ.1⟩

theorem eq_of_mem_USet (hΩ : HypOmegaGen Ω) {U : Subgroup G} (hU : U ∈ USet Ω)
    {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K) (hUK' : U ≤ K') : K = K' := by
  obtain ⟨R, -, J, -, hRJ, hUR, -, -, h4⟩ := exists_data_of_mem_USet hΩ hU
  exact eq_of_le_of_le hΩ hK hK' (hRJ.2.1.to_le hUR) h4 hUK hUK'

theorem natCard_eq_of_mem_USet (hΩ : HypOmegaGen Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) :
    Nat.card U = Nat.card V := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := exists_data_of_mem_USet hΩ hU
  obtain ⟨R', -, J', hJ', hRJ', hVR', -, hRV, -⟩ := exists_data_of_mem_USet hΩ hV
  have h1 : J = K := eq_of_mem_USet hΩ hU hJ hK (hUR.trans hRJ.1) hUK
  have h2 : J' = K := eq_of_mem_USet hΩ hV hJ' hK (hVR'.trans hRJ'.1) hVK
  subst h1
  subst h2
  have := hRJ.natCard_eq hRJ'
  omega

theorem eq_or_sup_mem_RSet (hΩ : HypOmegaGen Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K)
    (hT : IsPGroup 2 ↥(U ⊔ V)) : U = V ∨ (U ⊔ V ∈ RSet Ω ∧ IsSylow2In (U ⊔ V) K) := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := exists_data_of_mem_USet hΩ hU
  have hJK : J = K := eq_of_mem_USet hΩ hU hJ hK (hUR.trans hRJ.1) hUK
  subst hJK
  have hTK : U ⊔ V ≤ J := sup_le hUK hVK
  obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT hTK
  have hR₁card : Nat.card R₁ = 2 * Nat.card U := by rw [← hRU, hR₁.natCard_eq hRJ]
  rcases eq_or_eq_of_natCard_eq_two_mul le_sup_left hTR₁ hR₁card with h | h
  · left
    have hVU : V ≤ U := h ▸ le_sup_right
    have hcard := natCard_eq_of_mem_USet hΩ hK hU hV hUK hVK
    exact (Subgroup.eq_of_le_of_card_ge hVU hcard.le).symm
  · right
    rw [h]
    exact ⟨mem_RSet_of_isSylow2In hJ hR₁, hR₁⟩

theorem exists_mem_of_mem_etaSet (hΩ : HypOmegaGen Ω) {S : Subgroup G} {η : Set (Subgroup G)}
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
    · have hJK : J = K := eq_of_mem_USet hΩ hU.1 hJ hK hVJ.1 hUK
      exact hno V₂ hV₂ (hJK ▸ hVJ.2)
    · have hJK : J = K := eq_of_mem_USet hΩ hU.1 hJ hK hVJ.2 hUK
      exact hno V₁ hV₁ (hJK ▸ hVJ.1)
    · exact h.2.1 V₁ hV₁ V₂ hV₂ hne J hJ hVJ
  have hcard : (insert U η).ncard = η.ncard + 1 :=
    Set.ncard_insert_of_notMem hUη (Set.toFinite η)
  have := h.2.2 (insert U η) hsub' hd'
  omega

theorem mem_etaSet_of_cover (hΩ : HypOmegaGen Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (hsub : η ⊆ UinS Ω S) (hd : InDistinctMembers Ω η)
    (hcov : ∀ K ∈ Ω, (∃ U ∈ UinS Ω S, U ≤ K) → ∃ V ∈ η, V ≤ K) : η ∈ etaSet Ω S := by
  classical
  refine ⟨hsub, hd, fun η' hη' hd' => ?_⟩
  have hex : ∀ U' ∈ η', ∃ V ∈ η, ∃ K ∈ Ω, U' ≤ K ∧ V ≤ K := by
    intro U' hU'
    obtain ⟨K, hK, hU'K⟩ := exists_member_of_mem_USet hΩ (hη' hU').1
    obtain ⟨V, hV, hVK⟩ := hcov K hK ⟨U', hη' hU', hU'K⟩
    exact ⟨V, hV, K, hK, hU'K, hVK⟩
  choose! g hgη hgK using hex
  refine Set.ncard_le_ncard_of_injOn g hgη ?_ (Set.toFinite η)
  intro U₁ h₁ U₂ h₂ heq
  by_contra hne
  obtain ⟨K₁, hK₁, hU₁K₁, hgK₁⟩ := hgK U₁ h₁
  obtain ⟨K₂, hK₂, hU₂K₂, hgK₂⟩ := hgK U₂ h₂
  have hV : g U₁ ∈ USet Ω := (hsub (hgη U₁ h₁)).1
  have hK12 : K₁ = K₂ := eq_of_mem_USet hΩ hV hK₁ hK₂ hgK₁ (heq ▸ hgK₂)
  exact hd' U₁ h₁ U₂ h₂ hne K₁ hK₁ ⟨hU₁K₁, hK12 ▸ hU₂K₂⟩

end Finite

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
