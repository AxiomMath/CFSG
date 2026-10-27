module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M0
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Conj
public import CFSG.ClassicalInvolution.Asc77.AscT7DRSix
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25
abbrev _root_.CFSG.ClassicalInvolution.T7F25.Asc77.Hyp25Data :=
  @CFSG.ClassicalInvolution.Asc77.Hyp25Data
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
@[expose] def L6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω →
      ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ η ∈ etaG Ω,
        (∀ V ∈ η, V ≤ (S : Subgroup G)) →
          ∃! V : Subgroup G, V ∈ η ∧ (U = V ∨ (U ⊔ V) ∈ RSet Ω)
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem mem_kPerp_of_twin (hΩ : HypOmegaMod Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx => hΩ.le_normalizer_of_twin hK hL hKL hzK hzL (hRK.1 hx)⟩
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]
theorem exists_mem_of_mem_etaSet (hΩ : HypOmegaMod Ω) {S : Subgroup G} {η : Set (Subgroup G)}
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
    · have hJK : J = K := hΩ.eq_of_mem_USet hU.1 hJ hK hVJ.1 hUK
      exact hno V₂ hV₂ (hJK ▸ hVJ.2)
    · have hJK : J = K := hΩ.eq_of_mem_USet hU.1 hJ hK hVJ.2 hUK
      exact hno V₁ hV₁ (hJK ▸ hVJ.1)
    · exact h.2.1 V₁ hV₁ V₂ hV₂ hne J hJ hVJ
  have hcard : (insert U η).ncard = η.ncard + 1 :=
    Set.ncard_insert_of_notMem hUη (Set.toFinite η)
  have := h.2.2 (insert U η) hsub' hd'
  omega
theorem HypOmegaMod.natCard_eq_of_mem_USet (hΩ : HypOmegaMod Ω) {K U V : Subgroup G}
    (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) :
    Nat.card U = Nat.card V := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := hΩ.exists_data_of_mem_USet hU
  obtain ⟨R', -, J', hJ', hRJ', hVR', -, hRV, -⟩ := hΩ.exists_data_of_mem_USet hV
  have h1 : J = K := hΩ.eq_of_mem_USet hU hJ hK (hUR.trans hRJ.1) hUK
  have h2 : J' = K := hΩ.eq_of_mem_USet hV hJ' hK (hVR'.trans hRJ'.1) hVK
  subst h1
  subst h2
  have := hRJ.natCard_eq hRJ'
  omega
theorem HypOmegaMod.eq_or_sup_mem_RSet (hΩ : HypOmegaMod Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K)
    (hT : IsPGroup 2 ↥(U ⊔ V)) : U = V ∨ (U ⊔ V ∈ RSet Ω ∧ IsSylow2In (U ⊔ V) K) := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, hRU, -⟩ := hΩ.exists_data_of_mem_USet hU
  have hJK : J = K := hΩ.eq_of_mem_USet hU hJ hK (hUR.trans hRJ.1) hUK
  subst hJK
  have hTK : U ⊔ V ≤ J := sup_le hUK hVK
  obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT hTK
  have hR₁card : Nat.card R₁ = 2 * Nat.card U := by rw [← hRU, hR₁.natCard_eq hRJ]
  rcases eq_or_eq_of_natCard_eq_two_mul le_sup_left hTR₁ hR₁card with h | h
  · left
    have hVU : V ≤ U := h ▸ le_sup_right
    have hcard := hΩ.natCard_eq_of_mem_USet hK hU hV hUK hVK
    exact (Subgroup.eq_of_le_of_card_ge hVU hcard.le).symm
  · right
    rw [h]
    exact ⟨mem_RSet_of_isSylow2In hJ hR₁, hR₁⟩
end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Std7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
theorem l6_8 : L6_8 := by
  intro G _ _ Ω hΩ S U hU hUS η hη hηS
  obtain ⟨S₁, hS₁, -⟩ := hη
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  obtain ⟨K, hK, hUK⟩ := hΩ.exists_member_of_mem_USet hU
  obtain ⟨V₀, hV₀, hV₀K⟩ := exists_mem_of_mem_etaSet hΩ hηS' hK ⟨hU, hUS⟩ hUK
  have hV₀U : V₀ ∈ USet Ω := (hS₁.1 hV₀).1
  have hT : IsPGroup 2 ↥(U ⊔ V₀) := S.isPGroup'.to_le (sup_le hUS (hηS V₀ hV₀))
  have hdich := hΩ.eq_or_sup_mem_RSet hK hU hV₀U hUK hV₀K hT
  have hlie : ∀ V : Subgroup G, (U = V ∨ U ⊔ V ∈ RSet Ω) → V ≤ K := by
    intro V h
    rcases h with h | hR
    · exact h ▸ hUK
    · obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
      have hJK : J = K :=
        hΩ.eq_of_mem_USet hU hJ hK (le_sup_left.trans hRJ.1) hUK
      exact hJK ▸ (le_sup_right.trans hRJ.1)
  refine ⟨V₀, ⟨hV₀, ?_⟩, ?_⟩
  · rcases hdich with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro V₁ ⟨hV₁, h₁⟩
    by_contra hne
    exact hS₁.2.1 V₁ hV₁ V₀ hV₀ hne K hK ⟨hlie V₁ h₁, hV₀K⟩
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def Hyp23 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop :=
  Std7 Ω K K' z ∧ KPerp Ω K = {K, K'}
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G]
section Mu
variable {Ω : Set (Subgroup G)}
theorem conjSub_mem_DSet_conj [Finite G] (hΩ : HypOmegaMod Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W)
    (g : G) : conjSub g R ∈ DSet Ω (conjSub g W) := by
  refine ⟨Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hR.1 g, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 := hR.2 hx
  rw [Asc77.Thompson.conjSub_normalizer, mem_conjSub_iff]
  exact h1
theorem conjSub_MGrp [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    conjSub g (MGrp Ω W) = MGrp Ω (conjSub g W) := by
  apply le_antisymm
  · unfold MGrp
    rw [conjSub, Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    exact le_iSup₂ (f := fun R (_ : R ∈ DSet Ω (conjSub g W)) => R) (conjSub g R)
      (conjSub_mem_DSet_conj hΩ hR g)
  · refine iSup₂_le fun R hR => ?_
    have hR' : conjSub g⁻¹ R ∈ DSet Ω W := by
      have := conjSub_mem_DSet_conj hΩ hR g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h1 : conjSub g⁻¹ R ≤ MGrp Ω W := le_MGrp_of_mem_D hR'
    have h2 := conjSub_mono (n := g) h1
    rwa [conjSub_conjSub_inv] at h2
end Mu
end Thompson
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem exists_W_of_mem_omegaStarNbr (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaStarNbr Ω K) :
    ∃ W ∈ WSet Ω, ∃ R ∈ DSet Ω W, ∃ T ∈ DSet Ω W, IsSylow2In R K ∧ IsSylow2In T J := by
  obtain ⟨hJΩ, -, U, hU, hUJ, hUN⟩ := hJ
  have hU2 : IsPGroup 2 U := hΩ.isPGroup_of_mem_USet hU
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := hΩ.exists_data_of_mem_USet hU
  obtain ⟨R, hRK, hRU⟩ := T3.exists_sylow_normalized hU2 hUN
  have hRmem : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRK
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S, hS⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  have hUS : U ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans hS
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved G Ω hΩ S).1
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  have hW : (⨆ V ∈ η, V : Subgroup G) ∈ WSet Ω := ⟨η, hηG, rfl⟩
  set W : Subgroup G := ⨆ V ∈ η, V with hWdef
  have hRD : R ∈ DSet Ω W :=
    ⟨hRmem, le_normalizer_biSup_of_acts
      ((l6_10_proved G Ω hΩ S η hηG hηS).1 R hRmem hRS)⟩
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (hU4.trans (Subgroup.card_le_of_le (le_inf hUJ hUS)))
  have hV₀ : J ⊓ W ∈ η := l6_11_proved G Ω hΩ S η hηG hηS J hJΩ hJS
  have hV₀U : J ⊓ W ∈ USet Ω := (hη.1 hV₀).1
  have hV₀2 : IsPGroup 2 ↥(J ⊓ W) := hΩ.isPGroup_of_mem_USet hV₀U
  obtain ⟨-, -, -, -, -, -, -, -, hV₀4⟩ := hΩ.exists_data_of_mem_USet hV₀U
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hJΩ
  have hzV₀ : zJ ∈ J ⊓ W := T3.mem_of_isPGroup hzJ inf_le_left hV₀2 (by omega)
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) := by
    refine iSup₂_le fun V hV => ?_
    by_cases hVeq : V = J ⊓ W
    · rw [hVeq]
      exact inf_le_left.trans Subgroup.le_normalizer
    · obtain ⟨Rv, -, J', hJ', hRvJ', hVRv, -, -, hV4⟩ :=
        hΩ.exists_data_of_mem_USet (hη.1 hV).1
      have hVJ' : V ≤ J' := hVRv.trans hRvJ'.1
      have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet (hη.1 hV).1
      have hJJ' : J ≠ J' := by
        intro hJJ'
        rw [← hJJ'] at hVJ'
        exact hη.2.1 V hV (J ⊓ W) hV₀ hVeq J hJΩ ⟨hVJ', inf_le_left⟩
      refine hΩ.le_normalizer_of_le_centralizer hJΩ hJ' hJJ' hzJ hVJ' hV2 (by omega) ?_
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hWab v (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV hv) zJ hzV₀.2
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨T, hTJ, hTW⟩ := T3.exists_sylow_normalized hW2 hWJ
  have hWT : W ≤ Subgroup.normalizer (T : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hTW w hw)
  obtain ⟨S', hS'⟩ := (hW2.to_sup_of_normal_right' hTJ.2.1 hWT).exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hTS' : T ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  have hηS' : ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS'
  have hTmem : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hTJ
  have hTD : T ∈ DSet Ω W :=
    ⟨hTmem, le_normalizer_biSup_of_acts
      ((l6_10_proved G Ω hΩ S' η hηG hηS').1 T hTmem hTS')⟩
  exact ⟨W, hW, R, hRD, T, hTD, hRK, hTJ⟩
end Existence
end Thompson
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

structure Hyp25 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop where
  std : Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W'
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hRS : ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  ht : t ∈ (S : Subgroup G) ∧ t ≠ z ∧ ∃ g : G, g * z * g⁻¹ = t
  hu₁ : u₁ ∈ R ∧ orderOf u₁ = 4 ∧ ∀ r ∈ R, r * u₁ * r⁻¹ ∈ Subgroup.zpowers u₁
  hu₂ : u₂ ∈ R' ∧ orderOf u₂ = 4 ∧ ∀ r ∈ R', r * u₂ * r⁻¹ ∈ Subgroup.zpowers u₂

@[expose] def C25_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
        Subgroup.zpowers z

@[expose] def C25_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp23Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = {K, K'}
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23.setting (h : Hyp23 Ω K K' z) : Hyp23Setting Ω K K' z where
  stand := h.1.stand
  disconnected := h.1.disconnected
  hz := h.1.hz
  hK' := h.1.hK'
  hne := h.1.hne
  perp := h.2

theorem Hyp23Setting.twinSet_eq (h : Hyp23Setting Ω K K' z) : twinSet Ω K = {K, K'} := by
  ext L
  constructor
  · intro hL
    have hLperp : L ∈ KPerp Ω K :=
      mem_kPerp_of_twin h.stand.hyp hL.1 h.stand.mem (isUniqueInvolution_of_mem_twinSet h.hz hL)
        h.hz
    rw [h.perp] at hLperp
    exact hLperp
  · rintro (rfl | rfl)
    · exact mem_twinSet_self h.stand.mem h.hz
    · exact h.hK'
end Basic
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaMod Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  by_cases hJK : J = K
  · exact hJK ▸ hRJ
  · exfalso
    have h1 := hΩ.card_le_two_of_le_inf hJ hK hJK hRJ.2.1 hRJ.1 hRK
    have h2 := hΩ.eight_le_of_mem_RSet hR
    omega
end T7C
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
    CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
    CFSG.LieType.CurtisTits CFSG.Blueprint
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C

theorem exists_not_commute_of_stand {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand Ω K) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hs.hyp.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hs.mem hV)).exists_not_commute
  exact ⟨x, y, hxy⟩

end T7C
variable {G : Type} [Group G]
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

@[expose] def C25_2_t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R'
namespace T7DR
open CFSG.ClassicalInvolution.Asc77.T7DR
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tf4_of_index_two {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ t' : G} (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h2 : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R')) (ht' : t' ∈ (S : Subgroup G))
    (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R') :
    TwoSubgroupsFourGenerated G := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' hRsyl.1
    hR'syl.1 (S.isPGroup'.to_le (sup_le hRS hR'S))
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hyp.hR.1
  obtain ⟨a, b, haR, hbR, hclos, hbab, k, hk⟩ := exists_gens_of_isQuatSub hquat
  have hR8 : 8 ≤ Nat.card ↥R := hquat.eight_le
  have hRR' : R ≠ R' := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hRsyl.2.1 hRsyl.1 (by rw [h]; exact hR'syl.1)
    omega
  obtain ⟨g, hg'⟩ := hg
  have ht2 : t' * t' = 1 := by
    rw [← hg']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub haR
  have h5 : a * (t' * a * t'⁻¹) = (t' * a * t'⁻¹) * a := hc a haR _ ha'R'
  have h6 : b * (t' * a * t'⁻¹) = (t' * a * t'⁻¹) * b := hc b hbR _ ha'R'
  have haT : a ∈ (S : Subgroup G) := hRS haR
  have hbT : b ∈ (S : Subgroup G) := hRS hbR

  set U : Subgroup G := Subgroup.closure ({a, b, t'} : Set G) with hU
  have hUT : U ≤ (S : Subgroup G) := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact haT
    · exact hbT
    · exact ht'
  have hRU : R ≤ U := by
    rw [← hclos]
    exact Subgroup.closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr
      (Set.mem_insert _ _)))
  have ht'U : t' ∈ U := Subgroup.subset_closure (by simp)
  have hR'U : R' ≤ U := by
    intro x hx
    have hx' : x ∈ conjSub t' R := by rw [hconj]; exact hx
    rw [mem_conjSub_iff] at hx'
    have h1 : t'⁻¹ * x * t' ∈ U := hRU hx'
    have : x = t' * (t'⁻¹ * x * t') * t'⁻¹ := by group
    rw [this]
    exact U.mul_mem (U.mul_mem ht'U h1) (U.inv_mem ht'U)
  have hNU : R ⊔ R' ≤ U := sup_le hRU hR'U
  have ht'N : t' ∉ R ⊔ R' := by
    intro htN
    have hnorm : R ⊔ R' ≤ Subgroup.normalizer (R : Set G) := by
      refine sup_le Subgroup.le_normalizer ?_
      intro x hx
      exact Subgroup.mem_normalizer_fintype (fun n hn => by
        have h1 : n * x = x * n := hc n hn x hx
        have hxn : x * n * x⁻¹ = n := by
          calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [h1]
            _ = n := by group
        rw [hxn]
        exact hn)
    have : conjSub t' R = R := mem_normalizer_iff_conjSub_eq.mp (hnorm htN)
    exact hRR' (this.symm.trans hconj)
  have hNpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hltNU : Nat.card ↥(R ⊔ R') < Nat.card ↥U := by
    by_contra hge
    push Not at hge
    exact ht'N ((Subgroup.eq_of_le_of_card_ge hNU hge) ▸ ht'U)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hNU
  have hdvd2 : Nat.card ↥U ∣ Nat.card ↥(S : Subgroup G) := Subgroup.card_dvd_of_le hUT
  rw [h2, hm, mul_comm 2] at hdvd2
  have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hNpos hdvd2
  have hm2' : m = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h | h
    · rw [h, mul_one] at hm
      omega
    · exact h
  have hUS : U = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hUT (by rw [h2, hm, hm2']; omega)
  refine twoSubgroupsFourGenerated_of_sylow S fun H hH => ?_
  exact genLE_four_of_omega5_sub haT hbT ht' hUS hbab ⟨(k : ℤ), by simpa using hk⟩ ht2 h5 h6 hH
end T7DR
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2
namespace T7DR
open CFSG.ClassicalInvolution.Asc77.T7DR
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tf4_of_index_four {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ a b s t' : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (haR : a ∈ R) (hbR : b ∈ R)
    (hbab : b * a * b⁻¹ = a⁻¹) (hk : ∃ k : ℤ, b * b = a ^ k) (hs : s ∈ (S : Subgroup G))
    (ht' : t' ∈ (S : Subgroup G)) (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R')
    (hSgen : Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G)) (hs2 : s * s = 1)
    (hst : s * t' = t' * s) (hsa : s * a * s⁻¹ = a⁻¹) (hsb : s * b * s⁻¹ = b * a) :
    TwoSubgroupsFourGenerated G := by
  have hsetting : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst0 : AscStand Ω K := hsetting.stand
  have hΩ : HypOmegaMod Ω := hst0.hyp
  have hK : K ∈ Ω := hst0.mem
  have hK' : K' ∈ Ω := hsetting.hK'.1
  have hKK' : K' ≠ K := hsetting.hne
  have hz : IsUniqueInvolution K z := hsetting.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hsetting.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' hRsyl.1
    hR'syl.1 (S.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨g, hg'⟩ := hg
  have ht2 : t' * t' = 1 := by
    rw [← hg']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub haR
  have hb'R' : t' * b * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub hbR
  obtain ⟨k, hk'⟩ := hk
  have hbb : (b * b) * (b * b) = 1 := sq_mul_sq_eq_one hbab hk'
  have hbbK : b * b ∈ K := hRsyl.1 (R.mul_mem hbR hbR)
  have h6 : t' * (b * b) * t'⁻¹ = b * b := by
    rcases hz.unique (b * b) hbbK hbb with h | h
    · rw [h]
      group
    · rw [h]
      have := hyp.hzS t' ht'
      calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [this]
        _ = z := by group
  have haT : a ∈ (S : Subgroup G) := hRS haR
  have hbT : b ∈ (S : Subgroup G) := hRS hbR
  refine twoSubgroupsFourGenerated_of_sylow S fun H hH => ?_
  exact genLE_four_of_omega6_sub haT hbT hs ht' hSgen hbab ⟨k, hk'⟩ ht2 hs2
    hst hsa hsb (hc a haR _ ha'R') (hc a haR _ hb'R') (hc b hbR _ ha'R') (hc b hbR _ hb'R') h6 hH
end T7DR
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
