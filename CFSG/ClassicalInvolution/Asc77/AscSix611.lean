module

public import CFSG.ClassicalInvolution.Asc77.AscSix610

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem conjSub_le_of_le_of_mem {A S : Subgroup G} (hA : A ≤ S) {s : G} (hs : s ∈ S) :
    conjSub s A ≤ S := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : s⁻¹ * x * s ∈ S := hA hx
  have h2 : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [h2]
  exact S.mul_mem (S.mul_mem hs h1) (S.inv_mem hs)

theorem conjSub_inf_of_mem_inf_normalizer {K S : Subgroup G} {q : G}
    (hq : q ∈ S ⊓ Subgroup.normalizer (K : Set G)) : conjSub q (K ⊓ S) = K ⊓ S := by
  rw [conjSub_inf, mem_normalizer_iff_conjSub_eq.mp hq.2, conjSub_eq_self_of_mem hq.1]

theorem isSylow2In_map_subtype [Finite G] (K : Subgroup G) (P : Sylow 2 ↥K) :
    IsSylow2In ((P : Subgroup ↥K).map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, fun V' hV'K hV'2 hle => ?_⟩
  have hQV : (P : Subgroup ↥K) ≤ V'.subgroupOf K := fun x hx => hle ⟨x, hx, rfl⟩
  have hcomap : V'.subgroupOf K = (P : Subgroup ↥K) := P.is_maximal' hV'2.comap_subtype hQV
  rw [← Subgroup.map_subgroupOf_eq_of_le hV'K, hcomap]

@[expose] noncomputable def sylowOfIsSylow2In {V K : Subgroup G} (h : IsSylow2In V K) :
    Sylow 2 ↥K where
  toSubgroup := V.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

theorem natCard_isSylow2In [Finite G] (K : Subgroup G) :
    Nat.card {R : Subgroup G // IsSylow2In R K} = Nat.card (Sylow 2 ↥K) := by
  refine Nat.card_congr
    { toFun := fun R => sylowOfIsSylow2In R.2
      invFun := fun P => ⟨(P : Subgroup ↥K).map K.subtype, isSylow2In_map_subtype K P⟩
      left_inv := fun R => ?_
      right_inv := fun P => ?_ }
  · exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le R.2.1)
  · apply Sylow.ext
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem exists_sylow_normalized [Finite G] {K W : Subgroup G} (hW : IsPGroup 2 W)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ ∀ w ∈ W, conjSub w R = R := by
  have hinv : ∀ w ∈ W, ∀ R ∈ {R : Subgroup G | IsSylow2In R K}, conjSub w R ∈
      {R : Subgroup G | IsSylow2In R K} := by
    intro w hw R hR
    have := IsSylow2In.conj hR w
    rwa [mem_normalizer_iff_conjSub_eq.mp (hWK hw)] at this
  have hodd : ¬ 2 ∣ Nat.card ↥{R : Subgroup G | IsSylow2In R K} := by
    have h1 : Nat.card ↥{R : Subgroup G | IsSylow2In R K} = Nat.card (Sylow 2 ↥K) :=
      natCard_isSylow2In K
    rw [h1]
    exact not_dvd_card_sylow 2 ↥K
  obtain ⟨R, hR, hfix⟩ := exists_fixed_conjSub hW hinv hodd
  exact ⟨R, hR, hfix⟩

section Finite

variable [Finite G]

theorem exists_mem_UinS_of_two_lt (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hC : Cyc66 Ω) (S : Sylow 2 G) {K : Subgroup G} (hK : K ∈ Ω)
    (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    ∃ U ∈ UinS Ω (S : Subgroup G), U ≤ K := by
  by_contra hno
  push Not at hno
  have hΩc := hΩ.conjInvariant
  set 𝒮 : Subgroup G := (S : Subgroup G) with h𝒮
  have h𝒮2 : IsPGroup 2 𝒮 := S.isPGroup'
  obtain ⟨β, hβ, hβinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S
  obtain ⟨habel, hUW⟩ := eta_abelian_of_cyc66 hp hq hΩ hC hβ hβinv
  have hβK : ∀ V ∈ β, ¬ V ≤ K := fun V hV hle => hno V (hβ.1 hV) hle
  have hAW : ∀ A ∈ β, A ≤ ⨆ U ∈ β, U := fun A hA => le_iSup₂_of_le A hA le_rfl
  set N : Subgroup G := 𝒮 ⊓ Subgroup.normalizer (K : Set G) with hNdef
  set T : Subgroup G := K ⊓ 𝒮 with hTdef
  have hN2 : IsPGroup 2 N := h𝒮2.to_le inf_le_left
  have hTN : T ≤ N := fun x hx =>
    ⟨hx.2, mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_self_of_mem hx.1)⟩
  have hTn : ∀ q ∈ N, conjSub q T = T := fun q hq => conjSub_inf_of_mem_inf_normalizer hq
  have hT2 : IsPGroup 2 ↥T := h𝒮2.to_inf_right
  have hTK : T ≤ K := inf_le_left
  have hT4 : 4 ≤ Nat.card T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      _ = Nat.card T := hn.symm
  obtain ⟨zK, hzK⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hzT : zK ∈ T := mem_of_isUniqueInvolution_of_isPGroup hzK hTK hT2 (by omega)
  have huniq : IsUniqueInvolution T zK :=
    ⟨hzT, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y (hTK hy) hy2⟩
  obtain ⟨A, hAT, hAcyc, hAcard, hAinv⟩ :=
    exists_invariant_cyclic_order_four hN2 hTN hTn huniq hT4
  have hAK : A ≤ K := hAT.trans hTK
  have hAS : A ≤ 𝒮 := hAT.trans inf_le_right
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_card (n := 2) (by rw [hAcard]; norm_num)
  have hzA : zK ∈ A := mem_of_isUniqueInvolution_of_isPGroup hzK hAK hA2 (by omega)
  set orb : Set (Subgroup G) := {B | ∃ s ∈ 𝒮, B = conjSub s A} with horb
  have hmem : ∀ s ∈ 𝒮, ∀ J ∈ Ω, conjSub s A ≤ J → J = conjSub s K := by
    intro s hs J hJ hle
    have hA4 : 4 ≤ Nat.card (conjSub s A) := by rw [natCard_conjSub, hAcard]
    have hA2' : IsPGroup 2 ↥(conjSub s A) := isPGroup_conjSub s hA2
    exact hΩ.eq_of_le_of_le hJ (hΩc s K hK) hA2' hA4 hle (conjSub_mono hAK)
  have hcov : ∀ s ∈ 𝒮, ∀ V ∈ β, ¬ V ≤ conjSub s K := by
    intro s hs V hV hle
    have h1 : conjSub s⁻¹ V ≤ K := by
      have := conjSub_mono (n := s⁻¹) hle
      rwa [conjSub_inv_conjSub] at this
    exact hβK _ (hβinv s⁻¹ (𝒮.inv_mem hs) V hV) h1
  have hkey : Commutes A (⨆ U ∈ β, U) := by
    have hcomm : ∀ V ∈ β, Commutes A V := by
      intro V hV
      refine hC 𝒮 h𝒮2 (β ∪ orb) ?_ ?_ ?_ ?_ A (Or.inr ⟨1, 𝒮.one_mem, (conjSub_one A).symm⟩) V
        (Or.inl hV) ?_
      · rintro B (hB | ⟨s, hs, rfl⟩)
        · exact (hβ.1 hB).2
        · exact conjSub_le_of_le_of_mem hAS hs
      · rintro B (hB | ⟨t, ht, rfl⟩) s hs
        · exact Or.inl (hβinv s hs B hB)
        · exact Or.inr ⟨s * t, 𝒮.mul_mem hs ht, (conjSub_mul s t A).symm⟩
      · rintro B (hB | ⟨s, hs, rfl⟩)
        · obtain ⟨R, -, J, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hp (hβ.1 hB).1
          exact ⟨hcyc, h4⟩
        · exact ⟨isCyclic_conjSub hAcyc s, by rw [natCard_conjSub, hAcard]⟩
      · intro B hB B' hB' hne
        have hmemΩ : ∀ B ∈ β ∪ orb, ∃ J ∈ Ω, B ≤ J := by
          rintro B (hB | ⟨s, hs, rfl⟩)
          · exact hΩ.exists_member_of_mem_USet hp (hβ.1 hB).1
          · exact ⟨conjSub s K, hΩc s K hK, conjSub_mono hAK⟩
        obtain ⟨J, hJ, hBJ⟩ := hmemΩ B hB
        obtain ⟨J', hJ', hBJ'⟩ := hmemΩ B' hB'
        refine ⟨J, hJ, J', hJ', fun hJJ => ?_, hBJ, hBJ'⟩
        subst hJJ
        rcases hB with hB | ⟨s, hs, rfl⟩ <;> rcases hB' with hB' | ⟨t, ht, rfl⟩
        · exact hβ.2.1 B hB B' hB' hne J hJ ⟨hBJ, hBJ'⟩
        · exact hcov t ht B hB (hmem t ht J hJ hBJ' ▸ hBJ)
        · exact hcov s hs B' hB' (hmem s hs J hJ hBJ ▸ hBJ')
        · have h1 := hmem s hs J hJ hBJ
          have h2 := hmem t ht J hJ hBJ'
          have hKst : conjSub t K = conjSub s K := h2.symm.trans h1
          have hst : conjSub (s⁻¹ * t) K = K := by
            rw [conjSub_mul, hKst, conjSub_inv_conjSub]
          have hmemN : s⁻¹ * t ∈ N :=
            ⟨𝒮.mul_mem (𝒮.inv_mem hs) ht, mem_normalizer_iff_conjSub_eq.mpr hst⟩
          have h3 := hAinv _ hmemN
          apply hne
          calc conjSub s A = conjSub s (conjSub (s⁻¹ * t) A) := by rw [h3]
            _ = conjSub (s * (s⁻¹ * t)) A := (conjSub_mul s _ A).symm
            _ = conjSub t A := by rw [mul_inv_cancel_left]
      · intro hAV
        exact hβK V hV (hAV ▸ hAK)
    intro x hx y hy
    have h1 : (⨆ U ∈ β, U) ≤ Subgroup.centralizer (A : Set G) := by
      refine iSup₂_le fun V hV v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcomm V hV a ha v hv)
    exact (Subgroup.mem_centralizer_iff.mp (h1 hy) x hx)
  have hWK : (⨆ U ∈ β, U) ≤ Subgroup.normalizer (K : Set G) := by
    refine iSup₂_le fun V hV => ?_
    have hVU : V ∈ USet Ω := (hβ.1 hV).1
    obtain ⟨J, hJ, hVJ⟩ := hΩ.exists_member_of_mem_USet hp hVU
    have hKJ : K ≠ J := by
      rintro rfl
      exact hβK V hV hVJ
    have hV4 : 4 ≤ Nat.card V := by
      obtain ⟨R, -, J', -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hVU
      exact h4
    have hVc : V ≤ Subgroup.centralizer ({zK} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hkey zK (hzA) v (hAW V hV hv)).symm
    exact hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hKJ hzK hVJ
      (hΩ.isPGroup_of_mem_USet hp hVU) (by omega) hVc
  have hW2 : IsPGroup 2 ↥(⨆ U ∈ β, U) := h𝒮2.to_le (iSup₂_le fun V hV => (hβ.1 hV).2)
  obtain ⟨R, hR, hRfix⟩ := exists_sylow_normalized hW2 hWK
  have hRW : (⨆ U ∈ β, U) ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  have hSig : IsPGroup 2 ↥(R ⊔ (⨆ U ∈ β, U)) := IsPGroup.to_sup_of_normal_left' hR.2.1 hW2 hRW
  obtain ⟨S', hS'⟩ := IsPGroup.exists_le_sylow hSig
  obtain ⟨U, hUR, hUcyc, hUcard⟩ :=
    (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)).exists_cyclic_index_two
  have hU : U ∈ USet Ω := mem_USet_of_natCard hK hR hUR hUcyc hUcard
  have hUS' : U ≤ (S' : Subgroup G) := hUR.trans (le_sup_left.trans hS')
  have hβS' : ∀ V ∈ β, V ≤ (S' : Subgroup G) := fun V hV =>
    (hAW V hV).trans (le_sup_right.trans hS')
  have hβ' : β ∈ etaSet Ω (S' : Subgroup G) := mem_etaSet_of_le hΩc hβ hβS'
  obtain ⟨V, hVβ, hVK⟩ := exists_mem_of_mem_etaSet hp hΩ hβ' hK ⟨hU, hUS'⟩ (hUR.trans hR.1)
  exact hβK V hVβ hVK

theorem eta_inf_mem_of_cyc66 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hC : Cyc66 Ω) {S : Sylow 2 G} {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) {K : Subgroup G} (hK : K ∈ Ω)
    (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) : K ⊓ (⨆ V ∈ η, V) ∈ η := by
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  obtain ⟨habel, hUW⟩ := eta_abelian_of_cyc66 hp hq hΩ hC hS₁ hinv
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  obtain ⟨U, hU, hUK⟩ := exists_mem_UinS_of_two_lt hp hq hΩ hC S hK h2
  obtain ⟨V₀, hV₀η, hV₀K⟩ := exists_mem_of_mem_etaSet hp hΩ hηS' hK hU hUK
  have hV₀U : V₀ ∈ USet Ω := (hηS'.1 hV₀η).1
  set W : Subgroup G := ⨆ V ∈ η, V with hW
  have hWS : W ≤ (S : Subgroup G) := iSup₂_le fun V hV => hηS V hV
  have hV₀W : V₀ ≤ W := le_iSup₂_of_le V₀ hV₀η le_rfl
  have hX2 : IsPGroup 2 ↥(K ⊓ W) := (S.isPGroup'.to_le hWS).to_inf_right
  obtain ⟨R₀, -, J, hJ, hR₀J, hV₀R₀, -, hR₀card, -⟩ := hΩ.exists_data_of_mem_USet hp hV₀U
  have hJK : J = K := hΩ.eq_of_mem_USet hp hV₀U hJ hK (hV₀R₀.trans hR₀J.1) hV₀K
  have hR₀K : IsSylow2In R₀ K := hJK ▸ hR₀J
  obtain ⟨R₁, hR₁, hXR₁⟩ := IsSylow2In.exists_ge hX2 (inf_le_left : K ⊓ W ≤ K)
  have hR₁card : Nat.card R₁ = 2 * Nat.card V₀ := by rw [← hR₀card, hR₁.natCard_eq hR₀K]
  have hV₀X : V₀ ≤ K ⊓ W := le_inf hV₀K hV₀W
  rcases eq_or_eq_of_natCard_eq_two_mul hV₀X hXR₁ hR₁card with hX | hX
  · rw [hX]
    exact hV₀η
  · exfalso
    have hquat := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR₁)
    obtain ⟨x, hx, y, hy, hxy⟩ := hquat.exists_not_commute
    rw [← hX] at hx hy
    exact hxy (habel x hx.2 y hy.2)

end Finite

variable (p f)

theorem l6_11_of_l6_6ii (h : L6_6ii p f) : L6_11 p f := by
  intro hp hq G _ _ Ω hΩ S η hη hηS K hK h2
  exact eta_inf_mem_of_cyc66 hp hq hΩ (h hp hq G Ω hΩ) hη hηS hK h2

theorem l6_11 (h : L6_6 p f) : L6_11 p f :=
  l6_11_of_l6_6ii p f (l6_6ii_of_l6_6 p f h)

@[expose] def L6_11AEmpty : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ K ∈ Ω, AEmpty Ω K) →
      ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
        ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

theorem l6_11AEmpty (h : L6_6iiAEmpty p f) : L6_11AEmpty p f := by
  intro hp hq G _ _ Ω hΩ hA S η hη hηS K hK h2
  exact eta_inf_mem_of_cyc66 hp hq hΩ (h hp hq G Ω hΩ hA) hη hηS hK h2

end CFSG.ClassicalInvolution.Asc77
