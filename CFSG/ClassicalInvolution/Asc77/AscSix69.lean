module

public import CFSG.ClassicalInvolution.Asc77.AscSix68
public import CFSG.ClassicalInvolution.Asc77.AscSix66Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem isCyclic_conjSub {U : Subgroup G} (hU : IsCyclic ↥U) (g : G) : IsCyclic ↥(conjSub g U) := by
  let e := Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact (MulEquiv.isCyclic e).mp hU

theorem natCard_conjSub (U : Subgroup G) (g : G) : Nat.card ↥(conjSub g U) = Nat.card ↥U :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_inf (A B : Subgroup G) (g : G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

theorem conjSub_eq_of_le_of_mem {A : Subgroup G} {g : G} (hg : g ∈ A) : conjSub g A = A :=
  conjSub_eq_self_of_mem hg

theorem exists_invariant_mem_USet [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K T P : Subgroup G} (hK : K ∈ Ω) (hT : IsSylow2In T K) (hP : IsPGroup 2 P) (hTP : T ≤ P)
    (hTn : ∀ q ∈ P, conjSub q T = T) :
    ∃ U ∈ USet Ω, U ≤ T ∧ ∀ q ∈ P, conjSub q U = U := by
  have hTR : T ∈ RSet Ω := mem_RSet_of_isSylow2In hK hT
  have hquat := hΩ.isQuatSub_of_mem_RSet hp hTR
  have h8 := hquat.eight_le
  obtain ⟨k, hk, hcard⟩ := hquat.natCard_eq
  by_cases h16 : 16 ≤ Nat.card T
  · obtain ⟨U, hUT, hcyc, hUcard⟩ := hquat.exists_cyclic_index_two
    refine ⟨U, mem_USet_of_natCard hK hT hUT hcyc hUcard, hUT, fun q hq => ?_⟩
    have hcard' : Nat.card T = 2 * Nat.card (conjSub q U) := by rw [natCard_conjSub, hUcard]
    have hle : conjSub q U ≤ T := by
      have := conjSub_mono (n := q) hUT
      rwa [hTn q hq] at this
    exact (hquat.eq_of_cyclic hUT hle hcyc (isCyclic_conjSub hcyc q) hUcard hcard' h16).symm
  · have h8' : Nat.card T = 8 := by
      have : Nat.card T = 2 ^ (k + 2) := hcard
      have hk1 : k = 1 := by
        by_contra hne
        have : 2 ≤ k := by omega
        have h4 : 2 ^ 4 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hk1
      norm_num at this
      exact this
    obtain ⟨zK, hzK⟩ := hΩ.exists_uniqueInvolution hp hq hK
    have h2dvd : 2 ∣ Nat.card ↥T := by rw [h8']; norm_num
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have htsq : (t : G) * (t : G) = 1 := by
      have := pow_orderOf_eq_one (t : G)
      rwa [htG, pow_two] at this
    have htne : (t : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at htG
      omega
    have hzT : zK ∈ T := by
      rcases hzK.unique (t : G) (hT.1 t.2) htsq with h | h
      · exact absurd h htne
      · exact h ▸ t.2
    have huniq : IsUniqueInvolution T zK :=
      ⟨hzT, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y (hT.1 hy) hy2⟩
    obtain ⟨A, hAT, hcycA, hAcard, hAinv⟩ :=
      exists_invariant_cyclic_order_four hP hTP hTn huniq (by omega)
    exact ⟨A, mem_USet_of_natCard hK hT hAT hcycA (by rw [h8', hAcard]), hAT, hAinv⟩

theorem exists_invariant_mem_etaSet [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (S : Sylow 2 G) :
    ∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η := by
  classical
  have hΩc := hΩ.conjInvariant
  set 𝒮 : Subgroup G := (S : Subgroup G) with h𝒮
  have h𝒮2 : IsPGroup 2 𝒮 := S.isPGroup'
  let Adm : Set (Set (Subgroup G)) :=
    {η | η ⊆ UinS Ω 𝒮 ∧ (∀ s ∈ 𝒮, ∀ U ∈ η, conjSub s U ∈ η) ∧ InDistinctMembers Ω η}
  have hAdm : Adm.Nonempty :=
    ⟨∅, Set.empty_subset _, fun s _ U hU => absurd hU (Set.notMem_empty U),
      fun U hU => absurd hU (Set.notMem_empty U)⟩
  obtain ⟨η, hηA, hmax⟩ := Set.exists_max_image Adm (fun η => η.ncard) (Set.toFinite Adm) hAdm
  refine ⟨η, ?_, hηA.2.1⟩
  refine mem_etaSet_of_cover hp hΩ hηA.1 hηA.2.2 ?_
  rintro K hK ⟨U₀, hU₀, hU₀K⟩
  by_contra hno
  push Not at hno
  set N : Subgroup G := 𝒮 ⊓ Subgroup.normalizer (K : Set G) with hNdef
  set T : Subgroup G := K ⊓ 𝒮 with hTdef
  have hN2 : IsPGroup 2 N := h𝒮2.to_le inf_le_left
  have hTN : T ≤ N := fun x hx =>
    ⟨hx.2, mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_self_of_mem hx.1)⟩
  have hTn : ∀ q ∈ N, conjSub q T = T := by
    intro q hq
    rw [hTdef, conjSub_inf, mem_normalizer_iff_conjSub_eq.mp hq.2, conjSub_eq_self_of_mem hq.1]
  have hT2 : IsPGroup 2 T := h𝒮2.to_le inf_le_right
  have hTK : T ≤ K := inf_le_left
  have hU₀T : U₀ ≤ T := le_inf hU₀K hU₀.2
  have key : ∃ U₁ ∈ USet Ω, U₁ ≤ T ∧ ∀ q ∈ N, conjSub q U₁ = U₁ := by
    obtain ⟨R₀, -, J, hJ, hR₀J, hU₀R₀, -, hR₀card, -⟩ := hΩ.exists_data_of_mem_USet hp hU₀.1
    have hJK : J = K := hΩ.eq_of_mem_USet hp hU₀.1 hJ hK (hU₀R₀.trans hR₀J.1) hU₀K
    subst hJK
    obtain ⟨R₁, hR₁, hTR₁⟩ := IsSylow2In.exists_ge hT2 hTK
    have hR₁card : Nat.card R₁ = 2 * Nat.card U₀ := by rw [← hR₀card, hR₁.natCard_eq hR₀J]
    rcases eq_or_eq_of_natCard_eq_two_mul hU₀T hTR₁ hR₁card with hTeq | hTeq
    · refine ⟨U₀, hU₀.1, hU₀T, fun q hq => ?_⟩
      have := hTn q hq
      rwa [hTeq] at this
    · exact exists_invariant_mem_USet hp hq hΩ hK (hTeq ▸ hR₁) hN2 hTN hTn
  obtain ⟨U₁, hU₁, hU₁T, hU₁inv⟩ := key
  have hU₁K : U₁ ≤ K := hU₁T.trans hTK
  have hU₁S : U₁ ∈ UinS Ω 𝒮 := ⟨hU₁, hU₁T.trans inf_le_right⟩
  set orb : Set (Subgroup G) := {V | ∃ s ∈ 𝒮, V = conjSub s U₁} with horb
  have horb_sub : orb ⊆ UinS Ω 𝒮 := by
    rintro _ ⟨s, hs, rfl⟩
    exact UinS.conj hΩc hU₁S hs
  have hmem : ∀ s ∈ 𝒮, ∀ J ∈ Ω, conjSub s U₁ ≤ J → J = conjSub s K := fun s hs J hJ hle =>
    hΩ.eq_of_mem_USet hp (USet.conj hΩc hU₁ s) hJ (hΩc s K hK) hle (conjSub_mono hU₁K)
  have hinvη : ∀ s ∈ 𝒮, ∀ V ∈ η, conjSub s V ∈ η := hηA.2.1
  have hcov : ∀ s ∈ 𝒮, ∀ V ∈ η, ¬ V ≤ conjSub s K := by
    intro s hs V hV hle
    have h1 : conjSub s⁻¹ V ≤ K := by
      have := conjSub_mono (n := s⁻¹) hle
      rwa [conjSub_inv_conjSub] at this
    exact hno _ (hinvη s⁻¹ (𝒮.inv_mem hs) V hV) h1
  have hη'A : η ∪ orb ∈ Adm := by
    refine ⟨Set.union_subset hηA.1 horb_sub, ?_, ?_⟩
    · intro s hs V hV
      rcases hV with hV | ⟨t, ht, rfl⟩
      · exact Or.inl (hinvη s hs V hV)
      · exact Or.inr ⟨s * t, 𝒮.mul_mem hs ht, (conjSub_mul s t U₁).symm⟩
    · intro V₁ hV₁ V₂ hV₂ hne J hJ hVJ
      rcases hV₁ with hV₁ | ⟨s, hs, rfl⟩ <;> rcases hV₂ with hV₂ | ⟨t, ht, rfl⟩
      · exact hηA.2.2 V₁ hV₁ V₂ hV₂ hne J hJ hVJ
      · have hJ' := hmem t ht J hJ hVJ.2
        exact hcov t ht V₁ hV₁ (hJ' ▸ hVJ.1)
      · have hJ' := hmem s hs J hJ hVJ.1
        exact hcov s hs V₂ hV₂ (hJ' ▸ hVJ.2)
      · have h1 := hmem s hs J hJ hVJ.1
        have h2 := hmem t ht J hJ hVJ.2
        have hKst : conjSub t K = conjSub s K := h2.symm.trans h1
        have hst : conjSub (s⁻¹ * t) K = K := by
          rw [conjSub_mul, hKst, conjSub_inv_conjSub]
        have hmemN : s⁻¹ * t ∈ N :=
          ⟨𝒮.mul_mem (𝒮.inv_mem hs) ht, mem_normalizer_iff_conjSub_eq.mpr hst⟩
        have h3 := hU₁inv _ hmemN
        apply hne
        calc conjSub s U₁ = conjSub s (conjSub (s⁻¹ * t) U₁) := by rw [h3]
          _ = conjSub (s * (s⁻¹ * t)) U₁ := (conjSub_mul s _ U₁).symm
          _ = conjSub t U₁ := by rw [mul_inv_cancel_left]
  have hss : η ⊂ η ∪ orb := by
    refine Set.ssubset_def.mpr ⟨Set.subset_union_left, fun hsub => ?_⟩
    have hU₁orb : U₁ ∈ orb := ⟨1, 𝒮.one_mem, (conjSub_one U₁).symm⟩
    exact hno U₁ (hsub (Or.inr hU₁orb)) hU₁K
  have h1 : (η ∪ orb).ncard ≤ η.ncard := hmax _ hη'A
  have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
  omega

theorem eta_abelian_of_cyc66 [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hC : Cyc66 Ω) {S : Sylow 2 G} {η : Set (Subgroup G)} (h : η ∈ etaSet Ω (S : Subgroup G))
    (hinv : ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) :
    (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
      {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η := by
  have hcomm : ∀ A ∈ η, ∀ B ∈ η, Commutes A B := by
    have hdistinct : ∀ A ∈ η, ∀ B ∈ η, A ≠ B → Commutes A B := by
      refine hC (S : Subgroup G) S.isPGroup' η (fun A hA => (h.1 hA).2)
        (fun A hA s hs => hinv s hs A hA) ?_ ?_
      · intro A hA
        obtain ⟨R, -, J, -, -, -, hcyc, -, h4⟩ := hΩ.exists_data_of_mem_USet hp (h.1 hA).1
        exact ⟨hcyc, h4⟩
      · intro A hA B hB hne
        obtain ⟨J₁, hJ₁, hAJ₁⟩ := hΩ.exists_member_of_mem_USet hp (h.1 hA).1
        obtain ⟨J₂, hJ₂, hBJ₂⟩ := hΩ.exists_member_of_mem_USet hp (h.1 hB).1
        refine ⟨J₁, hJ₁, J₂, hJ₂, fun hJ => ?_, hAJ₁, hBJ₂⟩
        exact h.2.1 A hA B hB hne J₁ hJ₁ ⟨hAJ₁, hJ ▸ hBJ₂⟩
    intro A hA B hB x hx y hy
    by_cases hAB : A = B
    · subst hAB
      obtain ⟨R, -, J, -, -, -, hcyc, -, -⟩ := hΩ.exists_data_of_mem_USet hp (h.1 hA).1
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      have hx' : x = (g : G) ^ m := by simpa using (congrArg Subtype.val hm).symm
      have hy' : y = (g : G) ^ n := by simpa using (congrArg Subtype.val hn).symm
      rw [hx', hy']
      exact (Commute.zpow_zpow_self (g : G) m n).eq
    · exact hdistinct A hA B hB hAB x hx y hy
  have hW : ∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x := by
    have h1 : ∀ B ∈ η, (⨆ U ∈ η, U) ≤ Subgroup.centralizer (B : Set G) := by
      intro B hB
      refine iSup₂_le fun A hA x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm A hA B hB x hx y hy).symm
    have h2 : (⨆ U ∈ η, U) ≤ Subgroup.centralizer ((⨆ U ∈ η, U : Subgroup G) : Set G) := by
      refine iSup₂_le fun B hB y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp (h1 B hB hx) y hy
      exact this.symm
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  refine ⟨hW, ?_⟩
  ext U
  constructor
  · rintro ⟨hU, hUW⟩
    have hWS : (⨆ V ∈ η, V) ≤ (S : Subgroup G) := iSup₂_le fun V hV => (h.1 hV).2
    obtain ⟨V, ⟨hVη, hV⟩, -⟩ := l6_8 p f hp hq G Ω hΩ S U hU (hUW.trans hWS) η
      ⟨S, h, hinv⟩ (fun V hV => (h.1 hV).2)
    rcases hV with rfl | hR
    · exact hVη
    · exfalso
      obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
      obtain ⟨x, hx, y, hy, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_not_commute
      have hVW : V ≤ ⨆ V ∈ η, V := le_iSup₂_of_le V hVη le_rfl
      have hle : U ⊔ V ≤ ⨆ V ∈ η, V := sup_le hUW hVW
      exact hxy (hW x (hle hx) y (hle hy))
  · intro hV
    exact ⟨(h.1 hV).1, le_iSup₂_of_le U hV le_rfl⟩

variable (p f)

theorem l6_9_of_l6_6ii (h : L6_6ii p f) : L6_9 p f := by
  intro hp hq G _ _ Ω hΩ S
  exact ⟨exists_invariant_mem_etaSet hp hq hΩ S,
    fun η hη hinv => eta_abelian_of_cyc66 hp hq hΩ (h hp hq G Ω hΩ) hη hinv⟩

theorem l6_9 (h : L6_6 p f) : L6_9 p f :=
  l6_9_of_l6_6ii p f (l6_6ii_of_l6_6 p f h)

@[expose] def L6_9AEmpty : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ K ∈ Ω, AEmpty Ω K) →
      ∀ S : Sylow 2 G,
        (∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
        ∀ η ∈ etaSet Ω (S : Subgroup G), (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) →
          (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
            {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η

theorem l6_9AEmpty (h : L6_6iiAEmpty p f) : L6_9AEmpty p f := by
  intro hp hq G _ _ Ω hΩ hA S
  exact ⟨exists_invariant_mem_etaSet hp hq hΩ S,
    fun η hη hinv => eta_abelian_of_cyc66 hp hq hΩ (h hp hq G Ω hΩ hA) hη hinv⟩

end CFSG.ClassicalInvolution.Asc77
