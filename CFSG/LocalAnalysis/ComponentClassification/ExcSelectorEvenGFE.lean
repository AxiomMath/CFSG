module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenField
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenRee
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K]

theorem card_fixSubfield_of_pow [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ e) : Nat.card (fixSubfield σ) = 2 ^ e := by
  have h2e : 2 ≤ 2 * e := by omega
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, hσ1, -⟩ :=
    UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed h2e ⟨e, two_mul e⟩ hK hσ'
  obtain ⟨-, hcard⟩ := card_fixSubfield_of_sq (by omega) hK (by rw [sq]; exact hσσ) hσ1
  rwa [show 2 * e / 2 = e by omega] at hcard

theorem smallType_iff_of_normal {C G : Type} [Group C] [Group G] {J K' : Subgroup C}
    (hKJ : K' ≤ J) (e : J ≃* G) :
    SmallType K' ↔ SmallType ((K'.subgroupOf J).map e.toMonoidHom) := by
  have e₁ : K' ≃* (K'.subgroupOf J) := (Subgroup.subgroupOfEquivOfLe hKJ).symm
  exact (smallType_congr e₁).trans (smallType_congr (e.subgroupMap _))

theorem normal_map_of_equiv {J G : Type*} [Group J] [Group G] (e : J ≃* G) {N : Subgroup J}
    (hN : N.Normal) : (N.map e.toMonoidHom).Normal :=
  Subgroup.Normal.map hN _ e.surjective

theorem even_field_noSmall [Finite K] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {γ : MulAut (adjointGroup τ K)}
    (hγ : ∀ u, (γ u : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K))
    {L : Subgroup (adjointGroup τ K)} (hL : Assembly.IsComponentOf L (fixedSubgroup γ))
    (hLn : (L.subgroupOf (fixedSubgroup γ)).Normal) : ¬ SmallType L := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hk := card_fixSubfield_of_pow he hK hσ
  have hfix := fixedSubgroup_eq_fixedFieldImage_even (by
    rcases hτ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) hchar σ hγ
  rcases hτ with rfl | rfl | rfl | rfl
  · rcases Nat.lt_or_ge e 2 with he2 | he2
    ·
      have he1 : e = 1 := by omega
      subst he1
      have hJC : fixedFieldImage .G2 σ ≤ adjointGroup .G2 K := fun x hx =>
        (fixedFieldImage_le hx).1
      set J := (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) with hJ
      have eJ : J ≃* adjointGroup .G2 (fixSubfield σ) :=
        (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm
      rw [hfix] at hL hLn
      rw [smallType_iff_of_normal hL.1 eJ]
      have : ((L.subgroupOf J).map eJ.toMonoidHom).Normal := normal_map_of_equiv eJ hLn
      exact not_smallType_of_normal_G2_two (by rw [hk]; norm_num) _
    · obtain ⟨hs, hn⟩ := adjointGroup_G2_even (by omega) hk he2
      exact not_smallType_of_fixedFieldImage σ hfix hs hn hL
  · obtain ⟨hs, hn⟩ := adjointGroup_F4_even he hk
    exact not_smallType_of_fixedFieldImage σ hfix hs hn hL
  · obtain ⟨hs, hn⟩ := adjointGroup_E7_even he hk
    exact not_smallType_of_fixedFieldImage σ hfix hs hn hL
  · obtain ⟨hs, hn⟩ := adjointGroup_E8_even he hk
    exact not_smallType_of_fixedFieldImage σ hfix hs hn hL

@[expose] def ringEquivOfFinite [Finite K] (δ : K →+* K) : K ≃+* K :=
  RingEquiv.ofBijective δ δ.injective.bijective_of_finite

theorem ringEquivOfFinite_apply [Finite K] (δ : K →+* K) (c : K) :
    ringEquivOfFinite δ c = δ c := rfl

theorem toRingHom_ringEquivOfFinite [Finite K] (δ : K →+* K) :
    (ringEquivOfFinite δ).toRingHom = δ := RingHom.ext fun _ => rfl

theorem even_GFE_noSmall [Finite K] {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (β : MulAut (adjointGroup τ K)) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    {L : Subgroup (adjointGroup τ K)} (hL : Assembly.IsComponentOf L (fixedSubgroup β))
    (hLn : (L.subgroupOf (fixedSubgroup β)).Normal) : ¬ SmallType L := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  by_cases hin : β ∈ inner (adjointGroup τ K)
  · obtain ⟨c, rfl⟩ := hin
    have hc1 : c ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hc2 : c ^ 2 = 1 := by
      apply mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
      rw [map_pow, hβ2, map_one]
    exact absurd hL (not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.ordinary τ) hc1 hc2 L)
  rcases hτ with rfl | rfl | hτ
  ·
    rcases UnbalancedCatalog.even_G2_involution_inner_or_canonical_field (hG2 rfl) K hK β
        (orderOf_eq_prime hβ2 hβ1) with h | ⟨⟨e, he⟩, hδ⟩
    · exact absurd h hin
    have he1 : 1 ≤ e := by have := hG2 rfl; omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    set δ := iterateFrobenius K 2 (f / 2) with hδdef
    have hδc : ∀ c, δ c = c ^ 2 ^ (f / 2) := fun c => iterateFrobenius_def 2 (f / 2) c
    obtain ⟨β', ψ, hβ', hψ, -⟩ := hδ δ hδc
    set σ := ringEquivOfFinite δ
    have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [ringEquivOfFinite_apply, hδc, show f / 2 = e by omega]
    refine not_smallType_of_conj hψ (fun L' hL' hL'n => ?_) hL hLn
    exact even_field_noSmall (Or.inl rfl) he1 hK' σ hσ
      (fun u => by rw [hβ' u, toRingHom_ringEquivOfFinite]) hL' hL'n
  ·
    have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨ψ, hψ, heven, hodd, -⟩ := even_F4_all_outer_involutions_canonical hf K hK β hβ2 hin
    refine not_smallType_of_conj hψ (fun L' hL' hL'n => ?_) hL hLn
    obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' f
    ·
      have hn1 : 1 ≤ n := by omega
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, hn]
      set δ := iterateFrobenius K 2 n
      have hδc : ∀ c, δ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
      set σ := ringEquivOfFinite δ
      exact even_field_noSmall (τ := .F4) (Or.inr (Or.inl rfl)) hn1 hK' σ
        (fun c => by rw [ringEquivOfFinite_apply, hδc])
        (fun u => by
          have h := (heven n hn).2 δ hδc u
          rw [toRingHom_ringEquivOfFinite]
          exact h) hL' hL'n
    ·
      have hK' : Nat.card K = 2 ^ (2 * n + 1) := by rw [hK, hn]
      rw [(hodd n hn).1, fixedSubgroup_finiteReeAut] at hL'
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · exact not_smallType_of_isComponentOf_reeFixed_tits (by rw [hK']; norm_num) hL'
      · obtain ⟨hs, hns⟩ := reeFixed_F4_simple_not_smallType hn1 hK'
        rwa [eq_of_isComponentOf_of_isSimpleGroup hL']
  ·
    obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF β
    have hσ : Θ β = σ := hΘ β g σ hgσ
    rcases hinv β hβ2 with h1 | ⟨⟨e, he⟩, hpow⟩
    · have hker' : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at hker'
      exact absurd hker' hin
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [← hσ, hpow c, show f / 2 = e by omega]
    obtain ⟨_, -, hdesc⟩ :=
      (even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom
        hσe).1 τ
    obtain ⟨ψ, hψ, -⟩ := (hdesc g 1).2 β
      (fun u => by rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hβ2])
    refine not_smallType_of_conj (ψ := ψ) (γ := ψ * β * ψ⁻¹) rfl
      (fun L' hL' hL'n => ?_) hL hLn
    rcases hτ with rfl | rfl
    · exact even_field_noSmall (Or.inr (Or.inr (Or.inl rfl))) he1 hK' σ hσe hψ hL' hL'n
    · exact even_field_noSmall (Or.inr (Or.inr (Or.inr rfl))) he1 hK' σ hσe hψ hL' hL'n

end CFSG.ComponentClassification.ExcSelector
