module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem inner_subgroupOf_facts {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (X : Subgroup (MulAut S))
    (hX : (MulAut.conj : S →* MulAut S).range ≤ X) :
    ((MulAut.conj : S →* MulAut S).range.subgroupOf X).Normal ∧
      centralizer (((MulAut.conj : S →* MulAut S).range.subgroupOf X : Subgroup X) : Set X) = ⊥ ∧
      Nonempty (((MulAut.conj : S →* MulAut S).range.subgroupOf X) ≃* S) := by
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  have hN : Inn.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, mulAut_conj_map g s⟩⟩
  refine ⟨Subgroup.normal_subgroupOf, ?_, ⟨(subgroupOfEquivOfLe hX).trans
    (MonoidHom.ofInjective hκ).symm⟩⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  apply Subtype.ext
  ext s
  have h := mem_centralizer_iff.mp hσ ⟨MulAut.conj s, hX ⟨s, rfl⟩⟩
    (mem_subgroupOf.mpr ⟨s, rfl⟩)
  have h' : MulAut.conj ((σ : MulAut S) s) = MulAut.conj s := by
    rw [mulAut_conj_map]
    have h2 := congrArg Subtype.val h
    simp only [coe_mul] at h2
    rw [← h2, mul_inv_cancel_right]
  exact hκ h'

theorem hloc_of_coreFree {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (CFSG.generalizedFitting G) →
      (∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting G ≃* S) → ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (X : Subgroup (MulAut S)) (hX : (MulAut.conj : S →* MulAut S).range ≤ X) (z : X)
    (hz : orderOf z = 2) : pPrimeCore 2 ↥(centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨hN, hC, ⟨e⟩⟩ := inner_subgroupOf_facts hna X hX
  set N := (MulAut.conj : S →* MulAut S).range.subgroupOf X
  have : IsSimpleGroup N := e.isSimpleGroup
  have hnc : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hF := Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
    N hnc hC
  have : IsSimpleGroup (CFSG.generalizedFitting X) := by rw [hF]; infer_instance
  have hnc' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    rw [hF]
    exact hnc
  have h := hcore X this hnc' ⟨(MulEquiv.subgroupCongr hF).trans e⟩ z hz
  rwa [oddCore_eq_pPrimeCore_two] at h

theorem hbal_of_coreFree {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hcore : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (CFSG.generalizedFitting G) →
      (∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting G ≃* S) → ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (i : MulAut S) (hi : orderOf i = 2) :
    pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S))) = ⊥ := by
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  let e : S ≃* (MulAut.conj : S →* MulAut S).range := MonoidHom.ofInjective hκ
  have hF : CFSG.generalizedFitting (MulAut S) = (MulAut.conj : S →* MulAut S).range := by
    rw [generalizedFitting_eq_componentClassification]
    exact generalizedFitting_mulAut_eq_range hna
  have : IsSimpleGroup (MulAut.conj : S →* MulAut S).range := e.symm.isSimpleGroup
  have : IsSimpleGroup (CFSG.generalizedFitting (MulAut S)) := by rw [hF]; infer_instance
  have hnc' : ∃ a b : CFSG.generalizedFitting (MulAut S), a * b ≠ b * a := by
    rw [hF]
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have h := hcore (MulAut S) this hnc' ⟨(MulEquiv.subgroupCongr hF).trans e.symm⟩ i hi
  rwa [oddCore_eq_pPrimeCore_two] at h

theorem coreFree_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S]
    (θ : S ≃* Blueprint.NativeSporadic.Carrier s) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (CFSG.generalizedFitting G) →
      (∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting G ≃* S) → ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (centralizer ({t} : Set G)) = ⊥ :=
  fun G _ _ hF hnab ⟨e⟩ t ht => hs G hF hnab ⟨e.trans θ⟩ t ht

theorem sporadicOddCoreFree_J1 :
    CatalogueU.SporadicOddCoreFree .J1 := by
  intro G _ _ hF hnab ⟨e⟩ t ht
  have htop := CatalogueU.generalizedFitting_eq_top_of_J1 hF hnab e
  have eG : G ≃* Blueprint.NativeSporadic.J1 :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e
  exact (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨eG⟩ t ht).2.2.2

theorem coreFree_of_uBalanced (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {S : Type} [Group S] (hcat : Blueprint.Catalog S) (hbal : UBalanced S) :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (CFSG.generalizedFitting G) →
      (∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting G ≃* S) → ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (centralizer ({t} : Set G)) = ⊥ := by
  intro G _ _ hF hnab ⟨e⟩ t ht
  by_contra hne
  have hFG := generalizedFitting_eq_componentClassification G
  have hs : IsSimpleGroup (ComponentClassification.GeneralizedFitting.subgroup G) := by
    rw [← hFG]
    exact hF
  have hnc : ∃ a b : ComponentClassification.GeneralizedFitting.subgroup G, a * b ≠ b * a := by
    rw [← hFG]
    exact hnab
  let e' : ComponentClassification.GeneralizedFitting.subgroup G ≃* S :=
    (MulEquiv.subgroupCongr hFG.symm).trans e
  have hc : Blueprint.Catalog (ComponentClassification.GeneralizedFitting.subgroup G) :=
    SectionRank.catalog_of_mulEquiv e' hcat
  have hout := hU G hs hnc hc ⟨t, ht, hne⟩
  unfold OutcomeLocal.UOutcome at hout
  apply hbal
  rcases hout with h | ⟨n, hn, h7, ⟨e''⟩, -⟩ | ⟨h | ⟨⟨e''⟩⟩, -⟩
  · exact Or.inl ((ClassicalInvolution.oddLieType_congr e').1 h)
  · exact Or.inr (Or.inl ⟨n, hn, h7, ⟨e'.symm.trans e''⟩⟩)
  · exact Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e'.symm.symm h)))
  · exact Or.inr (Or.inr (Or.inr ⟨e'.symm.trans e''⟩))

theorem oddSubgroup_comm_of_card_le_eight {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G ≤ 8) (H : Subgroup G) (hH : Odd (Nat.card H)) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  have hle : Nat.card H ≤ 8 := (card_le_card_group H).trans hG
  have hcomm : ∀ a b : H, a * b = b * a := by
    have hcases : Nat.card H = 1 ∨ (Nat.card H).Prime := by
      obtain ⟨k, hk⟩ := hH
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
      · left; omega
      · right; rw [hk]; norm_num
      · right; rw [hk]; norm_num
      · right; rw [hk]; norm_num
    rcases hcases with h1 | hp
    · have : Subsingleton H := (Nat.card_eq_one_iff_unique.1 h1).1
      exact fun a b => Subsingleton.elim _ _
    · have : Fact (Nat.card H).Prime := ⟨hp⟩
      have : IsCyclic H := isCyclic_of_prime_card rfl
      exact fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b
  intro x hx y hy
  exact congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)

end CFSG.ComponentClassification.Foote5
