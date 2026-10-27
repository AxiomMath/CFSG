module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGBase
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.ComponentClassification.FooteLit

theorem card_support_of_even_involution {n : ℕ} {σ : Equiv.Perm (Fin n)} (h2 : orderOf σ = 2)
    (hs : Equiv.Perm.sign σ = 1) : ∃ k, 1 ≤ k ∧ σ.support.card = 4 * k := by
  have hct : ∀ i ∈ σ.cycleType, i = 2 := fun i hi =>
    le_antisymm (Nat.le_of_dvd (by norm_num) (h2 ▸ Equiv.Perm.dvd_of_mem_cycleType hi))
      (Equiv.Perm.two_le_of_mem_cycleType hi)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hct⟩
  have hsum : σ.support.card = 2 * Multiset.card σ.cycleType := by
    rw [← Equiv.Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul,
      Multiset.card_replicate, mul_comm]
  have hc : Even (Multiset.card σ.cycleType) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsign := Equiv.Perm.sign_of_cycleType σ
    rw [hs, Equiv.Perm.sum_cycleType, hsum] at hsign
    have hodd' : Odd (2 * Multiset.card σ.cycleType + Multiset.card σ.cycleType) := by
      obtain ⟨j, hj⟩ := hodd
      exact ⟨3 * j + 1, by omega⟩
    rw [hodd'.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hc1 : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have h1 : σ = 1 := Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h0)
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨k, hk⟩ := hc
  exact ⟨k, by omega, by rw [hsum, hk]; ring⟩

open scoped Classical in
theorem footeComponent_alt {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n ≤ 11)
    (e : G ≃* alternatingGroup (Fin n)) {L : Subgroup G} {t : G} (ht : IsTwoComponentAt t L) :
    9 ≤ n ∧ Nonempty (L ≃* alternatingGroup (Fin (n - 4))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, hLC, hLp⟩ := ht
  set K := alternatingGroup (Fin n) with hK
  set t' : K := e t with ht'
  have ht'2 : orderOf t' = 2 := by rw [ht', MulEquiv.orderOf_eq]; exact ht2
  set P : Subgroup K := zpowers t' with hPdef
  have hP : IsPGroup 2 P := LocalAnalysis.ComponentInitial.isPGroup_zpowers_of_orderOf_eq_two ht'2
  have hC : (centralizer ({t} : Set G)).map e.toMonoidHom = centralizer ({t'} : Set K) := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg e h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    · intro h
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h
  have hN := LocalAnalysis.ComponentInitial.centralizer_singleton_eq_normalizer_zpowers ht'2
  let φ : centralizer ({t} : Set G) ≃* normalizer (P : Set K) :=
    (e.subgroupMap _).trans ((MulEquiv.subgroupCongr hC).trans (MulEquiv.subgroupCongr hN))
  set L' := (L.subgroupOf (centralizer ({t} : Set G))).map φ.toMonoidHom with hL'def
  have hL' : IsPComponent 2 L' := CatalogueBAlternating.pComponent_map_equiv 2 φ _ hLp
  obtain ⟨h5, heq, -⟩ :=
    CatalogueBAlternating.between_normalizer_pComponent K le_rfl 2 P hP L' hL'
  set σ : Equiv.Perm (Fin n) := (t' : Equiv.Perm (Fin n)) with hσ
  have hfix : ∀ x : Fin n, x ∈ MulAction.fixedPoints P (Fin n) ↔ σ x = x := by
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨t', mem_zpowers t'⟩
    · rintro h ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
      change ((t' ^ k : K) : Equiv.Perm (Fin n)) x = x
      rw [SubgroupClass.coe_zpow]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k
  have hcard : Nat.card (MulAction.fixedPoints P (Fin n)) = n - σ.support.card := by
    have h1 : MulAction.fixedPoints P (Fin n) = ((σ.supportᶜ : Finset (Fin n)) : Set (Fin n)) := by
      ext x
      rw [hfix x]
      simp [Equiv.Perm.mem_support]
    rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_compl, Fintype.card_fin]
  have hσ2 : orderOf σ = 2 := by
    rw [hσ, Subgroup.orderOf_coe, ht'2]
  obtain ⟨k, hk1, hk⟩ := card_support_of_even_involution hσ2
    (Equiv.Perm.mem_alternatingGroup.mp t'.2)
  have hsupp : σ.support.card ≤ n := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  rw [hcard, hk] at h5
  have hk' : k = 1 := by omega
  have hF : Nat.card (MulAction.fixedPoints P (Fin n)) = n - 4 := by rw [hcard, hk, hk']
  refine ⟨by omega, ⟨?_⟩⟩
  have hinj : Function.Injective (K.subtype.comp (normalizer (P : Set K)).subtype) :=
    K.subtype_injective.comp (normalizer (P : Set K)).subtype_injective
  have e₁ : L ≃* L' := (subgroupOfEquivOfLe hLC).symm.trans
    ((L.subgroupOf (centralizer ({t} : Set G))).equivMapOfInjective φ.toMonoidHom φ.injective)
  have e₂ : L' ≃* (alternatingGroup (MulAction.fixedPoints P (Fin n))).map
      Equiv.Perm.ofSubtype :=
    (L'.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr heq)
  have e₃ := ((alternatingGroup (MulAction.fixedPoints P (Fin n))).equivMapOfInjective
    Equiv.Perm.ofSubtype Equiv.Perm.ofSubtype_injective).symm
  have e₄ : alternatingGroup (MulAction.fixedPoints P (Fin n)) ≃* alternatingGroup (Fin (n - 4)) :=
    Equiv.altCongrHom ((Finite.equivFin _).trans (finCongr hF))
  exact ((e₁.trans e₂).trans e₃).trans e₄

theorem footeKnownQuot_alt {n m : ℕ} (hn : n ≤ 11) (hn9 : 9 ≤ n) (hm : m = n - 4) (G : Type)
    [Group G] [Finite G] (hG : Nonempty (G ≃* alternatingGroup (Fin n))) : FooteKnownQuot G m := by
  intro L hL
  obtain ⟨e⟩ := hG
  obtain ⟨t, ht⟩ := hL.1
  obtain ⟨-, ⟨f⟩⟩ := footeComponent_alt hn e ht
  subst hm
  exact nonempty_quot_pPrimeCore_of_mulEquiv (by omega) f

theorem footeKnownQuot_alt9 (G : Type) [Group G] [Finite G]
    (hG : Nonempty (G ≃* alternatingGroup (Fin 9))) : FooteKnownQuot G 5 :=
  footeKnownQuot_alt (by norm_num) (by norm_num) rfl G hG

theorem footeKnownQuot_alt10 (G : Type) [Group G] [Finite G]
    (hG : Nonempty (G ≃* alternatingGroup (Fin 10))) : FooteKnownQuot G 6 :=
  footeKnownQuot_alt (by norm_num) (by norm_num) rfl G hG

theorem footeKnownQuot_alt11 (G : Type) [Group G] [Finite G]
    (hG : Nonempty (G ≃* alternatingGroup (Fin 11))) : FooteKnownQuot G 7 :=
  footeKnownQuot_alt (by norm_num) (by norm_num) rfl G hG

theorem noFooteComponent_alt8 (G : Type) [Group G] [Finite G]
    (hG : Nonempty (G ≃* alternatingGroup (Fin 8))) : NoFooteComponent G := by
  intro L hL
  obtain ⟨e⟩ := hG
  obtain ⟨t, ht⟩ := hL.1
  have h := (footeComponent_alt (by norm_num) e ht).1
  omega

end CFSG.ComponentClassification.FooteLit.KG
