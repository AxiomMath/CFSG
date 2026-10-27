module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bInner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

theorem mem_center_of_commutator_mem_center {G : Type*} [Group G] [Group.IsPerfect G] {a : G}
    (h : ∀ m : G, ⁅a, m⁆ ∈ center G) : a ∈ center G := by
  have hc : (QuotientGroup.mk a : G ⧸ center G) ∈ center (G ⧸ center G) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : (QuotientGroup.mk' (center G)) ⁅a, m⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (h m)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [Group.IsPerfect.center_quotient_center_eq_bot G, mem_bot] at hc
  exact (QuotientGroup.eq_one_iff a).1 hc

variable {X : Type} [Group X] [Finite X]

theorem map_isPComponent_centralizer {S : Type} [Group S] [Finite S] (π : X →* S)
    (hπ : Function.Surjective π) (hker : π.ker = center X) {t : X} {L : Subgroup X}
    (hL : IsTwoComponentIn L (centralizer {t})) :
    L.map π ≤ centralizer {π t} ∧ IsPComponent 2 ((L.map π).subgroupOf (centralizer {π t})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  have hLt : L ≤ centralizer {t} := hL.1
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer {t})) := (isTwoComponentIn_iff hLt).mp hL
  have hcent : ∀ {x : X}, x ∈ centralizer ({t} : Set X) → π x ∈ centralizer ({π t} : Set S) :=
    fun {x} hx => by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, hx, map_mul]
  have hRv : L.map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent (hLt hx)
  have hH₁v : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent hx
  let πH : ↥(centralizer ({t} : Set X)) →* ↥((centralizer ({t} : Set X)).map π) :=
    (π.comp (centralizer ({t} : Set X)).subtype).codRestrict _ fun h => ⟨h, h.2, rfl⟩
  have hπHs : Function.Surjective πH := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have hπHc : πH.ker ≤ center ↥(centralizer ({t} : Set X)) := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 hx' y)
  have hR₁ : IsPComponent 2 ((L.map π).subgroupOf ((centralizer {t}).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 πH hπHs hπHc
      (L.subgroupOf (centralizer {t})) hLc
    have heq : (L.subgroupOf (centralizer {t})).map πH =
        (L.map π).subgroupOf ((centralizer {t}).map π) := by
      ext ⟨y, hy⟩
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨⟨x, hxH⟩, hxL, hxy⟩
        exact ⟨x, hxL, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hxL, rfl⟩
        exact ⟨⟨x, hLt hxL⟩, hxL, rfl⟩
    rwa [heq] at h
  exact ⟨hRv, UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (map_mono hLt) hH₁v
    (normal_map_centralizer_of_ker π hπ hker t).isSubnormal hR₁⟩

theorem nonempty_coreQuot_map_psl2 (hX : IsQuasisimple X) {S : Type} [Group S] [Finite S]
    (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = center X) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) :
    Nonempty (↥(Q.map π) ⧸ pPrimeCore 2 ↥(Q.map π) ≃* PSL(2, GaloisField p k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hsimple : IsSimpleGroup PSL(2, GaloisField p k) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 (GaloisField p k) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  obtain ⟨-, -, hRv, hRc, N, hN, hNodd, ⟨eN⟩⟩ := exists_psl2_component hX π hπ hker hp2 hcfg
  let eJ : ↥((Q.map π).subgroupOf (centralizer {π t})) ≃* ↥(Q.map π) :=
    Subgroup.subgroupOfEquivOfLe hRv
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1
    hRc
  have hqR : IsQuasisimple (↥(Q.map π) ⧸ pPrimeCore 2 ↥(Q.map π)) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hq
  have hO : pPrimeCore 2 ↥(Q.map π) = N :=
    pPrimeCore_eq_of_quotient hNodd eN (LocalCores.isQuasisimple_nontrivial hqR)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans eN⟩

theorem nonempty_fusionZStar_equiv_map {S : Type*} [Group S] (π : X →* S)
    (hker : π.ker ≤ center X) {L : Subgroup X} (hperf : Group.IsPerfect L)
    (hq : IsQuasisimple (L.map π)) (h2 : 2 ∣ Nat.card (L.map π)) :
    Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* ↥(L.map π) ⧸ center ↥(L.map π)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := π.subgroupMap L with hψ
  have hψs : Function.Surjective ψ := MonoidHom.subgroupMap_surjective π L
  set φ := (QuotientGroup.mk' (center ↥(L.map π))).comp ψ with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψs
  have : Group.IsPerfect (L.map π) := hq.1
  have hφk : Open.fusionZStar ↥L = φ.ker := by
    ext l
    rw [GSThmB.OddQuot.mem_fusionZStar_iff, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have hOc : (pPrimeCore 2 ↥L).map ψ ≤ center ↥(L.map π) := by
        have : ((pPrimeCore 2 ↥L).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
        rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
          ((pPrimeCore 2 ↥L).map ψ) with h' | h'
        · exact h'
        · exfalso
          have hodd : Odd (Nat.card ((pPrimeCore 2 ↥L).map ψ)) :=
            Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
              (Subgroup.card_map_dvd _ _)
          rw [h', Subgroup.card_top] at hodd
          exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
      refine mem_center_of_commutator_mem_center fun m => ?_
      obtain ⟨m', rfl⟩ := hψs m
      rw [← map_commutatorElement]
      exact hOc (mem_map_of_mem ψ (h m'))
    · intro h m
      have hl : l ∈ center ↥L := by
        refine mem_center_of_commutator_mem_center fun m => ?_
        have h1 : ψ ⁅l, m⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact (mem_center_iff.1 h (ψ m)).symm
        have h1' : ((⁅l, m⁆ : L) : X) ∈ center X := hker (by
          change π _ = 1
          exact congrArg Subtype.val h1)
        rw [mem_center_iff]
        intro y
        exact Subtype.ext (mem_center_iff.1 h1' y)
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hl m).symm]
      exact one_mem _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφk).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hφs)⟩

theorem comps_of_config (hX : IsQuasisimple X) {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {c t : X} {Q L : Subgroup X} (hcfg : Lemma58bConfig X p k c t Q)
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L)
    {P : Type} [Group P] [Finite P] (θ : X ⧸ center X ≃* P) :
    θ (QuotientGroup.mk t) * θ (QuotientGroup.mk t) = 1 ∧ θ (QuotientGroup.mk t) ≠ 1 ∧
    ∃ R₁ R₂ : Subgroup P,
      R₁ ≤ centralizer {θ (QuotientGroup.mk t)} ∧
      IsPComponent 2 (R₁.subgroupOf (centralizer {θ (QuotientGroup.mk t)})) ∧
      Nonempty (↥R₁ ⧸ pPrimeCore 2 ↥R₁ ≃* PSL(2, GaloisField p k)) ∧
      R₂ ≤ centralizer {θ (QuotientGroup.mk t)} ∧
      IsPComponent 2 (R₂.subgroupOf (centralizer {θ (QuotientGroup.mk t)})) ∧
      θ (QuotientGroup.mk t) ∈ R₂ ∧
      (IsQuasisimple R₂ → Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* ↥R₂ ⧸ center ↥R₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center X) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨hxx, hx1, hRv, hRc, -⟩ := exists_psl2_component hX π hπ hker hp2 hcfg
  obtain ⟨hLv, hLc⟩ := map_isPComponent_centralizer π hπ hker hL
  obtain ⟨e₁⟩ := nonempty_coreQuot_map_psl2 hX π hπ hker hp2 hcfg
  obtain ⟨h₁H, h₁⟩ := P51e.Comp.comp_map_mulEquiv θ hRv hRc
  obtain ⟨h₂H, h₂⟩ := P51e.Comp.comp_map_mulEquiv θ hLv hLc
  let eQ := (Q.map π).equivMapOfInjective θ.toMonoidHom θ.injective
  let eL := (L.map π).equivMapOfInjective θ.toMonoidHom θ.injective
  refine ⟨by rw [← map_mul]; exact (map_eq_one_iff θ θ.injective).2 hxx,
    fun h => hx1 (θ.injective (h.trans (map_one θ).symm)), _, _, h₁H, h₁,
    ⟨(QuotientGroup.congr _ _ eQ.symm (pPrimeCore_map_iso 2 eQ.symm)).trans e₁⟩, h₂H, h₂,
    mem_map_of_mem _ (mem_map_of_mem π htL), fun hq => ?_⟩
  have hq' : IsQuasisimple (L.map π) := LocalCores.isQuasisimple_of_mulEquiv eL.symm hq
  have h2 : 2 ∣ Nat.card (L.map π) := by
    have hmem : π t ∈ L.map π := mem_map_of_mem π htL
    have hord : orderOf (⟨π t, hmem⟩ : L.map π) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
    rw [← hord]
    exact orderOf_dvd_natCard _
  obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_map π hker.le hL.2.2.1 hq' h2
  exact ⟨eZ.trans (Sol78.centerQuotCongr eL)⟩

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
