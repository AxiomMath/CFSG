module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitIsoTransport
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Inner

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem seven_le_of_alternating {n : ℕ} (θ : ↥(generalizedFitting G) ≃* alternatingGroup (Fin n))
    {L : Subgroup G} (hLN : L ≤ generalizedFitting G)
    (e7 : GSThmB.OddBar L ≃* alternatingGroup (Fin 7)) : 7 ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card ↥L ≤ Nat.card ↥(generalizedFitting G) := Subgroup.card_le_of_le hLN
  have h2 : Nat.card (GSThmB.OddBar L) ≤ Nat.card ↥L :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [Nat.card_congr e7.toEquiv, nat_card_alternating_seven] at h2
  have h3 : Nat.card ↥(generalizedFitting G) ≤ n.factorial := by
    rw [Nat.card_congr θ.toEquiv]
    calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Subgroup.card_le_card_group _
      _ = n.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h4 : n.factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
  have h5 : (6 : ℕ).factorial = 720 := by decide
  omega

theorem eq_nine_of_alternating (hF : IsSimpleGroup ↥(generalizedFitting G)) {n : ℕ}
    (θ : ↥(generalizedFitting G) ≃* alternatingGroup (Fin n)) {t : G} (ht : orderOf t = 2)
    (htF : t ∉ generalizedFitting G) {L : Subgroup G} (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7)))
    (hcyc : ∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) :
    n = 9 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := h7
  have hnab := generalizedFitting_nonabelian hF ⟨e7⟩
  have hLN := le_generalizedFitting hF hnab ht hLt hL
  have hn7 := seven_le_of_alternating θ hLN e7
  have hFeq := CFSG.generalizedFitting_eq_componentClassification G
  have : IsSimpleGroup ↥(GeneralizedFitting.subgroup G) := hFeq ▸ hF
  have hnab' : ∃ a b : ↥(GeneralizedFitting.subgroup G), a * b ≠ b * a := hFeq ▸ hnab
  let θ' : ↥(GeneralizedFitting.subgroup G) ≃* alternatingGroup (Fin n) :=
    (MulEquiv.subgroupCongr hFeq.symm).trans θ
  obtain ⟨K, hAK, e, he⟩ :=
    CatalogueBAlternating.generalizedFitting_between_alternating_symmetric hnab' (Or.inr hn7) θ'
  have hσA : ((e t : K) : Equiv.Perm (Fin n)) ∉ alternatingGroup (Fin n) := by
    intro hσ
    obtain ⟨f, hf⟩ := θ'.surjective ⟨_, hσ⟩
    have h1 : e f.val = e t := Subtype.ext (by rw [he f, hf])
    apply htF
    rw [← e.injective h1, hFeq]
    exact f.2
  have hKtop : K = ⊤ := eq_top_of_alternating_le hAK (e t).2 hσA
  let e' : G ≃* Equiv.Perm (Fin n) :=
    (e.trans (MulEquiv.subgroupCongr hKtop)).trans Subgroup.topEquiv
  set σ : Equiv.Perm (Fin n) := e' t with hσ
  have hσo : orderOf σ = 2 := by rw [hσ, MulEquiv.orderOf_eq, ht]
  set L' : Subgroup (Equiv.Perm (Fin n)) := L.map e'.toMonoidHom with hL'
  have hL'C : L' ≤ centralizer ({σ} : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hLt hx)
    simp only [MulEquiv.coe_toMonoidHom, hσ]
    rw [← map_mul, ← map_mul, h1]
  have hL'p := FooteLit.isPComponent_map_centralizer e' hLt hL
  set P : Subgroup (Equiv.Perm (Fin n)) := zpowers σ with hP
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσo, pow_one])
  have hNC := normalizer_zpowers_eq_centralizer hσo
  have hL'N : L' ≤ normalizer (P : Set (Equiv.Perm (Fin n))) := by rw [hNC]; exact hL'C
  have hL'pN : IsPComponent 2 (L'.subgroupOf (normalizer (P : Set (Equiv.Perm (Fin n))))) := by
    rw [hNC]
    exact hL'p
  obtain ⟨h5, hEq, -⟩ :=
    CatalogueBAlternating.symmetric_normalizer_pComponent 2 P hP2 _ hL'pN
  let eL : ↥L ≃* ↥(alternatingGroup ↥(MulAction.fixedPoints P (Fin n))) :=
    (((L.equivMapOfInjective e'.toMonoidHom e'.injective).trans
      (subgroupOfEquivOfLe hL'N).symm).trans (MulEquiv.subgroupCongr hEq)).trans
      ((alternatingGroup _).equivMapOfInjective _
        (CatalogueBAlternating.fixedPointsNormalizerHom_injective P)).symm
  have : IsSimpleGroup ↥(alternatingGroup ↥(MulAction.fixedPoints P (Fin n))) :=
    alternatingGroup.isSimpleGroup h5
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hO : pPrimeCore 2 ↥L = ⊥ := by
    have : (pPrimeCore 2 ↥L).Normal := pPrimeCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥L) with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (GSThmB.OddBar L) = 1 := by
        unfold GSThmB.OddBar
        rw [h]
        exact Subgroup.index_top
      rw [Nat.card_congr e7.toEquiv, nat_card_alternating_seven] at h1
      omega
  have hfix : Nat.card ↥(MulAction.fixedPoints P (Fin n)) = 7 := by
    let e8 : alternatingGroup (Fin 7) ≃* alternatingGroup ↥(MulAction.fixedPoints P (Fin n)) :=
      e7.symm.trans (((QuotientGroup.quotientMulEquivOfEq hO).trans
        QuotientGroup.quotientBot).trans eL)
    have h1 := Nat.card_congr e8.toEquiv
    have : Nontrivial ↥(MulAction.fixedPoints P (Fin n)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternating_seven, nat_card_alternatingGroup] at h1
    set m := Nat.card ↥(MulAction.fixedPoints P (Fin n))
    by_contra hm
    rcases Nat.lt_or_ge m 8 with h8 | h8
    · interval_cases m <;> simp_all [Nat.factorial]
    · have h9 : (8 : ℕ).factorial ≤ m.factorial := Nat.factorial_le h8
      have h10 : (8 : ℕ).factorial = 40320 := by decide
      omega
  have hsum : Nat.card ↥(MulAction.fixedPoints P (Fin n)) + σ.support.card = n :=
    card_fixedPoints_add_card_support σ
  have hsupp : σ.support.card < 4 := by
    by_contra h4
    push Not at h4
    exact false_of_support_ge_four hcyc e' hL'N hL'pN hP2 h4
  have hne : σ.support.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at h0
    rw [h0, orderOf_one] at hσo
    exact absurd hσo (by decide)
  have hev : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support (by
    rw [← hσo]; exact pow_orderOf_eq_one σ)
  omega

end CFSG.ComponentClassification.HSFLit.HS7
