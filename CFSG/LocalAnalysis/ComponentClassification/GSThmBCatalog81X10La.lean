module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Clu
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfB

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace X10

theorem pow_eq_of_odd {G : Type*} [Group G] {t o : G} (ht : t * t = 1) (hc : t * o = o * t)
    (hodd : Odd (orderOf o)) : (t * o) ^ orderOf o = t := by
  rw [(Commute.mul_pow hc (orderOf o)), pow_orderOf_eq_one, mul_one]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, pow_two, ht, one_pow, one_mul]

theorem exists_lift_SL2Comp {G : Type*} [Group G] [Finite G] {K : Type} [Field K] {t : G}
    (ht : t * t = 1) {E : Subgroup (G ⧸ pPrimeCore 2 G)}
    (hE : IsSL2Comp K (QuotientGroup.mk' (pPrimeCore 2 G) t) E) :
    ∃ M : Subgroup G, M ≤ centralizer {t} ∧ IsPComponent 2 (M.subgroupOf (centralizer {t})) ∧
      t ∈ M ∧ M.map (QuotientGroup.mk' (pPrimeCore 2 G)) = E ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 G) with hπ
  set X := centralizer ({t} : Set G) with hX
  obtain ⟨hEC, hEp, htE, hEO, ⟨eE⟩⟩ := hE
  have hXπ : centralizer ({π t} : Set (G ⧸ pPrimeCore 2 G)) = X.map π :=
    OddQuot.centralizer_singleton_map_eq ht
  set f := π.subgroupMap X with hf
  obtain ⟨hbij, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    f (π.subgroupMap_surjective X)
    (OddQuot.not_two_dvd_card_ker_subgroupMap π OddQuot.not_two_dvd_card_ker X)
  rw [hXπ] at hEC hEp
  obtain ⟨L, hL, hLE⟩ := hbij.surjOn (show E.subgroupOf (X.map π) ∈ {M | IsPComponent 2 M} from hEp)
  have hLE' : L.map f = E.subgroupOf (X.map π) := hLE
  set M := L.map X.subtype with hM
  have hMX : M ≤ X := map_subtype_le L
  have hML : M.subgroupOf X = L := by
    ext x
    rw [mem_subgroupOf, hM, mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨M, hMX, hML ▸ hL, ?_, ?_, ?_⟩
  ·
    have htX : π t ∈ X.map π := hEC htE
    have hmem : (⟨π t, htX⟩ : ↥(X.map π)) ∈ L.map f := by
      rw [hLE', mem_subgroupOf]
      exact htE
    obtain ⟨l, hlL, hlt⟩ := hmem
    have hπl : π (l : G) = π t := congrArg Subtype.val hlt
    have hlX : (l : G) ∈ X := l.2
    have hlc : (l : G) * t = t * l := mem_centralizer_singleton_iff.mp hlX
    obtain ⟨o, ho⟩ : ∃ o : G, o = t⁻¹ * (l : G) := ⟨_, rfl⟩
    have hoO : o ∈ pPrimeCore 2 G := by
      rw [ho, ← QuotientGroup.eq]
      exact hπl.symm
    have hto : t * o = o * t := by
      rw [ho]
      calc t * (t⁻¹ * (l : G)) = t⁻¹ * (t * (l : G)) := by group
        _ = t⁻¹ * ((l : G) * t) := by rw [← hlc]
        _ = t⁻¹ * (l : G) * t := by group
    have hl : (l : G) = t * o := by rw [ho, mul_inv_cancel_left]
    have hlM : (l : G) ∈ M := mem_map_of_mem _ hlL
    have hodd : Odd (orderOf o) := by
      have h1 := orderOf_dvd_natCard (⟨o, hoO⟩ : ↥(pPrimeCore 2 G))
      rw [Subgroup.orderOf_mk] at h1
      have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 G) :=
        (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := G))
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact fun h3 => h2 (h3.trans h1)
    rw [← pow_eq_of_odd ht hto hodd, ← hl]
    exact pow_mem hlM _
  ·
    rw [hM, Subgroup.map_map, ← OddQuot.subtype_comp_subgroupMap π X, ← Subgroup.map_map, hLE',
      subgroupOf_map_subtype, inf_eq_left.mpr hEC]
  ·
    obtain ⟨e₂, -⟩ := hiso L hL
    let e₁ : L ≃* M := L.equivMapOfInjective X.subtype X.subtype_injective
    have q₁ : M ⧸ pPrimeCore 2 M ≃* L ⧸ pPrimeCore 2 L :=
      (QuotientGroup.congr (pPrimeCore 2 L) (pPrimeCore 2 M) e₁ (pPrimeCore_map_iso 2 e₁)).symm
    let e₃ : ↥(L.map f) ≃* ↥(E.subgroupOf (X.map π)) := MulEquiv.subgroupCongr hLE
    have q₃ : ↥(L.map f) ⧸ pPrimeCore 2 ↥(L.map f) ≃*
        ↥(E.subgroupOf (X.map π)) ⧸ pPrimeCore 2 ↥(E.subgroupOf (X.map π)) :=
      QuotientGroup.congr _ _ e₃ (pPrimeCore_map_iso 2 e₃)
    let e₄ : ↥(E.subgroupOf (X.map π)) ≃* E := subgroupOfEquivOfLe hEC
    have q₄ : ↥(E.subgroupOf (X.map π)) ⧸ pPrimeCore 2 ↥(E.subgroupOf (X.map π)) ≃*
        E ⧸ pPrimeCore 2 E :=
      QuotientGroup.congr _ _ e₄ (pPrimeCore_map_iso 2 e₄)
    have q₅ : E ⧸ pPrimeCore 2 E ≃* E :=
      (QuotientGroup.quotientMulEquivOfEq hEO).trans QuotientGroup.quotientBot
    exact ⟨((((q₁.trans e₂).trans q₃).trans q₄).trans q₅).trans eE⟩

end X10

end CFSG.ComponentClassification.GSThmB
