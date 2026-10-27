module

public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Tools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Cover

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem covers_subgroupOf_iff {F K : Subgroup X} (hFK : F ≤ K) :
    F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ ↔ F ⊔ pPrimeCoreOf 2 K = K := by
  have key : (F.subgroupOf K ⊔ pPrimeCore 2 ↥K).map K.subtype = F ⊔ pPrimeCoreOf 2 K := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hFK]
    rfl
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  constructor
  · intro h
    rw [← key, h, htop]
  · intro h
    apply Subgroup.map_injective K.subtype_injective
    rw [key, h, htop]

omit [Finite X] in
theorem isSubnormal_subgroupOf_of_normal_of_subnormal {H A B : Subgroup X} (hAH : A ≤ H)
    (hBA : B ≤ A) (hA : (A.subgroupOf H).IsSubnormal) (hB : (B.subgroupOf A).Normal) :
    (B.subgroupOf H).IsSubnormal := by
  have hBH : B.subgroupOf H ≤ A.subgroupOf H := Subgroup.subgroupOf_mono H hBA
  refine Subgroup.IsSubnormal.trans hBH ?_ hA
  let e : ↥(A.subgroupOf H) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAH
  have : (B.subgroupOf H).subgroupOf (A.subgroupOf H) =
      (B.subgroupOf A).comap e.toMonoidHom := by
    ext x
    rfl
  rw [this]
  exact hB.isSubnormal.comap _

theorem not_commutator_le_of_odd {E R : Subgroup X} (hq : IsTwoGenQuasi ↥E)
    (hR : Odd (Nat.card R)) : ¬ ⁅E, E⁆ ≤ R := by
  intro hle
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥E →* ↥E ⧸ pPrimeCore 2 ↥E := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hperf : ⁅(⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E)),
      (⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E))⁆ = ⊤ := by
    have := hq.2.1.1
    rwa [_root_.commutator_def] at this
  have hcomm : (⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map E.subtype = ⁅E, E⁆ := by
    have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [Subgroup.map_commutator, htop]
  have hS : ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ ≤ R.comap E.subtype := by
    intro c hc
    have hcE : (c : X) ∈ ⁅E, E⁆ := by
      rw [← hcomm]
      exact ⟨c, hc, rfl⟩
    exact hle hcE
  have hmap : (⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map π = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, hperf]
  have hmap2 : (R.comap E.subtype).map π = ⊤ :=
    top_le_iff.1 (hmap ▸ Subgroup.map_mono hS)
  have hdvd1 : Nat.card (↥E ⧸ pPrimeCore 2 ↥E) ∣ Nat.card (R.comap E.subtype) := by
    have := Subgroup.card_map_dvd (H := R.comap E.subtype) π
    rwa [hmap2, Subgroup.card_top] at this
  have hdvd2 : Nat.card (R.comap E.subtype) ∣ Nat.card R := by
    have h1 : Nat.card ((R.comap E.subtype).map E.subtype) = Nat.card (R.comap E.subtype) :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hcop : Nat.Coprime 2 (Nat.card (↥E ⧸ pPrimeCore 2 ↥E)) :=
    Nat.Coprime.coprime_dvd_right (hdvd1.trans hdvd2) (Nat.coprime_two_left.2 hR)
  have hbot : pPrimeCore 2 (↥E ⧸ pPrimeCore 2 ↥E) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have htop : (⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E)) = ⊥ :=
    (pPrimeCore_eq_bot_iff.1 hbot) ⊤ inferInstance (by rwa [Subgroup.card_top])
  have hnt : Nontrivial (↥E ⧸ pPrimeCore 2 ↥E) := CFSG.LocalCores.isQuasisimple_nontrivial hq.2
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥E ⧸ pPrimeCore 2 ↥E)
  have hxtop : x ∈ (⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E)) := Subgroup.mem_top x
  rw [htop, Subgroup.mem_bot] at hxtop
  exact hx hxtop

theorem isTwoGenQuasi_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) (hF : primeResidual 2 ↥F = ⊤)
    (hK : IsTwoGenQuasi ↥K) : IsTwoGenQuasi ↥F := by
  refine ⟨hF, ?_⟩
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hFK hcov
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hK.2

theorem isDoubleCoverOfAlt_quot_iff_of_covers {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) (n : ℕ) :
    IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n ↔ IsDoubleCoverOfAlt (↥K ⧸ pPrimeCore 2 ↥K) n := by
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hFK hcov
  exact ⟨CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e,
    CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e.symm⟩

theorem le_of_covers_of_normalized {L E K' : Subgroup X} (hEL : E ≤ L)
    (hcov : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤) (hL : primeResidual 2 ↥L = ⊤)
    (hE : E ≤ K') (hnorm : ∀ c ∈ L, c ∈ normalizer (K' : Set X)) : L ≤ K' := by
  have _ := hEL
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ primeResidual 2 ↥L := by rw [hL]; exact Subgroup.mem_top _
  rw [primeResidual_eq_closure] at hy'
  have hcl : Subgroup.closure {x : ↥L | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ K'.comap L.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    have hxk : x ^ (2 ^ k) = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hk] at this
    have hx : x ∈ E.subgroupOf L ⊔ pPrimeCore 2 ↥L := by
      rw [hcov]
      exact Subgroup.mem_top _
    obtain ⟨o, ho, a, ha, -, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd hodd hx hxk
    have haK : (a : X) ∈ K' := hE ha
    show (x : X) ∈ K'
    rw [hxa]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm o o.2) (a : X)).1 haK
  exact hcl hy'

end Cover

end CFSG.OddStandard.Solomon75
