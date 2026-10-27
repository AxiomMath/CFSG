module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZProj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZL34
public import Certificates.Certificate2022
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInputs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.HeZ

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem not_le_of_four {C Q : Subgroup X} (hC : pRank 2 ↥C = 1)
    (hfour : ∃ y₁ ∈ Q, ∃ y₂ ∈ Q, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁) : ¬ Q ≤ C := by
  intro hQC
  obtain ⟨y₁, h₁, y₂, h₂, hy₁, hy₂, h1, h2, hne, hc⟩ := hfour
  exact false_of_pair hC (hQC h₁) (hQC h₂) hy₁ hy₂ h1 h2 hne hc

omit [Finite X] in
theorem normal_inf_centralizer {L Q : Subgroup X} (hQN : Q ≤ normalizer (L : Set X)) :
    ((Q ⊓ centralizer (L : Set X)).subgroupOf Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨hnQ, hnC⟩ := mem_inf.mp hn
  refine mem_inf.mpr ⟨mul_mem (mul_mem g.2 hnQ) (inv_mem g.2), ?_⟩
  exact (mem_normalizer_iff.mp (HeEnd.normalizer_le_normalizer_centralizer L (hQN g.2)) n).mp hnC

omit [Finite X] in
theorem exists_proj {L Q K : Subgroup X} (hZ : center ↥L = ⊥)
    (hOut : Group.IsSolvable (OuterAutomorphisms.Outer ↥L))
    (hQN : Q ≤ normalizer (L : Set X)) (hQp : ⁅Q, Q⁆ = Q) {u : X} (hu : u ∈ L)
    (hQu : Q ≤ centralizer ({u} : Set X))
    (hK : ∀ S : Subgroup X, S ≤ L ⊓ centralizer ({u} : Set X) → ⁅S, S⁆ = S → S ≤ K)
    {t : X} (htN : t ∈ normalizer (L : Set X)) (htQ : ∀ q ∈ Q, t * q = q * t) :
    ∃ P : Subgroup X, P ≤ K ∧ ⁅P, P⁆ = P ∧
      Nat.card P * Nat.card ↥(Q ⊓ centralizer (L : Set X)) = Nat.card Q ∧
      (∀ l ∈ P, t * l = l * t) ∧
      (∀ x : ↥Q, x ∈ (fstHom hZ (SeitzReduction.perfect_le_sup_centralizer hOut hQp hQN)).ker ↔
        (x : X) ∈ centralizer (L : Set X)) ∧
      Nonempty (↥Q ⧸ (fstHom hZ (SeitzReduction.perfect_le_sup_centralizer hOut hQp hQN)).ker ≃*
        ↥P) := by
  set hQLC := SeitzReduction.perfect_le_sup_centralizer hOut hQp hQN
  refine ⟨projL hZ hQLC, hK _ (le_inf (projL_le hZ hQLC)
    (projL_le_centralizer hZ hQLC hu hQu)) (projL_perfect hZ hQLC hQp), projL_perfect hZ hQLC hQp,
    card_projL_mul hZ hQLC, fun l hl => comm_of_mem_projL hZ hQLC htN htQ hl,
    mem_ker_fstHom_iff hZ hQLC, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivRange (fstHom hZ hQLC)).trans
    ((fstHom hZ hQLC).range.equivMapOfInjective L.subtype L.subtype_injective)

theorem comm_of_case_twoA {L Q K : Subgroup X}
    (hZ : center ↥L = ⊥) (hOut : Group.IsSolvable (OuterAutomorphisms.Outer ↥L))
    (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1)
    (hQN : Q ≤ normalizer (L : Set X)) (hQp : ⁅Q, Q⁆ = Q) {u : X} (hu : u ∈ L)
    (hQu : Q ≤ centralizer ({u} : Set X))
    (hKS : ∀ S : Subgroup X, S ≤ L ⊓ centralizer ({u} : Set X) → ⁅S, S⁆ = S → S ≤ K)
    (hKt : IsL34Type (↥K ⧸ center ↥K)) (hKp : ⁅K, K⁆ = K) (hKZ : Nat.card (center ↥K) = 4)
    (hQt : IsL34Type (↥Q ⧸ center ↥Q)) (hQZ : Nat.card (center ↥Q) = 4)
    (hQf : ∃ y₁ ∈ Q, ∃ y₂ ∈ Q, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁)
    {t : X} (htN : t ∈ normalizer (L : Set X)) (htQ : ∀ q ∈ Q, t * q = q * t) :
    ∀ k ∈ K, t * k = k * t := by
  obtain ⟨P, hPK, hPp, hcard, htP, -, -⟩ := exists_proj hZ hOut hQN hQp hu hQu hKS htN htQ
  have hsimp : IsSimpleGroup (↥Q ⧸ center ↥Q) := HeInner.isSimpleGroup_of_l34 hQt
  have hQperf : Group.IsPerfect ↥Q := isPerfect_iff.mpr hQp
  have hn := normal_inf_centralizer (L := L) hQN
  rcases Quasisimple.normal_le_center_or_eq_top ⟨hQperf.commutator_eq_top, hsimp⟩
      ((Q ⊓ centralizer (L : Set X)).subgroupOf Q) with h | h
  · have hle : Nat.card ↥(Q ⊓ centralizer (L : Set X)) ≤ 4 := by
      rw [← hQZ, ← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left :
        Q ⊓ centralizer (L : Set X) ≤ Q)).toEquiv]
      exact card_le_of_le h
    have hQcard : Nat.card Q = 80640 := by
      have h1 := card_eq_card_quotient_mul_card_subgroup (center ↥Q)
      rw [GSThmB.card_of_lieModel_L34 hQt, hQZ] at h1
      exact h1
    have hP : 20160 ≤ Nat.card P := by
      by_contra hlt
      simp only [not_le] at hlt
      have : Nat.card P * Nat.card ↥(Q ⊓ centralizer (L : Set X)) ≤ 20159 * 4 :=
        Nat.mul_le_mul (by omega) hle
      omega
    rw [← eq_of_card_ge hKt hKp hKZ hPK hPp hP]
    exact htP
  · exfalso
    apply not_le_of_four hrank hQf
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ (Q ⊓ centralizer (L : Set X)).subgroupOf Q := by rw [h]; exact mem_top _
    exact (mem_inf.mp (mem_subgroupOf.mp this)).2

theorem false_of_case_twoB {L Q K : Subgroup X} (hZ : center ↥L = ⊥)
    (hOut : Group.IsSolvable (OuterAutomorphisms.Outer ↥L))
    (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1)
    (hQN : Q ≤ normalizer (L : Set X)) (hQp : ⁅Q, Q⁆ = Q) {u : X} (hu : u ∈ L)
    (hQu : Q ≤ centralizer ({u} : Set X))
    (hKS : ∀ S : Subgroup X, S ≤ L ⊓ centralizer ({u} : Set X) → ⁅S, S⁆ = S → S ≤ K)
    (hKc : Nat.card K = 80640) (hQc : Nat.card Q = 21504)
    (hQn : ∀ N : Subgroup X, N ≤ Q → (N.subgroupOf Q).Normal → N ≠ Q → IsPGroup 2 N)
    (hQf : ∃ y₁ ∈ Q, ∃ y₂ ∈ Q, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁)
    (hSyl : ∀ T : Subgroup X, T ≤ Q → Nat.card T = 1024 →
      ∀ N : Subgroup X, N ≤ T → (N.subgroupOf T).Normal → 4 ≤ Nat.card N →
        ∃ y₁ ∈ N, ∃ y₂ ∈ N, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
          y₁ * y₂ = y₂ * y₁)
    {t : X} (htN : t ∈ normalizer (L : Set X)) (htQ : ∀ q ∈ Q, t * q = q * t) : False := by
  obtain ⟨P, hPK, -, hcard, -, -, -⟩ := exists_proj hZ hOut hQN hQp hu hQu hKS htN htQ
  set N := Q ⊓ centralizer (L : Set X) with hNdef
  have hPd : Nat.card P ∣ 5376 := by
    have h1 : Nat.card P ∣ 80640 := hKc ▸ card_dvd_of_le hPK
    have h2 : Nat.card P ∣ 21504 := hQc ▸ ⟨_, hcard.symm⟩
    have := Nat.dvd_gcd h1 h2
    simpa using this
  have hN4 : 4 ≤ Nat.card N := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hPd
    by_contra hlt
    simp only [not_le] at hlt
    have : Nat.card P * Nat.card N ≤ 5376 * 3 := Nat.mul_le_mul hle (by omega)
    omega
  have hNQ : N ≤ Q := inf_le_left
  have hNn := normal_inf_centralizer (L := L) hQN
  have hNne : N ≠ Q := fun h => not_le_of_four hrank hQf (h ▸ inf_le_right)
  have hN2 : IsPGroup 2 N := hQn N hNQ hNn hNne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Q) := inferInstance
  have hTc : Nat.card (T : Subgroup ↥Q) = 1024 := by
    rw [Sylow.card_eq_multiplicity, hQc]
    have : Nat.factorization 21504 2 = 10 := by
      rw [show (21504 : ℕ) = 2 ^ 10 * 21 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]
      simp
    rw [this]
    norm_num
  have hN' : (N.subgroupOf Q).Normal := hNn
  have hNT : N.subgroupOf Q ≤ T := by
    have h2 : IsPGroup 2 (N.subgroupOf Q) :=
      hN2.of_equiv (subgroupOfEquivOfLe hNQ).symm
    exact h2.le_sylow_of_normal T
  set T' : Subgroup X := (T : Subgroup ↥Q).map Q.subtype
  have hT'Q : T' ≤ Q := map_subtype_le _
  have hT'c : Nat.card T' = 1024 := by rw [card_map_of_injective Q.subtype_injective, hTc]
  have hNT' : N ≤ T' := by
    intro x hx
    exact ⟨⟨x, hNQ hx⟩, hNT (mem_subgroupOf.mpr hx), rfl⟩
  have hNTn : (N.subgroupOf T').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h := hNn.conj_mem ⟨n, hNQ hn⟩ (mem_subgroupOf.mpr hn) ⟨g, hT'Q g.2⟩
    exact mem_subgroupOf.mp h
  obtain ⟨y₁, h₁, y₂, h₂, hy₁, hy₂, h1, h2, hne, hc⟩ := hSyl T' hT'Q hT'c N hNT' hNTn hN4
  exact false_of_pair hrank (mem_inf.mp h₁).2 (mem_inf.mp h₂).2 hy₁ hy₂ h1 h2 hne hc

theorem false_of_case_outer {L Q K : Subgroup X}
    (hZ : center ↥L = ⊥) (hOut : Group.IsSolvable (OuterAutomorphisms.Outer ↥L))
    (hrank : pRank 2 ↥(centralizer (L : Set X)) = 1)
    (hQN : Q ≤ normalizer (L : Set X)) (hQp : ⁅Q, Q⁆ = Q) {u : X} (hu : u ∈ L)
    (hQu : Q ≤ centralizer ({u} : Set X))
    (hKS : ∀ S : Subgroup X, S ≤ L ⊓ centralizer ({u} : Set X) → ⁅S, S⁆ = S → S ≤ K)
    (hKt : IsL34Type (↥K ⧸ center ↥K)) (hKZ : Nat.card (center ↥K) = 4)
    (hKc : Nat.card K = 80640) (hQc : Nat.card Q = 7560) (hQZ : Nat.card (center ↥Q) = 3)
    (hQs : IsSimpleGroup (↥Q ⧸ center ↥Q))
    (hQf : ∃ y₁ ∈ Q, ∃ y₂ ∈ Q, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁)
    {t : X} (htN : t ∈ normalizer (L : Set X)) (htQ : ∀ q ∈ Q, t * q = q * t) : False := by
  obtain ⟨P, hPK, -, hcard, -, hker, ⟨eP⟩⟩ := exists_proj hZ hOut hQN hQp hu hQu hKS htN htQ
  set hQLC := SeitzReduction.perfect_le_sup_centralizer hOut hQp hQN
  have hQperf : Group.IsPerfect ↥Q := isPerfect_iff.mpr hQp
  have hn := normal_inf_centralizer (L := L) hQN
  have hkerEq : (fstHom hZ hQLC).ker = (Q ⊓ centralizer (L : Set X)).subgroupOf Q := by
    ext x
    rw [hker x, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rcases Quasisimple.normal_le_center_or_eq_top ⟨hQperf.commutator_eq_top, hQs⟩
      ((Q ⊓ centralizer (L : Set X)).subgroupOf Q) with h | h
  ·
    have hNc : Nat.card ↥((Q ⊓ centralizer (L : Set X)).subgroupOf Q) =
        Nat.card ↥(Q ⊓ centralizer (L : Set X)) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    have hd : Nat.card ↥(Q ⊓ centralizer (L : Set X)) ∣ 3 := by
      rw [← hNc, ← hQZ]
      exact card_dvd_of_le h
    have hPd : Nat.card P ∣ 80640 := hKc ▸ card_dvd_of_le hPK
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h3
    · rw [h1, mul_one, hQc] at hcard
      rw [hcard] at hPd
      norm_num at hPd
    ·
      have hNZ : (Q ⊓ centralizer (L : Set X)).subgroupOf Q = center ↥Q :=
        eq_of_le_of_card_ge h (by rw [hNc, h3, hQZ])
      have hPs : IsSimpleGroup ↥P := by
        have e : ↥Q ⧸ center ↥Q ≃* ↥P :=
          (QuotientGroup.quotientMulEquivOfEq (hkerEq.trans hNZ).symm).trans eP
        exact e.symm.isSimpleGroup
      have hPc : Nat.card P = 2520 := by
        rw [h3, hQc] at hcard
        omega
      exact false_of_simple_card_eq_2520 hKt hKZ hPK hPs hPc
  · apply not_le_of_four hrank hQf
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ (Q ⊓ centralizer (L : Set X)).subgroupOf Q := by rw [h]; exact mem_top _
    exact (mem_inf.mp (mem_subgroupOf.mp this)).2

end CFSG.ComponentClassification.GrSLit.HeZ
