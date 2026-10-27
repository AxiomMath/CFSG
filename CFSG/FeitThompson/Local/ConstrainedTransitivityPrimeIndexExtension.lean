module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.MaximalInvariantSubgroupTransport
import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreOvergroups
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Local.InvariantHallSubgroupsConjugate
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.OddOrder.SemidirectReassociation

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem natCard_mul_relIndex {X L : Subgroup G} (h : X ≤ L) :
    Nat.card X * X.relIndex L = Nat.card L := by
  have h2 := Subgroup.card_mul_index (X.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h2
  simpa [Subgroup.relIndex] using h2

theorem maximalNormalizedPSubgroups_subset_of_normal_of_relIndex_prime [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P : Subgroup G} {q r : ℕ} (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hA : (A.subgroupOf P).Normal)
    (hindex : A.relIndex P = r) (hrπ : r ∈ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups P q ⊆ maximalNormalizedPSubgroups A q := by
  intro Q hQ
  rcases eq_or_ne Q ⊥ with rfl | hQbot
  ·
    obtain ⟨Q₀, hQ₀, hPQ₀⟩ :=
      exists_mem_maximalNormalizedPSubgroups_le_normalizer hAP hA hindex hrπ hconj
    have hQ₀bot : Q₀ = ⊥ := eq_of_mem_of_le hQ (isPGroup_of_mem hQ₀) hPQ₀ bot_le
    exact hQ₀bot ▸ hQ₀
  · exact mem_maximalNormalizedPSubgroups_of_mem_of_isPiSubgroup hG hsolv hcon hq hqπ hAP hP
      hQbot hQ

theorem exists_mem_constrainedCentralizerCore_conj_smul_eq [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A P : Subgroup G} {q r : ℕ} (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A)
    (hq : q.Prime) (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hA : (A.subgroupOf P).Normal)
    (hindex : A.relIndex P = r) (hrπ : r ∈ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
      ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ := by
  intro Q₁ hQ₁ Q₂ hQ₂
  have hsub := maximalNormalizedPSubgroups_subset_of_normal_of_relIndex_prime hG hsolv hcon hq
    hqπ hAP hP hA hindex hrπ hconj
  obtain ⟨k, hk, hkeq⟩ := hconj Q₁ (hsub hQ₁) Q₂ (hsub hQ₂)
  have hPA : P ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAP).1 hA
  have hKN : constrainedCentralizerCore A ≤ normalizer (A : Set G) :=
    (constrainedCentralizerCore_le_centralizer A).trans (centralizer_le_normalizer _)
  have hPK : P ≤ normalizer ((constrainedCentralizerCore A : Subgroup G) : Set G) :=
    hPA.trans (normalizer_le_normalizer_constrainedCentralizerCore A)
  set L : Subgroup G := constrainedCentralizerCore A ⊔ P with hLdef
  have hKL : constrainedCentralizerCore A ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hLK : L ≤ normalizer ((constrainedCentralizerCore A : Subgroup G) : Set G) :=
    sup_le le_normalizer hPK
  have hLtop : L < ⊤ :=
    lt_of_le_of_lt (sup_le hKN hPA) (normalizer_lt_top_of_isSimpleGroup hAbot hAtop)
  have hLsolv : Group.IsSolvable L := hsolv L hLtop.ne
  have hKπ : IsPiSubgroup (subgroupPrimeSupport A)ᶜ (constrainedCentralizerCore A) :=
    (isPiSubgroup_constrainedCentralizerCore A).mono
      fun _ hp => (mem_subgroupPrimeSupportCompl_iff.1 hp).2
  have hcop : (Nat.card (constrainedCentralizerCore A)).Coprime (Nat.card P) :=
    Nat.Coprime.symm (IsPiNumber.coprime_of_compl (isPiSubgroup_iff_isPiNumber.1 hP)
      (isPiSubgroup_iff_isPiNumber.1 hKπ) Nat.card_pos.ne' Nat.card_pos.ne')
  have hdisj : Disjoint (constrainedCentralizerCore A) P :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hKPbot : constrainedCentralizerCore A ⊓ P = ⊥ := disjoint_iff.1 hdisj
  have hcardL : Nat.card L = Nat.card (constrainedCentralizerCore A) * Nat.card P :=
    natCard_sup_of_le_normalizer hPK hdisj
  have hrel : ∀ X : Subgroup G, X ≤ L → Nat.card X = Nat.card P →
      X.relIndex L = Nat.card (constrainedCentralizerCore A) := by
    intro X hXL hXcard
    have h := natCard_mul_relIndex hXL
    rw [hXcard, hcardL, mul_comm (Nat.card (constrainedCentralizerCore A))] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  set V : Subgroup G := normalizer (Q₂ : Set G) ⊓ L with hVdef
  have hVL : V ≤ L := inf_le_right
  have : Group.IsSolvable V := isSolvable_of_le hVL
  have hhall : ∀ X : Subgroup G, X ≤ V → Nat.card X = Nat.card P →
      IsHallSubgroup (subgroupPrimeSupport A) (X.subgroupOf V) := by
    intro X hXV hXcard
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXV).toEquiv, hXcard]
      exact isPiSubgroup_iff_isPiNumber.1 hP
    · have h := Subgroup.relIndex_mul_relIndex X V L hXV hVL
      rw [hrel X (hXV.trans hVL) hXcard] at h
      have hdvd : (X.subgroupOf V).index ∣ Nat.card (constrainedCentralizerCore A) :=
        ⟨V.relIndex L, h.symm⟩
      exact (isPiSubgroup_iff_isPiNumber.1 hKπ).of_dvd hdvd Nat.card_pos.ne'
  have hPQ₂ : P ≤ normalizer (Q₂ : Set G) := le_normalizer_of_mem hQ₂
  have hPV : P ≤ V := le_inf hPQ₂ hPL
  have hP'Q₂ : (MulAut.conj k⁻¹ • P : Subgroup G) ≤ normalizer (Q₂ : Set G) := by
    rw [← hkeq, normalizer_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 (le_normalizer_of_mem hQ₁)
  have hP'L : (MulAut.conj k⁻¹ • P : Subgroup G) ≤ L :=
    Subgroup.conj_smul_le_of_le hPL ⟨k⁻¹, hKL ((constrainedCentralizerCore A).inv_mem hk)⟩
  have hP'V : (MulAut.conj k⁻¹ • P : Subgroup G) ≤ V := le_inf hP'Q₂ hP'L
  have hP'card : Nat.card (MulAut.conj k⁻¹ • P : Subgroup G) = Nat.card P := natCard_conj_smul _ _
  obtain ⟨v, hv⟩ :=
    exists_conj_smul_eq_of_isHallSubgroup (hhall P hPV rfl) (hhall _ hP'V hP'card)
  have hvP : (MulAut.conj (v : G) • P : Subgroup G) = MulAut.conj k⁻¹ • P :=
    conj_smul_eq_of_subgroupOf hPV hP'V hv
  have hkv : k * (v : G) ∈ normalizer (P : Set G) := by
    rw [← conj_smul_eq_self_iff_mem_normalizer, map_mul, mul_smul, hvP, ← mul_smul, ← map_mul,
      mul_inv_cancel, map_one, one_smul]
  have hvmul : (v : G) ∈ (constrainedCentralizerCore A : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ P hPK]
    exact hVL v.2
  obtain ⟨l, hl, p, hp, hlp⟩ := hvmul
  have hcK : k * l ∈ constrainedCentralizerCore A :=
    (constrainedCentralizerCore A).mul_mem hk hl
  have hcN : k * l ∈ normalizer (P : Set G) := by
    have he : k * l = (k * (v : G)) * p⁻¹ := by rw [← hlp]; group
    rw [he]
    exact (normalizer (P : Set G)).mul_mem hkv
      ((normalizer (P : Set G)).inv_mem (Subgroup.le_normalizer hp))
  have hcC : k * l ∈ centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hxK : (k * l) * x * (k * l)⁻¹ * x⁻¹ ∈ constrainedCentralizerCore A := by
      have h4 : x * (k * l)⁻¹ * x⁻¹ ∈ constrainedCentralizerCore A :=
        (Subgroup.mem_normalizer_iff.1 (hLK (hPL hx)) _).1
          ((constrainedCentralizerCore A).inv_mem hcK)
      have h5 := (constrainedCentralizerCore A).mul_mem hcK h4
      simpa [mul_assoc] using h5
    have hxP : (k * l) * x * (k * l)⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN x).1 hx) (P.inv_mem hx)
    have h1 : (k * l) * x * (k * l)⁻¹ * x⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← hKPbot]; exact ⟨hxK, hxP⟩
    have h3 : ((k * l) * x) * (x * (k * l))⁻¹ = 1 := by
      rw [mul_inv_rev]; simpa [mul_assoc] using h1
    exact (mul_inv_eq_one.mp h3).symm
  have hlQ : l ∈ normalizer (Q₂ : Set G) := by
    have hvQ : (v : G) ∈ normalizer (Q₂ : Set G) := (Subgroup.mem_inf.1 v.2).1
    have he : l = (v : G) * p⁻¹ := by rw [← hlp]; group
    rw [he]
    exact (normalizer (Q₂ : Set G)).mul_mem hvQ
      ((normalizer (Q₂ : Set G)).inv_mem (hPQ₂ hp))
  refine ⟨k * l, ?_, ?_⟩
  · rw [constrainedCentralizerCore_eq_inf_centralizer hAbot hAtop hcon hAP hP, Subgroup.mem_inf]
    exact ⟨hcK, hcC⟩
  · rw [mul_inv_rev, map_mul, mul_smul, hkeq, conj_smul_eq_self_iff_mem_normalizer]
    exact (normalizer (Q₂ : Set G)).inv_mem hlQ

theorem isConstrainedTransitive_of_normal_of_relIndex_prime
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A P : Subgroup G} {q r : ℕ}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hAP : A ≤ P) (_hPtop : P < ⊤)
    (hP : IsPiSubgroup (subgroupPrimeSupport A) P) (hA : (A.subgroupOf P).Normal)
    (hindex : A.relIndex P = r) (hrπ : r ∈ subgroupPrimeSupport A)
    (hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂) :
    maximalNormalizedPSubgroups P q ⊆ maximalNormalizedPSubgroups A q ∧
      ∀ Q₁ ∈ maximalNormalizedPSubgroups P q, ∀ Q₂ ∈ maximalNormalizedPSubgroups P q,
        ∃ c ∈ constrainedCentralizerCore P, (MulAut.conj c⁻¹ • Q₁ : Subgroup G) = Q₂ :=
  have := hsimple
  ⟨maximalNormalizedPSubgroups_subset_of_normal_of_relIndex_prime hG hsolv hcon hq hqπ hAP hP hA
      hindex hrπ hconj,
    exists_mem_constrainedCentralizerCore_conj_smul_eq hG hsolv hAbot hAtop hcon hq hqπ hAP hP hA
      hindex hrπ hconj⟩

end

end CFSG.FeitThompson
