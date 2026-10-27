module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526I1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row28SylowPairPE

variable {X : Type} [Group X] [Finite X] {G : Type} [Group G] [Finite G]

theorem exists_sylow_central_pair_of_pElem {L I Q A : Subgroup X} (hLn : L.Normal)
    (hIn : ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Subgroup.normalizer (I : Set X))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hQnc : ¬ IsCyclic ↥Q)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) (hA3 : Nat.card A = 3)
    (hLI : ∀ x ∈ L ⊓ I, (∃ k : ℕ, orderOf x = 3 ^ k) → x = 1) :
    ∃ P Q₁ B : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧ A ≤ P ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Q₁ I ∧ (∃ i ∈ I, Q₁ = conjSub i Q) ∧ B ≤ Q₁ ∧ Nat.card B = 3 ∧
      Q₁ ≤ P ∧ P ≤ Subgroup.normalizer (Q₁ : Set X) ∧ (∀ d ∈ A ⊔ B, ∀ y ∈ P, d * y = y * d) ∧
      IsElemAbelian 3 (A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP3, hPtop, hAP⟩ : ∃ P : Subgroup X, IsPGroup 3 P ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧ A ≤ P := by
    obtain ⟨P₀, hAP₀⟩ := hA.isPGroup.exists_le_sylow
    refine ⟨(P₀ : Subgroup X), P₀.isPGroup', ?_, hAP₀⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, P₀.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P₀.not_dvd_index⟩
  have hPnI : P ≤ Subgroup.normalizer (I : Set X) := by
    intro y hy
    exact hIn y (exists_sylow_central_pair_aux1 hP3 hy)
  have hnL : (⊤ : Subgroup X) ≤ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
  have hQ₁ : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ I) I := by
    have hM : CFSG.ABGLocalTools.IsSylowOf 3 P (I ⊔ P) := hPtop.of_le le_sup_right le_top
    have hMn : I ⊔ P ≤ Subgroup.normalizer (I : Set X) := sup_le Subgroup.le_normalizer hPnI
    exact hM.inf_of_le_normalizer le_sup_left hMn
  obtain ⟨i, hi, hQ₁Q⟩ := exists_sylow_central_pair_aux2 hQ hQ₁
  have hPL : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L := hPtop.inf_of_le_normalizer le_top hnL
  have hAeq : P ⊓ L = A := hA.eq_of_le (le_inf hAP hA.le) inf_le_right hPL.isPGroup
  have hAnorm : ∀ y ∈ P, ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro y hy a ha
    rw [← hAeq] at ha ⊢
    exact Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hy ha.1) (P.inv_mem hy), hLn.conj_mem a ha.2 y⟩
  have hAc : ∀ a ∈ A, ∀ y ∈ P, a * y = y * a :=
    exists_sylow_central_pair_aux4 hP3 hAP hA3 hAnorm
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    exact hQnc inferInstance
  have hQ₁ne : P ⊓ I ≠ ⊥ := by
    intro h
    apply hQne
    have hcard : Nat.card Q = Nat.card (P ⊓ I : Subgroup X) := by
      rw [hQ₁Q, conjSub, Subgroup.card_map_of_injective (MulAut.conj i).injective]
    rw [h, Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq Q hcard
  have hQ₁norm : ∀ y ∈ P, ∀ n ∈ P ⊓ I, y * n * y⁻¹ ∈ P ⊓ I := fun y hy n hn =>
    Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hy hn.1) (P.inv_mem hy),
      (Subgroup.mem_normalizer_iff.mp (hPnI hy) n).mp hn.2⟩
  obtain ⟨b, hbQ₁, hb3, hbc⟩ := exists_sylow_central_pair_aux3 hP3 inf_le_left hQ₁ne hQ₁norm
  have hBQ₁ : Subgroup.zpowers b ≤ P ⊓ I := Subgroup.zpowers_le.mpr hbQ₁
  have hB3 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb3]
  have hBc : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_left (hbc y hy) n
  have hdisj : Disjoint A (Subgroup.zpowers b) := by
    rw [disjoint_iff_inf_le]
    intro y hy
    rw [Subgroup.mem_bot]
    exact hLI y (Subgroup.mem_inf.2 ⟨hA.le hy.1, hQ₁.le (hBQ₁ hy.2)⟩)
      (exists_sylow_central_pair_aux1 hA.isPGroup hy.1)
  have hBP : Subgroup.zpowers b ≤ P := hBQ₁.trans inf_le_left
  have hBnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (A : Set X) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
    have hc : n * x = x * n := hAc n hn x (hBP hx)
    show x * n * x⁻¹ ∈ A
    rw [← hc, mul_inv_cancel_right]
    exact hn
  have hcard9 : Nat.card ↥(A ⊔ Subgroup.zpowers b) = 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A _ hBnorm hdisj, hA3,
      hB3]
  have hDc : ∀ d ∈ A ⊔ Subgroup.zpowers b, ∀ y ∈ P, d * y = y * d := by
    intro d hd y hy
    have hle : A ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer (P : Set X) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        exact fun h hh => (hAc a ha h hh).symm
      · rw [Subgroup.mem_centralizer_iff]
        exact fun h hh => (hBc a ha h hh).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hd)) y hy).symm
  have hDP : A ⊔ Subgroup.zpowers b ≤ P := sup_le hAP hBP
  have hDea : IsElemAbelian 3 (A ⊔ Subgroup.zpowers b) := by
    refine ⟨⟨⟨fun a a' => Subtype.ext (hDc a a.2 a' (hDP a'.2))⟩⟩, ?_⟩
    intro x hx
    have hx' : x ∈ ((A ⊔ Subgroup.zpowers b : Subgroup X) : Set X) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A _ hBnorm] at hx'
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    have hcomm : Commute a c := hAc a ha c (hBP hc)
    rw [hcomm.mul_pow, exists_sylow_central_pair_aux5 hA3 ha,
      exists_sylow_central_pair_aux5 hB3 hc, one_mul]
  have hPnorm : P ≤ Subgroup.normalizer ((P ⊓ I : Subgroup X) : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hQ₁norm y hy h hh
    · intro hh
      have h1 : h = y⁻¹ * (y * h * y⁻¹) * y := by group
      have hI := (Subgroup.mem_normalizer_iff.mp (hPnI (P.inv_mem hy)) (y * h * y⁻¹)).mp hh.2
      rw [inv_inv] at hI
      rw [h1]
      exact Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem (P.inv_mem hy) hh.1) hy, hI⟩
  exact ⟨P, P ⊓ I, Subgroup.zpowers b, hPtop, hAP, hQ₁, ⟨i, hi, hQ₁Q⟩, hBQ₁, hB3, inf_le_left,
    hPnorm, hDc, hDea, hcard9⟩

end Row28SylowPairPE

end CFSG.LocalAnalysis.RankThreeUC.S15
