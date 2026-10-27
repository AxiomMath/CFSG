module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210ElemSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210SylowNorm
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

private theorem card_conj (h : L210Hyp A) (g : X) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = 2 ^ 8 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card]

theorem L210_eq_of_elemAbelian_card (h : L210Hyp A) {E : Subgroup X} (hE : IsElemAbelian 2 E)
    (hEc : Nat.card E = 2 ^ 8) (hEN : E ≤ normalizer (A : Set X)) : E = A := by
  by_contra hne
  have hnotle : ¬ E ≤ A := by
    intro hEA
    exact hne (Subgroup.eq_of_le_of_card_ge hEA (le_of_eq (h.card.trans hEc.symm)))
  obtain ⟨i, hiE, hiA⟩ := Set.not_subset.mp hnotle
  have hi2 : i * i = 1 := by
    simpa [pow_two] using hE.2 i hiE
  have hiN : i ∈ normalizer (A : Set X) := hEN hiE
  have hCi : Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16 :=
    h.centralizer_le i hiN hiA hi2
  obtain ⟨D, hDE, hDF, hcardD⟩ :=
    exists_complement_of_isElemAbelian (E := E) (F := E ⊓ A) hE (inf_le_left : E ⊓ A ≤ E)
  have hFle : (E ⊓ A : Subgroup X) ≤ A ⊓ centralizer ({i} : Set X) := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hE.comm hiE hx.1
  have hFcard : Nat.card ↥(E ⊓ A) ≤ 16 :=
    le_trans (Subgroup.card_le_of_le hFle) hCi
  have hDgt : 8 < Nat.card D := by
    by_contra hnot
    push_neg at hnot
    have hbound : Nat.card D * Nat.card ↥(E ⊓ A) ≤ 8 * 16 := Nat.mul_le_mul hnot hFcard
    rw [hEc] at hcardD
    norm_num at hcardD hbound
    omega
  have hDbot : D ⊓ A = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hDE] at hDF
    exact hDF
  have hDcard : Nat.card D ≤ 8 :=
    h.noE16 D (le_trans hDE hEN) (hE.mono hDE) hDbot
  omega

theorem L210_exists_sylow (h : L210Hyp A) :
    ∃ T : Sylow 2 X, (T : Subgroup X) ≤ normalizer (A : Set X) ∧ GoldHyp T A := by
  classical
  let S : Set (Subgroup X) := {Q | IsPGroup 2 Q ∧ A ≤ Q ∧ Q ≤ normalizer (A : Set X)}
  have hAS : A ∈ S := by
    show IsPGroup 2 A ∧ A ≤ A ∧ A ≤ normalizer (A : Set X)
    exact ⟨IsPGroup.of_card (n := 8) h.card, le_rfl, Subgroup.le_normalizer⟩
  obtain ⟨T₀, hT₀max⟩ :=
    Set.Finite.exists_maximalFor (fun Q : Subgroup X => Nat.card Q) S (Set.toFinite S)
      ⟨A, hAS⟩
  have hT₀S : IsPGroup 2 T₀ ∧ A ≤ T₀ ∧ T₀ ≤ normalizer (A : Set X) := hT₀max.1
  have hT₀P : IsPGroup 2 T₀ := hT₀S.1
  have hAT₀ : A ≤ T₀ := hT₀S.2.1
  have hT₀N : T₀ ≤ normalizer (A : Set X) := hT₀S.2.2
  have hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → Q ≤ normalizer (A : Set X) →
      T₀ ≤ Q → Q = T₀ := by
    intro Q hQP hQN hTQ
    have hQS : Q ∈ S := by
      show IsPGroup 2 Q ∧ A ≤ Q ∧ Q ≤ normalizer (A : Set X)
      exact ⟨hQP, le_trans hAT₀ hTQ, hQN⟩
    have hle : Nat.card T₀ ≤ Nat.card Q := Subgroup.card_le_of_le hTQ
    have hge : Nat.card Q ≤ Nat.card T₀ := hT₀max.2 hQS hle
    exact (Subgroup.eq_of_le_of_card_ge hTQ hge).symm
  have hnorm : normalizer (T₀ : Set X) ≤ normalizer (A : Set X) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hA'leT : A.map (MulAut.conj n).toMonoidHom ≤ T₀ :=
      calc A.map (MulAut.conj n).toMonoidHom ≤ T₀.map (MulAut.conj n).toMonoidHom :=
            Subgroup.map_mono hAT₀
        _ = T₀ := by
            simpa only [MulEquiv.toMonoidHom_eq_coe] using
              Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
    exact L210_eq_of_elemAbelian_card h (h.elemAb.map (MulAut.conj n).toMonoidHom) (card_conj h n)
      (le_trans hA'leT hT₀N)
  obtain ⟨T, hT⟩ :=
    exists_sylow_of_maximal_two_subgroup (N := normalizer (A : Set X)) (P := T₀) hT₀P hT₀N
      hmax hnorm
  refine ⟨T, ?_, ?_⟩
  · rw [hT]; exact hT₀N
  · refine ⟨?_, h.elemAb, ?_⟩
    · rw [hT]; exact hAT₀
    · intro g hg a ha
      have hA''leT : A.map (MulAut.conj g).toMonoidHom ≤ T₀ := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
        show g * b * g⁻¹ ∈ T₀
        rw [← hT]
        exact hg b hb
      have hA'' : A.map (MulAut.conj g).toMonoidHom = A :=
        L210_eq_of_elemAbelian_card h (h.elemAb.map (MulAut.conj g).toMonoidHom) (card_conj h g)
          (le_trans hA''leT hT₀N)
      rw [← hA'']
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha

end CFSG.EvenSporadicStandard.HNRecog.Harada
