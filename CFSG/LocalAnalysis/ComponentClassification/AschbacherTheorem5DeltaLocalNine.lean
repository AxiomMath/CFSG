module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineX

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools DeltaLocal DeltaLocal.Nine

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace DeltaLocal.Nine

theorem false_of_orient (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {a m : Fin r}
    (ham : a ≠ m)
    (horient : (Nat.card (aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) g : Subgroup G)).factorization 2 ≤
      (Nat.card (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
        Subgroup.normalizer (D : Set G) : Subgroup G)).factorization 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : g ∉ Subgroup.normalizer (D : Set G) := by
    obtain ⟨-, -, hne, -⟩ := hΔ
    exact fun h => hne ((rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer h))
  obtain ⟨T, hT, hTk⟩ := sylow_normalizes h3 hin hC hΔ hr a
  obtain ⟨-, R, hR, hRT⟩ := orbit_normalizes h3 hin hC hΔ hr (i := a) (j := a) (k := m)
    (hT.le.trans inf_le_left) (hT.le.trans inf_le_right) hT.isPGroup (preimage_le D _) le_rfl
    (factor_le_centralizing hC.hyp.hcomm (Ne.symm ham)) (hTk a)
  have hRTN : R ≤ Subgroup.normalizer (T : Set G) := by
    refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun t ht => hRT t ht x hx
  have hRcard : Nat.card R ≤ Nat.card T := by
    rw [hR.card_eq, hT.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) horient
  obtain ⟨X, hX2, hXH, hTX, hTXne, hXm, hXA, hRX, hY⟩ := exists_X h3 hin hC hΔ hr ham hT
    hR.isPGroup (hR.le.trans inf_le_left) (hR.le.trans inf_le_right) hRTN
  obtain ⟨S, hS, -, hST, hXS⟩ := part_two hC hg hX2 hTX hTXne hXm (hXA a) hRX hR hRcard
  exact part_three h3 hin hC hΔ hr hX2 hXH hTX hTXne hXm (hXA a) hY hS hST hXS

end DeltaLocal.Nine

theorem lemma_6_9 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar)
    (hΔ : (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty) : r = 2 := by
  obtain ⟨K, g, rfl, hne, U, hU⟩ := hΔ
  have hΔg : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) := ⟨g, rfl, hne, U, hU⟩
  by_contra hr2
  have hr : 3 ≤ r := by have := two_le hC; omega
  set a : Fin r := ⟨0, by omega⟩ with hadef
  set m : Fin r := ⟨1, by omega⟩ with hmdef
  have ham : a ≠ m := fun h => absurd (congrArg Fin.val h) (by simp [hadef, hmdef])
  rcases le_total ((Nat.card (aschbacherThm5Preimage D (Abar a) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g : Subgroup G)).factorization 2)
    ((Nat.card (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G) : Subgroup G)).factorization 2) with horient | horient
  · exact false_of_orient h3 hin hC hΔg hr ham horient
  ·
    refine false_of_orient h3 hin (hC.conj g) (delta_conj h3 hin hC hΔg) hr ham ?_
    rw [preimage_conjFactors, Six.conj_normalizer_inv, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one, normalizer_rightConjugate]
    simpa only [inf_comm] using horient

end CFSG.ComponentClassification.AschbacherTheorem5
