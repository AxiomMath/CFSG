module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB

theorem i227cmp_elem_family {K : Type*} [Group K] {ι : Type*} [Fintype ι] (x : ι → K)
    (hord : ∀ i, orderOf (x i) = 3) (hcomm : ∀ i j, i ≠ j → Commute (x i) (x j))
    (hind : iSupIndep fun i => Subgroup.zpowers (x i)) :
    IsElemAbelian 3 (⨆ i, Subgroup.zpowers (x i)) ∧
      Nat.card (⨆ i, Subgroup.zpowers (x i) : Subgroup K) = 3 ^ Fintype.card ι := by
  classical
  have hc : Pairwise fun i j : ι => ∀ a b : K, a ∈ Subgroup.zpowers (x i) →
      b ∈ Subgroup.zpowers (x j) → Commute a b := by
    intro i j hij a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hcomm i j hij).zpow_zpow m n
  set φ := Subgroup.noncommPiCoprod hc with hφ
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = ⨆ i, Subgroup.zpowers (x i) := Subgroup.noncommPiCoprod_range
  have hzc : ∀ (i : ι) (a b : K), a ∈ Subgroup.zpowers (x i) → b ∈ Subgroup.zpowers (x i) →
      a * b = b * a := by
    intro i a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.refl (x i)).zpow_zpow m n).eq
  have hx3 : ∀ i, x i ^ 3 = 1 := fun i => by
    rw [← hord i]; exact pow_orderOf_eq_one _
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩, ?_⟩
  · have ha : (a : K) ∈ φ.range := by rw [hrange]; exact a.2
    have hb : (b : K) ∈ φ.range := by rw [hrange]; exact b.2
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine Subtype.ext ?_
    show (a : K) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    exact congrArg φ (funext fun i => Subtype.ext (hzc i _ _ (u i).2 (v i).2))
  · have hg' : g ∈ φ.range := by rw [hrange]; exact hg
    obtain ⟨u, rfl⟩ := hg'
    rw [← map_pow]
    have : u ^ 3 = 1 := by
      funext i
      refine Subtype.ext ?_
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (u i).2
      show ((u i : K)) ^ 3 = 1
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    rw [this, map_one]
  · have h1 : Nat.card (⨆ i, Subgroup.zpowers (x i) : Subgroup K) =
        Nat.card (∀ i, Subgroup.zpowers (x i)) := by
      rw [← hrange]
      exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm
    rw [h1, Nat.card_pi]
    simp [Nat.card_zpowers, hord]

theorem i227cmp_normalizer_le_weakCoreIn {K : Type*} [Group K] [Finite K] {P Q : Subgroup K}
    (hQP : Q ≤ P) (hr : 3 ≤ CFSG.Open.pRank 3 Q) :
    Subgroup.normalizer (Q : Set K) ≤ weakCoreIn 3 P ⊤ := by
  have hr3 : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))) :=
    hr.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left)
  exact le_iSup₂_of_le Q ⟨hQP, (by norm_num : 2 ≤ 3).trans hr, hr3⟩ (top_inf_eq _).ge

theorem i227cmp_glaWeakCore_le_weakCoreIn {K : Type*} [Group K] [Finite K] (P : Subgroup K) :
    GLAWeakCore 3 P ≤ weakCoreIn 3 P ⊤ := by
  refine sSup_le ?_
  rintro N ⟨Q, hQP, h2, h3, rfl⟩
  exact le_iSup₂_of_le Q ⟨hQP, h2, h3⟩ (top_inf_eq _).ge

theorem i227cmp_top_le_weakCoreIn_conj {K : Type} [Group K] [Finite K] {P : Subgroup K}
    (h : (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤) (g : K) :
    (⊤ : Subgroup K) ≤ weakCoreIn 3 (GLBConj g P) ⊤ := by
  have h1 : (⊤ : Subgroup K) ≤ GLAWeakCore 3 P := h.trans (weakCoreIn_le_glaWeakCore 3 P ⊤)
  have h2 := gLBConj_mono g h1
  have htop : GLBConj g (⊤ : Subgroup K) = ⊤ := by ext z; simp [mem_gLBConj]
  rw [htop, ← glaWeakCore_gLBConj Nat.prime_three] at h2
  exact h2.trans (i227cmp_glaWeakCore_le_weakCoreIn _)

end CFSG.HardMathSupport.Solomon.Coordinator
