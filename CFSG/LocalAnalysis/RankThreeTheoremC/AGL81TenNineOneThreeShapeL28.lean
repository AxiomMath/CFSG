module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.L28Local CFSG.Quasithin.F6.L28Res

namespace TenNineOneThree

private theorem exists_orderOf_nine {K : Type} [Group K] [Finite K] (ε₀ : K ≃* G8) (S : Sylow 3 K) :
    ∃ s ∈ (S : Subgroup K), orderOf s = 9 := by
  have hE : Nat.card ((S : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← card_sylow_three ε₀ S]
    exact (Nat.card_congr (ε₀.subgroupMap (S : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine card_G8 hE card_T0
  have hy : g⁻¹ * g9 * g ∈ (S : Subgroup K).map ε₀.toMonoidHom := by
    rw [hg, show g * (g⁻¹ * g9 * g) * g⁻¹ = g9 by group]
    exact Subgroup.mem_zpowers g9
  obtain ⟨s, hs, hse⟩ := hy
  refine ⟨s, hs, ?_⟩
  have h1 : orderOf s = orderOf (ε₀ s) := (orderOf_injective ε₀.toMonoidHom ε₀.injective s).symm
  have h2 : orderOf (g⁻¹ * g9 * g) = orderOf g9 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective g9
    simpa [MulAut.conj_apply] using this
  rw [h1, show ε₀ s = g⁻¹ * g9 * g from hse, h2, orderOf_g9]

theorem exists_orderOf_nine_of_isCaseTwoGroup {K : Type} [Group K] [Finite K]
    (hK : IsCaseTwoGroup 3 K) (S : Sylow 3 K) : ∃ s ∈ (S : Subgroup K), orderOf s = 9 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  exact exists_orderOf_nine ε₀ S

theorem pRank_top_le_two_of_card {P : Type} [Group P] [Finite P] (hP : Nat.card P = 27)
    (hnc : ¬ ∀ a b : P, a * b = b * a) : Open.pRank 3 (⊤ : Subgroup P) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  by_contra! hlt
  have hdvd : Nat.card E ∣ 27 := hP ▸ Subgroup.card_subgroup_dvd_card E
  have hE27 : Nat.card E = 27 := by
    have hd : Nat.card E ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have htop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hE27, hP])
  apply hnc
  intro a b
  have := hE.1.is_comm.comm (⟨a, htop ▸ Subgroup.mem_top a⟩ : E) ⟨b, htop ▸ Subgroup.mem_top b⟩
  exact congrArg Subtype.val this

theorem shapeSimple_of_l28 {K : Type} [Group K] [Finite K] (hK : IsCaseTwoGroup 3 K)
    (S : Sylow 3 K) {P : Subgroup (MulAut K)} (hP : IsPGroup 3 P)
    (hSP : (S : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ P) : ShapeSimple P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  have hD := l28Data_of_equiv ε₀ S
  set I := (S : Subgroup K).map (MulAut.conj : K →* MulAut K) with hI
  have hIcard : Nat.card I = 9 := by
    rw [hI, Subgroup.card_map_of_injective hD.conj_injective, hD.card_eq]
  have hP27 : Nat.card P ≤ 27 := kFactL28AutThree K hK P hP
  have h9P : 9 ∣ Nat.card P := hIcard ▸ Subgroup.card_dvd_of_le hSP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk' : k = 2 ∨ k = 3 := by
    have h1 : 3 ^ 2 ∣ 3 ^ k := by rw [← hk]; simpa using h9P
    have h2 : 3 ^ k ≤ 3 ^ 3 := by rw [← hk]; simpa using hP27
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    omega
  rcases hk' with rfl | rfl
  ·
    obtain ⟨s0, hs0S, hs0⟩ := exists_orderOf_nine ε₀ S
    have hgen : Subgroup.zpowers (MulAut.conj s0) = P := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hSP ⟨s0, hs0S, rfl⟩
      · rw [Nat.card_zpowers, orderOf_injective _ hD.conj_injective, hs0, hk]
        norm_num
    left
    refine ⟨?_, by rw [hk]; norm_num⟩
    rw [← hgen]
    infer_instance
  · right
    have hnc : ¬ ∀ a b : P, a * b = b * a := by
      intro hcomm
      obtain ⟨ψ, hψP, hψI⟩ : ∃ ψ ∈ P, ψ ∉ I := by
        by_contra! h
        have := Subgroup.card_le_of_le (show P ≤ I from h)
        rw [hk, hIcard] at this
        norm_num at this
      apply hψI
      have hfix : ∀ x ∈ (S : Subgroup K), ψ x = x := by
        intro x hx
        have hc := congrArg Subtype.val (hcomm ⟨ψ, hψP⟩ ⟨MulAut.conj x, hSP ⟨x, hx, rfl⟩⟩)
        have hc' : ψ * MulAut.conj x = MulAut.conj x * ψ := hc
        apply hD.conj_injective
        ext y
        have h1 := congrArg (fun α : MulAut K => α (ψ.symm y)) hc'
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.apply_symm_apply] at h1
        rw [MulAut.conj_apply, MulAut.conj_apply, h1]
      obtain ⟨t, ht, rfl⟩ := hD.aut ψ hfix
      exact ⟨t, ht, rfl⟩
    exact ⟨hnc, pRank_top_le_two_of_card (by rw [hk]; norm_num) hnc⟩

theorem kFactCaseIThreeShapeL28 :
    ∀ (B : Type) [Group B] [Finite B] (Kb : Subgroup B) [Kb.Normal] (T : Subgroup B),
      IsPGroup 3 T → (∃ S : Sylow 3 Kb, (S : Subgroup Kb).map Kb.subtype ≤ T) →
      IsCaseTwoGroup 3 Kb →
        ShapeSimple (T ⧸ ((MulAut.conjNormal (H := Kb)).comp T.subtype).ker) := by
  intro B _ _ Kb _ T hT ⟨S, hST⟩ hK
  set φ := (MulAut.conjNormal (H := Kb)).comp T.subtype with hφ
  have hrange : (S : Subgroup Kb).map (MulAut.conj : Kb →* MulAut Kb) ≤ φ.range := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨s, hST ⟨s, hs, rfl⟩⟩, ?_⟩
    ext y
    simp [hφ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hP : IsPGroup 3 φ.range := hT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact shapeSimple_congr (QuotientGroup.quotientKerEquivRange φ).symm
    (shapeSimple_of_l28 hK S hP hrange)

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
