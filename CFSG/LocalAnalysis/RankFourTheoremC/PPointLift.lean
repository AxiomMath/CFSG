module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup

theorem injOn_mk_of_isPGroup {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {O : Subgroup C} [O.Normal] (hO : p.Coprime (Nat.card O)) {Q : Subgroup C} (hQ : IsPGroup p Q) :
    ∀ q ∈ Q, ∀ q' ∈ Q, QuotientGroup.mk' O q = QuotientGroup.mk' O q' → q = q' := by
  intro q hq q' hq' h
  have hdisj : Disjoint Q O := by
    obtain ⟨m, hm⟩ := hQ.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard (by rw [hm]; exact hO.pow_left m)
  have hmem : q⁻¹ * q' ∈ O := by
    have : QuotientGroup.mk' O (q⁻¹ * q') = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have h1 : q⁻¹ * q' ∈ Q ⊓ O := ⟨Q.mul_mem (Q.inv_mem hq) hq', hmem⟩
  rw [disjoint_iff.mp hdisj, mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem exists_normalizing_lift {C : Type} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {O W : Subgroup C} [O.Normal] (hO : p.Coprime (Nat.card O)) (hW : IsPGroup p W) {γ : C}
    (hγ : ∀ w ∈ W, γ * w * γ⁻¹ ∈ O ⊔ W) :
    ∃ o ∈ O, ∃ w₀ ∈ W, ∀ w ∈ W, (o * w₀ * γ) * w * (o * w₀ * γ)⁻¹ ∈ W := by
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p W (O ⊔ W) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hW, fun hdvd => ?_⟩
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal] at hdvd
    have hcop : p.Coprime (W.relIndex O) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_card W O) hO
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hE : W.map (MulAut.conj γ).toMonoidHom ≤ O ⊔ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact hγ w hw
  obtain ⟨c, hc, hcE⟩ := exists_conj_le_of_isSylowOf hsyl hE (hW.map _)
  obtain ⟨o, ho, w₀, hw₀, hoc⟩ := Subgroup.mem_sup_of_normal_left.mp hc
  refine ⟨o, ho, w₀, hw₀, fun w hw => ?_⟩
  have h1 : c * (γ * w * γ⁻¹) * c⁻¹ ∈ W := hcE ⟨γ * w * γ⁻¹, ⟨w, hw, rfl⟩, rfl⟩
  rw [hoc]
  simpa [mul_assoc] using h1

theorem mem_zpowers_of_pow_three_of_isCyclic {D : Type*} [Group D] [Finite D] [IsCyclic D]
    {z c : D} (hz : orderOf z = 3) (hc : c ^ 3 = 1) : c ∈ zpowers z := by
  by_cases hc1 : c = 1
  · rw [hc1]
    exact one_mem _
  have hco : orderOf c = 3 := orderOf_eq_prime hc hc1
  have h : zpowers z = zpowers c :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, hco])
  rw [h]
  exact mem_zpowers c

end CFSG.LocalAnalysis.RankFourTheoremC
