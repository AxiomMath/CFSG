module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Pointwise

theorem i227cop_inf_eq_bot {K : Type*} [Group K] {R N : Subgroup K} (hR : IsPGroup 3 R)
    (hN : Nat.Coprime 3 (Nat.card N)) : R ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hR ⟨x, hx.1⟩
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx.2
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (hN.pow_left k) h1 h2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)

theorem i227cop_exists_normalizer_mul {K : Type*} [Group K] [Finite K] {N Q : Subgroup K}
    [N.Normal] (hN : Nat.Coprime 3 (Nat.card N)) (hQ : IsPGroup 3 Q) (x : K)
    (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q ⊔ N) :
    ∃ y ∈ Subgroup.normalizer (Q : Set K), ∃ n ∈ N, x = y * n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G' : Subgroup K := Q ⊔ N with hG'
  have hQG' : Q ≤ G' := le_sup_left
  have hNG' : N ≤ G' := le_sup_right
  set R : Subgroup K := Q.map (MulAut.conj x).toMonoidHom with hR
  have hmemR : ∀ w : K, w ∈ R ↔ x⁻¹ * w * x ∈ Q := by
    intro w
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hq
    · intro hw
      exact ⟨x⁻¹ * w * x, hw, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hRG' : R ≤ G' := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hx q hq
  have hbot : Q ⊓ N = ⊥ := i227cop_inf_eq_bot hQ hN
  have hNQ : N.subgroupOf Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have h : (q : K) ∈ Q ⊓ N := ⟨q.2, Subgroup.mem_subgroupOf.1 hq⟩
    rw [hbot, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hrel : N.relIndex G' = Nat.card Q := by
    rw [hG', Subgroup.relIndex_sup_right, Subgroup.relIndex, hNQ, Subgroup.index_bot]
  have hcardN : Nat.card (N.subgroupOf G') = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG').toEquiv
  have hcardG : Nat.card G' = Nat.card Q * Nat.card N := by
    have h := Subgroup.index_mul_card (N.subgroupOf G')
    rw [hcardN] at h
    rw [← h]
    change N.relIndex G' * Nat.card N = _
    rw [hrel]
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hcardR : Nat.card R = Nat.card Q := Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hN3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hN
  have hidx : ∀ T : Subgroup K, T ≤ G' → Nat.card T = Nat.card Q → ¬ 3 ∣ (T.subgroupOf G').index := by
    intro T hT hTc
    have h := Subgroup.index_mul_card (T.subgroupOf G')
    have hc : Nat.card (T.subgroupOf G') = Nat.card Q :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv).trans hTc
    rw [hc, hcardG] at h
    have : (T.subgroupOf G').index = Nat.card N := by
      have h' : (T.subgroupOf G').index * Nat.card Q = Nat.card N * Nat.card Q := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hQpos h'
    rw [this]
    exact hN3
  have hQ₁ : IsPGroup 3 (Q.subgroupOf G') := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQG').symm
  have hR₁ : IsPGroup 3 (R.subgroupOf G') :=
    (hQ.map (MulAut.conj x).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hRG').symm
  let S₁ : Sylow 3 G' := hQ₁.toSylow (hidx Q hQG' rfl)
  let S₂ : Sylow 3 G' := hR₁.toSylow (hidx R hRG' hcardR)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G' S₁ S₂
  have hS : ((g • S₁ : Sylow 3 G') : Subgroup G') = R.subgroupOf G' := by
    rw [hg]; exact IsPGroup.toSylow_coe _ _
  have key : ∀ w : K, w ∈ G' → (w ∈ R ↔ (g : K)⁻¹ * w * g ∈ Q) := by
    intro w hw
    have h := Subgroup.ext_iff.1 hS ⟨w, hw⟩
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      at h
    simp only [S₁, IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply,
      Subgroup.mem_subgroupOf] at h
    exact h.symm
  have hgG : (g : K) ∈ G' := g.2
  set y₀ : K := (g : K)⁻¹ * x with hy₀
  have hy₀N : y₀ ∈ Subgroup.normalizer (Q : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hy : y₀ * h * y₀⁻¹ = (g : K)⁻¹ * (x * h * x⁻¹) * g := by
      simp [hy₀, mul_assoc]
    rw [hy]
    constructor
    · intro hh
      have hw : x * h * x⁻¹ ∈ G' := hx h hh
      exact (key _ hw).1 ((hmemR _).2 (by simpa [mul_assoc] using hh))
    · intro hh
      have hw : x * h * x⁻¹ ∈ G' := by
        have : (g : K) * ((g : K)⁻¹ * (x * h * x⁻¹) * g) * (g : K)⁻¹ ∈ G' :=
          mul_mem (mul_mem hgG (hQG' hh)) (inv_mem hgG)
        simpa [mul_assoc] using this
      have h2 := (key _ hw).2 hh
      have h3 := (hmemR _).1 h2
      simpa [mul_assoc] using h3
  obtain ⟨q, hq, n, hn, hqn⟩ := Subgroup.mem_sup_of_normal_right.1 hgG
  refine ⟨q * y₀, mul_mem (Subgroup.le_normalizer hq) hy₀N, y₀⁻¹ * n * y₀, ?_, ?_⟩
  · simpa using (inferInstance : N.Normal).conj_mem n hn y₀⁻¹
  · have hg' : (g : K) = q * n := hqn.symm
    calc x = (g : K) * y₀ := by simp [hy₀]
      _ = q * y₀ * (y₀⁻¹ * n * y₀) := by rw [hg']; group

end CFSG.HardMathSupport.Solomon.Coordinator
