module

public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Uniform.U3Witness
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Nbr

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_oddCoreOf_of_normalizes_of_odd' {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M :=
  CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd_gen hNM hn hodd

theorem commutes_of_mem_omegaNbr3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : Commutes K J := by
  have hg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hg hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have h8T : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hg hT
  obtain ⟨Q, hQ, hQinv⟩ := AscL62.exists_sylow_normalized hT2 hTN
  have hQset : Q ∈ RSet Ω := mem_RSet_of_isSylow2In hK hQ
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have h8Q : 8 ≤ Nat.card Q := Sec6Gen.eight_le_of_mem_RSet hg hQset
  have hTnQ : T ≤ Subgroup.normalizer (Q : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hQinv t ht)
  have hTQ2 : IsPGroup 2 ↥(T ⊔ Q) := hT2.to_sup_of_normal_right' hQ2 hTnQ
  obtain ⟨S, hS⟩ := hTQ2.exists_le_sylow
  have hTneQ : T ≠ Q := by
    intro h
    exact hne (Sec6Gen.eq_of_le_of_le hg hJΩ hK hT2 (by omega) hTJ (h ▸ hQ.1))
  have hTQc : Commutes T Q :=
    Q3.Q3CP.l67Gen G Ω hg S T hT Q hQset (le_sup_left.trans hS) (le_sup_right.trans hS) hTneQ
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution hg hK
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hg hJΩ
  have hTcK : ∀ k ∈ K, ∀ v ∈ T, v * k = k * v := by
    intro k hk v hv
    have h1 := Sec6Gen.commutator_mem_oddCoreOf_of_centralizes hzK hQ hT2
      (fun y hy => conjSub_eq_of_mem_normalizer (hTN hy))
      (fun r hr v hv => (hTQc v hv r hr).symm) k hk v hv
    rw [oddCoreOf_eq_bot_of_exact hex hK, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hKnJ : ∀ x ∈ K, conjSub x J = J := by
    intro x hx
    refine Sec6Gen.eq_of_le_of_le hg (hΩ.conjInvariant x J hJΩ) hJΩ hT2 (by omega) ?_ hTJ
    intro v hv
    rw [mem_conjSub_iff]
    have h1 := hTcK x hx v hv
    have : x⁻¹ * v * x = v := by
      calc x⁻¹ * v * x = x⁻¹ * (v * x) := by group
        _ = x⁻¹ * (x * v) := by rw [h1]
        _ = v := by group
    rw [this]
    exact hTJ hv
  have hQcJ : ∀ j ∈ J, ∀ v ∈ Q, v * j = j * v := by
    intro j hj v hv
    have h1 := Sec6Gen.commutator_mem_oddCoreOf_of_centralizes hzJ hTsyl hQ2
      (fun y hy => hKnJ y (hQ.1 hy)) (fun r hr v hv => hTQc r hr v hv) j hj v hv
    rw [oddCoreOf_eq_bot_of_exact hex hJΩ, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hJnK : ∀ y ∈ J, conjSub y K = K := by
    intro y hy
    refine Sec6Gen.eq_of_le_of_le hg (hΩ.conjInvariant y K hK) hK hQ2 (by omega) ?_ hQ.1
    intro v hv
    rw [mem_conjSub_iff]
    have h1 := hQcJ y hy v hv
    have : y⁻¹ * v * y = v := by
      calc y⁻¹ * v * y = y⁻¹ * (v * y) := by group
        _ = y⁻¹ * (y * v) := by rw [h1]
        _ = v := by group
    rw [this]
    exact hQ.1 hv
  intro k hk j hj
  have hcK : ⁅k, j⁆ ∈ K := by
    have h1 : j * k⁻¹ * j⁻¹ ∈ K := by
      have := conj_mem_conjSub (n := j) (K.inv_mem hk)
      rwa [hJnK j hj] at this
    have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hk h1
  have hcJ : ⁅k, j⁆ ∈ J := by
    have h1 : k * j * k⁻¹ ∈ J := by
      have := conj_mem_conjSub (n := k) hj
      rwa [hKnJ k hk] at this
    have e : ⁅k, j⁆ = (k * j * k⁻¹) * j⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact J.mul_mem h1 (J.inv_mem hj)
  have h4 := hΩ.omega4_commutes hex hK hJΩ hne.symm
  by_cases h1 : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1
  · exact h4.2 h1 k hk j hj
  · have h0 : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 0 := by
      have := h4.1
      omega
    have hodd : Odd (Nat.card ↥(K ⊓ J)) := by
      have hpos : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
      rcases padicValNat.eq_zero_iff.mp h0 with h | h | h
      · exact absurd h (by norm_num)
      · exact absurd h hpos
      · exact Nat.odd_iff.mpr (by omega)
    have hn : K ≤ Subgroup.normalizer ((K ⊓ J : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨hhK, hhJ⟩
        refine ⟨K.mul_mem (K.mul_mem hx hhK) (K.inv_mem hx), ?_⟩
        have := conj_mem_conjSub (n := x) hhJ
        rwa [hKnJ x hx] at this
      · rintro ⟨hhK, hhJ⟩
        have e : h = x⁻¹ * (x * h * x⁻¹) * x := by group
        refine ⟨?_, ?_⟩
        · rw [e]
          exact K.mul_mem (K.mul_mem (K.inv_mem hx) hhK) hx
        · rw [e]
          have := conj_mem_conjSub (n := x⁻¹) hhJ
          rw [hKnJ x⁻¹ (K.inv_mem hx), inv_inv] at this
          exact this
    have hle : K ⊓ J ≤ oddCoreOf K := le_oddCoreOf_of_normalizes_of_odd' inf_le_left hn hodd
    rw [oddCoreOf_eq_bot_of_exact hex hK, le_bot_iff] at hle
    have hmem : ⁅k, j⁆ ∈ K ⊓ J := ⟨hcK, hcJ⟩
    rw [hle] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

theorem mem_omegaNbr_of_le_centralizer3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hJc : J ≤ Subgroup.centralizer ({z} : Set G)) :
    J ∈ omegaNbr Ω K := by
  have hg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨R, hR, hRJ, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have h8 := Sec6Gen.eight_le_of_mem_RSet hg hR
  exact ⟨hJ, hne, R, hR, hRJ.1, Sec6Gen.le_normalizer_of_le_centralizer hg hK hJ hne.symm hz hRJ.1
    hRJ.2.1 (by omega) (hRJ.1.trans hJc)⟩

theorem commutes_of_twin3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) : Commutes K J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4_commutes hex hK hJ hKJ
  exact h3 (le_antisymm h2 h1)

theorem nbhd_imp_of_twin3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K K' : Subgroup G} (hK' : K' ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hcomm : Commutes K K') :
    ∀ L ∈ Ω, ((L = K ∨ Commutes L K) → (L = K' ∨ Commutes L K')) := by
  intro L hL h
  rcases h with rfl | hc
  · exact Or.inr hcomm
  · by_cases hLK' : L = K'
    · exact Or.inl hLK'
    · right
      have hLc : L ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hc x hx z hz.mem)
      have hnbr := mem_omegaNbr_of_le_centralizer3 hΩ hK' hL hLK' hz' hLc
      have := commutes_of_mem_omegaNbr3 hΩ hex hK' hnbr
      exact fun a ha b hb => (this b hb a ha).symm

theorem nbhd_eq_of_twin3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hcomm : Commutes K K') :
    ∀ L ∈ Ω, ((L = K ∨ Commutes L K) ↔ (L = K' ∨ Commutes L K')) := fun L hL =>
  ⟨nbhd_imp_of_twin3 hΩ hex hK' hz hz' hcomm L hL,
    nbhd_imp_of_twin3 hΩ hex hK hz' hz (fun a ha b hb => (hcomm b hb a ha).symm) L hL⟩

end Nbr

end CFSG.ClassicalInvolution.Q3.Q3T7E9
