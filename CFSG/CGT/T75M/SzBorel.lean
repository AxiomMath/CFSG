module

public import CFSG.CGT.Timmesfeld75.BenderInputs4
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
public import CFSG.CGT.T75M.SzData

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki

variable {K : Type} [Group K] [Finite K]

theorem mem_normalizer_sylow_of_mem_normalizer (hK : IsBenderGroup K) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) (Q : Sylow 2 K) (hTQ : T ≤ (Q : Subgroup K)) {g : K}
    (hg : g ∈ Subgroup.normalizer (T : Set K)) :
    g ∈ Subgroup.normalizer (Q : Set K) := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htt : t * t = 1 := elemAbelian_mul_self hT.1 ht
  have hcomm : ∀ q ∈ (Q : Subgroup K), ∀ s ∈ T, q * s = s * q := fun q hq s hs =>
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q (hTQ hs)
      (elemAbelian_mul_self hT.1 hs) q hq).eq.symm
  have hle : conjSubgroup g (Q : Subgroup K) ≤ Subgroup.normalizer (Q : Set K) := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    refine centralizer_le_normalizer_of_isBenderGroup hK Q (hTQ ht) htt ht1' ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgT : g⁻¹ * t * g ∈ T := by
      have h2 : t ∈ conjSubgroup g T := by
        rw [mem_normalizer_iff_conjSubgroup_eq.1 hg]; exact ht
      exact mem_conjSubgroup.1 h2
    have h3 : (g⁻¹ * x * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * x * g) :=
      hcomm _ hx _ hgT
    calc x * t = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h3]
      _ = t * x := by group
  have hP : IsPGroup 2 (conjSubgroup g (Q : Subgroup K)) := Q.isPGroup'.map _
  have hle2 := le_of_isPGroup_of_le_normalizer hP Q hle
  exact mem_normalizer_iff_conjSubgroup_eq.2 (conjSubgroup_eq_of_le hle2)

theorem eq_one_of_mem_normalizer_two_sylows (hK : IsBenderGroup K) (Q : Sylow 2 K) {k : K}
    (hk : k ∉ Subgroup.normalizer (Q : Set K)) {g : K}
    (hg1 : g ∈ Subgroup.normalizer (Q : Set K))
    (hg2 : g ∈ Subgroup.normalizer ((conjSubgroup k (Q : Subgroup K) : Subgroup K) : Set K))
    (hgg : g * g = 1) : g = 1 := by
  by_contra hg1'
  have hse := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q
  have hodd := hse.2.2 k hk
  set M : Subgroup K := Subgroup.normalizer (Q : Set K) with hM
  have hmem : g ∈ M ⊓ M.map (MulAut.conj k).toMonoidHom := by
    refine ⟨hg1, ?_⟩
    have h := mem_normalizer_conjSubgroup_iff.1 hg2
    exact ⟨k⁻¹ * g * k, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hdvd : orderOf (⟨g, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj k).toMonoidHom)) ∣
      Nat.card ↥(M ⊓ M.map (MulAut.conj k).toMonoidHom) := orderOf_dvd_natCard _
  have hord : orderOf (⟨g, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj k).toMonoidHom)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1'
  rw [hord] at hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem mem_center_of_mem_normalizer_sylow (hK : IsBenderGroup K) (Q : Sylow 2 K) {g : K}
    (hg : g ∈ Subgroup.normalizer (Q : Set K)) (hgg : g * g = 1) :
    g ∈ (Subgroup.center (Q : Subgroup K)).map (Q : Subgroup K).subtype := by
  have hP : IsPGroup 2 (Subgroup.zpowers g) := by
    by_cases hg1 : g = 1
    · rw [hg1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_card (n := 0) (by simp)
    · have : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, this]; simp)
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (Q : Set K) := by
    rw [Subgroup.zpowers_le]; exact hg
  have hgQ : g ∈ (Q : Subgroup K) :=
    le_of_isPGroup_of_le_normalizer hP Q hle (Subgroup.mem_zpowers g)
  refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro q
  exact Subtype.ext
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hgQ hgg q
      q.2).eq.symm

end CFSG.CGT.T75M
