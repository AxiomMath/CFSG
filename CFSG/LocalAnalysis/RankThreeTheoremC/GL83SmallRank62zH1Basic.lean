module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem k631a_mem_of_pow_mem {N : Subgroup G} {g : G} {m n : ℕ} (h : Nat.Coprime m n)
    (hm : g ^ m ∈ N) (hn : g ^ n ∈ N) : g ∈ N := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime h
  have e : g = (g ^ m) ^ u * (g ^ n) ^ v := by
    calc g = g ^ (u * (m : ℤ) + v * (n : ℤ)) := by rw [huv, zpow_one]
      _ = (g ^ m) ^ u * (g ^ n) ^ v := by
        rw [zpow_add, zpow_mul', zpow_mul']
        simp
  rw [e]
  exact N.mul_mem (N.zpow_mem hm u) (N.zpow_mem hn v)

theorem k631a_exists_pow_eq_one {f : ℕ} {P : Subgroup G} (hP : IsPGroup f P) {g : G}
    (hg : g ∈ P) : ∃ n : ℕ, g ^ f ^ n = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨g, hg⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem k631a_eq_one_of_mem_inf [Finite G] {f : ℕ} {P O : Subgroup G} (hP : IsPGroup f P)
    (hO : Nat.Coprime f (Nat.card O)) {g : G} (hgP : g ∈ P) (hgO : g ∈ O) : g = 1 := by
  obtain ⟨n, hn⟩ := k631a_exists_pow_eq_one hP hgP
  have h1 : orderOf g ∣ f ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf g ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hgO
  have h3 : Nat.Coprime (f ^ n) (Nat.card O) := hO.pow_left n
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

theorem k631a_exists_invariant_sylow [Finite G] {f r : ℕ} [Fact f.Prime] [Fact r.Prime]
    {W R : Subgroup G} (hR : IsPGroup f R) (hRW : R ≤ normalizer (W : Set G))
    (hcard : ¬ f ∣ Nat.card (Sylow r W)) :
    ∃ P : Subgroup G, P ≤ W ∧ IsPGroup r P ∧ ¬ r ∣ (P.subgroupOf W).index ∧
      R ≤ normalizer (P : Set G) := by
  let ρ : ↥R →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hRW)
  let _ : MulDistribMulAction ↥R ↥W := MulDistribMulAction.compHom W ρ
  obtain ⟨S, hS⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) hcard
  have hsmul : ∀ a : ↥R, a • S = S := fun a => MulAction.mem_fixedPoints.mp hS a
  refine ⟨(S : Subgroup W).map W.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, ?_⟩
  · have h : ((S : Subgroup W).map W.subtype).subgroupOf W = (S : Subgroup W) :=
      Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
    rw [h]
    exact S.not_dvd_index
  · rw [le_normalizer_iff]
    rintro a ha _ ⟨k, hk, rfl⟩
    have h1 : (⟨a, ha⟩ : ↥R) • k ∈ (((⟨a, ha⟩ : ↥R) • S : Sylow r W) : Subgroup W) := by
      rw [Sylow.pointwise_smul_def]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨k, hk, rfl⟩
    rw [hsmul] at h1
    exact ⟨_, h1, W.normalizerMonoidHom_apply_apply_coe ⟨a, hRW ha⟩ k⟩

theorem k631a_exists_normalized_sylow [Finite G] {f r : ℕ} (hf : f.Prime) (hr : r.Prime)
    {W R : Subgroup G} (hR : IsPGroup f R) (hRW : R ≤ normalizer (W : Set G))
    (hcop : ¬ f ∣ Nat.card W) :
    ∃ P : Subgroup G, P ≤ W ∧ IsPGroup r P ∧ ¬ r ∣ (P.subgroupOf W).index ∧
      R ≤ normalizer (P : Set G) := by
  have := Fact.mk hf
  have := Fact.mk hr
  refine k631a_exists_invariant_sylow hR hRW fun hd => ?_
  obtain ⟨S⟩ : Nonempty (Sylow r W) := inferInstance
  exact hcop (hd.trans (S.card_dvd_index.trans (S : Subgroup W).index_dvd_card))

end CFSG.LocalAnalysis.RankThreeTheoremC
