module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

private theorem cq_normal_subgroupOf_commutator {Q : Type*} [Group Q] {X K : Subgroup Q}
    (hXK : X ≤ Subgroup.normalizer (K : Set Q)) : (⁅X, K⁆.subgroupOf K).Normal := by
  have hJK : ⁅X, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXK hx) k).1 hk) (K.inv_mem hk)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2 fun a ha => ?_
  have key : ∀ a ∈ K, ∀ y ∈ ⁅X, K⁆, a * y * a⁻¹ ∈ ⁅X, K⁆ := by
    intro a ha
    have : ⁅X, K⁆ ≤ (⁅X, K⁆).comap (MulAut.conj a).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun x hx b hb => ?_
      show a * ⁅x, b⁆ * a⁻¹ ∈ ⁅X, K⁆
      have e : a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆⁻¹ * ⁅x, a * b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (⁅X, K⁆).mul_mem ((⁅X, K⁆).inv_mem (Subgroup.commutator_mem_commutator hx ha))
        (Subgroup.commutator_mem_commutator hx (K.mul_mem ha hb))
    exact fun y hy => this hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key a ha y
  · intro h
    have := key a⁻¹ (K.inv_mem ha) _ h
    have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rwa [e] at this

private theorem cq_normal_le_center_or_eq_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNorm : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have hmem : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa [π] using hmem
  · right
    have hNZ : ∀ x : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, x = n * z := by
      intro x
      have hx : π x ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      have : π (n⁻¹ * x) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hcomm : ∀ a b : Q ⧸ N, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
      obtain ⟨n, hn, z, hz, rfl⟩ := hNZ x
      obtain ⟨m, hm, w, hw, rfl⟩ := hNZ y
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      simp only [map_mul, hn1, hm1, one_mul]
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    have : Group.IsPerfect Q := ⟨hperf⟩
    have : IsMulCommutative (Q ⧸ N) := ⟨⟨hcomm⟩⟩
    have : Subsingleton (Q ⧸ N) := Group.IsPerfect.subsingleton_of_isMulCommutative
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk' N x) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this

private theorem cq_commutator_eq_of_isQuasisimple {Q : Type*} [Group Q] {X K : Subgroup Q}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hXK : X ≤ Subgroup.normalizer (K : Set Q))
    (hnc : ¬ X ≤ Subgroup.centralizer (K : Set Q)) : ⁅X, K⁆ = K := by
  have hJK : ⁅X, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXK hx) k).1 hk) (K.inv_mem hk)
  have hn := cq_normal_subgroupOf_commutator hXK
  rcases cq_normal_le_center_or_eq_top hK (⁅X, K⁆.subgroupOf K) with hc | htop
  · exfalso
    apply hnc
    have hJcent : ⁅X, K⁆ ≤ Subgroup.centralizer (K : Set Q) := by
      intro j hj k hk
      have hjK : j ∈ K := hJK hj
      have := Subgroup.mem_center_iff.1
        (hc (show (⟨j, hjK⟩ : ↥K) ∈ ⁅X, K⁆.subgroupOf K from (Subgroup.mem_subgroupOf).2 hj))
        ⟨k, hk⟩
      exact congrArg Subtype.val this
    have h1 : ⁅⁅X, K⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJcent
    have h2 : ⁅⁅K, X⁆, K⁆ = ⊥ := by rwa [Subgroup.commutator_comm K X]
    have h3 : ⁅⁅K, K⁆, X⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.1⟩
    rw [hperf] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rwa [Subgroup.commutator_comm])
  · exact le_antisymm hJK (by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ ⁅X, K⁆.subgroupOf K := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf).1 this)

theorem commutator_eq_of_isQuasisimple_of_not_le {G : Type*} [Group G] {L A : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ A ≤ L ⊔ Subgroup.centralizer (L : Set G)) : ⁅L, A⁆ = L := by
  have hnc : ¬ A ≤ Subgroup.centralizer (L : Set G) := fun h => hnot (h.trans le_sup_right)
  have h := cq_commutator_eq_of_isQuasisimple hq hAN hnc
  rwa [Subgroup.commutator_comm] at h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
