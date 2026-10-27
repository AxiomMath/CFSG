module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

@[expose] def GenerationStmt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    ¬ E ≤ Subgroup.centralizer (K : Set Y) →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) →
    (J.subgroupOf (K ⊓ Subgroup.centralizer (E : Set Y))).Normal →
    CFSG.Open.IsQuasisimple ↥J → 3 ∣ Nat.card ↥J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    ∃ b ∈ E, b ≠ 1 ∧ ¬ ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
      (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal

@[expose] def GenFaithful : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → IsChevTwo (↥K ⧸ Subgroup.center ↥K) →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    (∀ b ∈ E, b ∈ Subgroup.centralizer (K : Set Y) → b = 1) →
    ¬ E ≤ Subgroup.centralizer (K : Set Y) →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) →
    (J.subgroupOf (K ⊓ Subgroup.centralizer (E : Set Y))).Normal →
    CFSG.Open.IsQuasisimple ↥J → 3 ∣ Nat.card ↥J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    ∃ b ∈ E, b ≠ 1 ∧ ¬ ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
      (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal

private theorem ys08_isQuasisimple_native {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

private theorem ys08_not_comm {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (h : ∀ a b : Q, a * b = b * a) : False := by
  have hc : Subgroup.center Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    exact fun y => h y x
  have := hQ.2.toNontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  apply hz
  rw [QuotientGroup.eq_one_iff, hc]
  trivial

theorem notNormal_of_central {Y : Type} [Group Y] [Finite Y] (K E J : Subgroup Y)
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hK3 : GLAPPrimeCore 3 ↥K = ⊥)
    (hEK : ¬ E ≤ Subgroup.centralizer (K : Set Y))
    (hJ : J ≤ K ⊓ Subgroup.centralizer (E : Set Y)) (hJq : CFSG.Open.IsQuasisimple ↥J)
    {b : Y} (hbE : b ∈ E) (hbK : b ∈ Subgroup.centralizer (K : Set Y)) :
    ¬ ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
      (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal := by
  intro hN
  have hXK : K ⊓ Subgroup.centralizer ({b} : Set Y) = K := by
    refine inf_eq_left.2 fun k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hbK k hk
  have hO : GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) = ⊥ := by
    rw [hXK]
    unfold GLAPPrimeCoreOf
    rw [hK3, Subgroup.map_bot]
  have hJb : J ≤ K ⊓ Subgroup.centralizer ({b} : Set Y) :=
    hJ.trans (inf_le_inf_left K (Subgroup.centralizer_le (by simpa using hbE)))
  have hJK : J ≤ K := hJ.trans inf_le_left
  have hconj : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have hkX : k ∈ K ⊓ Subgroup.centralizer ({b} : Set Y) := by rw [hXK]; exact hk
    have h1 := hN.conj_mem ⟨j, hJb hj⟩
      (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hj)) ⟨k, hkX⟩
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rwa [hO, sup_bot_eq] at h2
  have hJn : (J.subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hconj g g.2 x hx
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (ys08_isQuasisimple_native hKq) hJn with h | h
  · have hKJ : K ≤ J := Subgroup.subgroupOf_eq_top.mp h
    apply hEK
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hJ (hKJ hk)).2 e he).symm
  · refine ys08_not_comm hJq fun a c => ?_
    have ha : (⟨a.1, hJK a.2⟩ : ↥K) ∈ Subgroup.center ↥K := h (Subgroup.mem_subgroupOf.2 a.2)
    have h1 := Subgroup.mem_center_iff.1 ha ⟨c.1, hJK c.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val h1.symm)

theorem generation_of_faithful (h : GenFaithful) : GenerationStmt := by
  intro Y _ _ K E J hKq hK3 hKc hEN hEel hE9 hEK hJle hJn hJq h3 hJL
  by_cases hcyc : ∃ b ∈ E, b ≠ 1 ∧ b ∈ Subgroup.centralizer (K : Set Y)
  · obtain ⟨b, hbE, hb1, hbK⟩ := hcyc
    exact ⟨b, hbE, hb1, notNormal_of_central K E J hKq hK3 hEK hJle hJq hbE hbK⟩
  · push Not at hcyc
    exact h Y K E J hKq hK3 hKc hEN hEel hE9 (fun b hb hbK => by_contra fun h1 => hcyc b hb h1 hbK)
      hEK hJle hJn hJq h3 hJL

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
