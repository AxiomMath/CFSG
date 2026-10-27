module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Goldschmidt

open CFSG.Open Bender CFSG.ComponentClassification.AschbacherTheorem3

theorem mem_sylowCenter_of_sq_eq_one {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (hB : fusionBenderBorel G q k) (hq : 2 ≤ q) (Q : Sylow 2 G) {t : G}
    (ht : t ∈ (Q : Subgroup G)) (ht2 : t ^ 2 = 1) : t ∈ sylowCenter (Q : Subgroup G) := by
  by_cases ht1 : t = 1
  · rw [ht1]
    exact (sylowCenter _).one_mem
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB Q
  have hM := isStronglyEmbedded_of_fusion hSE
  have hZnt : 1 < Nat.card (sylowCenter (Q : Subgroup G)) := by rw [hZcard]; omega
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hZnt)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hmemN : ∀ x ∈ (Q : Subgroup G), x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    fun x hx => Subgroup.le_normalizer hx
  obtain ⟨g, hg, hgz⟩ := hM.involutions_conjugate_in (hmemN _ (sylowCenter_le _ hzZ))
    ⟨hz1', hZ2 _ hzZ⟩ (hmemN _ ht) ⟨ht1, ht2⟩
  have hmem := conj_mem_sylowCenter hg hzZ
  have hgz' : g⁻¹ * z * g = t := hgz
  rw [hgz'] at hmem
  exact hmem

theorem mem_center_of_conj_eq_one {G : Type*} [Group G] {g : G} (h : MulAut.conj g = 1) :
    g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro x
  have hx := congrArg (fun φ : MulAut G => φ x) h
  change g * x * g⁻¹ = x at hx
  calc x * g = g * x * g⁻¹ * g := by rw [hx]
    _ = g * x := by group

theorem card_le_omegaOne_of_bender {G : Type} [Group G] [Finite G] (hG : fusionIsBenderGroup G)
    (Q : Sylow 2 G) (A : Subgroup (MulAut G)) (h1 : ∀ α ∈ A, α * α = 1)
    (h2 : ∀ α ∈ A, ∀ q ∈ (Q : Subgroup G), α q ∈ (Q : Subgroup G))
    (h3 : ∀ α ∈ A, ∀ q ∈ (Q : Subgroup G), q ^ 2 = 1 → α q = q)
    (h4 : ∀ α ∈ A, ∀ q ∈ (Q : Subgroup G), q⁻¹ * α q ∈ omegaOne (Q : Subgroup G)) :
    Nat.card A ≤ Nat.card (omegaOne (Q : Subgroup G)) := by
  classical
  have hD := BenderExt.benderData_of_isBenderGroup hG
  obtain ⟨q, k, hq4, hB⟩ := hD.borel
  obtain ⟨hSE, hZ2, -, -⟩ := benderBorel_sylowCenter hB Q
  have : IsSimpleGroup G := hD.simple
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      apply hSE.1
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
      rw [← (Subgroup.mem_center_iff.mp hx t), mul_inv_cancel_right]
  have hΩ : omegaOne (Q : Subgroup G) ≤ sylowCenter (Q : Subgroup G) :=
    (Subgroup.closure_le _).mpr fun t ht =>
      mem_sylowCenter_of_sq_eq_one hB (by omega) Q ht.1 ht.2
  have hinner : ∀ α ∈ A, ∃ s ∈ omegaOne (Q : Subgroup G), α = MulAut.conj s := by
    intro α hα
    by_cases hconj : ∃ s ∈ (Q : Subgroup G), α = MulAut.conj s
    · obtain ⟨s, hs, rfl⟩ := hconj
      refine ⟨s, mem_omegaOne hs ?_, rfl⟩
      have h := h1 _ hα
      rw [← map_mul] at h
      have hc := mem_center_of_conj_eq_one h
      rw [hcenter, Subgroup.mem_bot] at hc
      rw [sq]
      exact hc
    · exfalso
      push Not at hconj
      have hZ : ∀ z ∈ sylowCenter (Q : Subgroup G), α z = z := fun z hz =>
        h3 α hα z (sylowCenter_le _ hz) (hZ2 z hz)
      have hpow : ∃ n : ℕ, α ^ (2 ^ n) = 1 := ⟨1, by rw [pow_one, sq]; exact h1 α hα⟩
      obtain ⟨-, -, t, ht, htZ⟩ := hD.aut Q α (h2 α hα) hZ hpow hconj
      exact htZ (hΩ (h4 α hα t ht))
  choose s hs hαs using hinner
  let ι : A → omegaOne (Q : Subgroup G) := fun α => ⟨s α α.2, hs α α.2⟩
  have hι : Function.Injective ι := by
    intro α β h
    apply Subtype.ext
    have h' : s α α.2 = s β β.2 := congrArg Subtype.val h
    rw [hαs α α.2, hαs β β.2, h']
  exact Nat.card_le_card_of_injective ι hι

end Goldschmidt

end CFSG.ComponentClassification.AschbacherToolkit
