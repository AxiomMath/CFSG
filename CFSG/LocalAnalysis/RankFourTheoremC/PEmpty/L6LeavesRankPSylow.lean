module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

theorem exists_sylow_inf_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ S : Sylow p N, (S : Subgroup N).map N.subtype = (P : Subgroup G) ⊓ N := by
  obtain ⟨S⟩ := Sylow.nonempty (G := N) (p := p)
  have hmapp : IsPGroup p ((S : Subgroup N).map N.subtype) := S.isPGroup'.map N.subtype
  obtain ⟨P', hP'⟩ := hmapp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hconj : (P' : Subgroup G) ⊓ N = ((P : Subgroup G) ⊓ N).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hx⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have hx' : g * a * g⁻¹ ∈ N := hx
      have := (inferInstance : N.Normal).conj_mem _ hx' g⁻¹
      rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this
    · rintro ⟨a, ⟨ha, haN⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, (inferInstance : N.Normal).conj_mem _ haN g⟩
  have h1 : Nat.card ((S : Subgroup N).map N.subtype) ≤
      Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) := by
    have hle : (S : Subgroup N).map N.subtype ≤ (P' : Subgroup G) ⊓ N :=
      le_inf hP' (Subgroup.map_subtype_le _)
    calc Nat.card ((S : Subgroup N).map N.subtype) ≤
          Nat.card ((P' : Subgroup G) ⊓ N : Subgroup G) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) := by
          rw [hconj]
          exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardeq : Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) =
      Nat.card (((P : Subgroup G) ⊓ N).subgroupOf N) :=
    (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (P : Subgroup G) ⊓ N ≤ N)).toEquiv).symm
  have hpp : IsPGroup p (((P : Subgroup G) ⊓ N).subgroupOf N) :=
    (P.isPGroup'.to_inf_left (K := N)).comap_of_injective N.subtype N.subtype_injective
  have h2 : Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) ≤ Nat.card (S : Subgroup N) := by
    obtain ⟨S₂, hS₂⟩ := hpp.exists_le_sylow
    calc Nat.card ((P : Subgroup G) ⊓ N : Subgroup G)
        = Nat.card (((P : Subgroup G) ⊓ N).subgroupOf N) := hcardeq
      _ ≤ Nat.card (S₂ : Subgroup N) := Subgroup.card_le_of_le hS₂
      _ = Nat.card (S : Subgroup N) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card ((S : Subgroup N).map N.subtype) = Nat.card (S : Subgroup N) :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hfinal : Nat.card (((P : Subgroup G) ⊓ N).subgroupOf N) =
      p ^ (Nat.card N).factorization p := by
    rw [← hcardeq, ← Sylow.card_eq_multiplicity S]
    omega
  refine ⟨Sylow.ofCard _ hfinal, ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_right

theorem exists_sylow_normalized {X : Type*} [Group X] [Finite X] {f : ℕ} [Fact f.Prime]
    (N : Subgroup X) [N.Normal] {y : X} (hy : y ^ f = 1) :
    ∃ E : Subgroup X, E ≤ N ∧ IsPGroup f E ∧
      (∀ Q : Subgroup X, Q ≤ N → IsPGroup f Q → E ≤ Q → Q = E) ∧
      y ∈ normalizer (E : Set X) ∧
      ∀ g : X, ∃ n ∈ normalizer (E : Set X), ∃ o ∈ N, g = n * o := by
  have hzp : IsPGroup f (zpowers y) := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]⟩
  obtain ⟨F, hF⟩ := hzp.exists_le_sylow
  obtain ⟨S, hS⟩ := exists_sylow_inf_normal F N
  have hyF : y ∈ (F : Subgroup X) := hF (Subgroup.mem_zpowers y)
  refine ⟨(F : Subgroup X) ⊓ N, inf_le_right, F.isPGroup'.to_inf_left, ?_, ?_, ?_⟩
  · intro Q hQN hQp hEQ
    have hQ' : IsPGroup f (Q.subgroupOf N) := hQp.comap_of_injective N.subtype N.subtype_injective
    have hSQ : (S : Subgroup N) ≤ Q.subgroupOf N := by
      intro s hs
      have : (s : X) ∈ (F : Subgroup X) ⊓ N := by
        rw [← hS]
        exact ⟨s, hs, rfl⟩
      exact hEQ this
    have := S.3 hQ' hSQ
    calc Q = (Q.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hQN).symm
      _ = (S : Subgroup N).map N.subtype := by rw [this]
      _ = _ := hS
  · refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    have hfwd : ∀ z ∈ (F : Subgroup X), ∀ h ∈ (F : Subgroup X) ⊓ N,
        z * h * z⁻¹ ∈ (F : Subgroup X) ⊓ N := fun z hz h hh =>
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hz hh.1) (Subgroup.inv_mem _ hz),
        (inferInstance : N.Normal).conj_mem _ hh.2 z⟩
    refine ⟨hfwd y hyF h, fun hh => ?_⟩
    have := hfwd y⁻¹ (Subgroup.inv_mem _ hyF) _ hh
    rwa [show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at this
  · intro g
    have h1 := Sylow.normalizer_sup_eq_top S
    rw [hS] at h1
    have hg : g ∈ normalizer ((F : Subgroup X) ⊓ N : Subgroup X) ⊔ N := by
      rw [h1]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    exact ⟨n, hn, o, ho, rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
