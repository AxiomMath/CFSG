module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

theorem exists_sylow_normalized_of_mem_normalizer {X : Type*} [Group X] [Finite X] {f : ℕ}
    [Fact f.Prime] (N : Subgroup X) {y : X} (hy : y ^ f = 1)
    (hN : y ∈ normalizer (N : Set X)) :
    ∃ E : Subgroup X, E ≤ N ∧ IsPGroup f E ∧
      (∀ Q : Subgroup X, Q ≤ N → IsPGroup f Q → E ≤ Q → Q = E) ∧
      y ∈ normalizer (E : Set X) := by
  set G₁ : Subgroup X := N ⊔ zpowers y with hG₁
  have hNG : N ≤ G₁ := le_sup_left
  have hyG : y ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hG₁n : G₁ ≤ normalizer (N : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hN)
  haveI : (N.subgroupOf G₁).Normal := Subgroup.normal_subgroupOf_iff_le_normalizer hNG |>.mpr hG₁n
  have hy' : (⟨y, hyG⟩ : G₁) ^ f = 1 := Subtype.ext (by simpa using hy)
  obtain ⟨E', hE'N, hE'p, hE'max, hE'y, -⟩ :=
    exists_sylow_normalized (N.subgroupOf G₁) hy'
  refine ⟨E'.map G₁.subtype, ?_, hE'p.map _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact hE'N he
  · intro Q hQN hQp hEQ
    have hQG : Q ≤ G₁ := hQN.trans hNG
    have hQ' : IsPGroup f (Q.subgroupOf G₁) :=
      hQp.comap_of_injective G₁.subtype G₁.subtype_injective
    have hle : E' ≤ Q.subgroupOf G₁ := fun e he => hEQ ⟨e, he, rfl⟩
    have h1 : Q.subgroupOf G₁ ≤ N.subgroupOf G₁ := fun q hq => hQN hq
    have := hE'max _ h1 hQ' hle
    calc Q = (Q.subgroupOf G₁).map G₁.subtype := (Subgroup.map_subgroupOf_eq_of_le hQG).symm
      _ = E'.map G₁.subtype := by rw [this]
  · refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    have hfwd : ∀ z ∈ normalizer (E' : Set G₁), ∀ h ∈ E'.map G₁.subtype,
        (z : X) * h * (z : X)⁻¹ ∈ E'.map G₁.subtype := by
      rintro z hz _ ⟨e, he, rfl⟩
      exact ⟨z * e * z⁻¹, (Subgroup.mem_normalizer_iff.mp hz e).mp he, rfl⟩
    refine ⟨hfwd ⟨y, hyG⟩ hE'y h, fun hh => ?_⟩
    have := hfwd ⟨y, hyG⟩⁻¹ (Subgroup.inv_mem _ hE'y) _ hh
    rwa [show (((⟨y, hyG⟩ : G₁)⁻¹ : G₁) : X) * (y * h * y⁻¹) * (((⟨y, hyG⟩ : G₁)⁻¹ : G₁) : X)⁻¹ = h
      by simp [mul_assoc]] at this

theorem exists_conj_mem_of_isPGroup {X : Type*} [Group X] [Finite X] {f : ℕ} [Fact f.Prime]
    (N S : Subgroup X) (hSN : S ≤ N) (hSp : IsPGroup f S)
    (hSmax : ∀ Q : Subgroup X, Q ≤ N → IsPGroup f Q → S ≤ Q → Q = S) {h : X} (hh : h ∈ N)
    (hhf : h ^ f = 1) : ∃ g ∈ N, g⁻¹ * h * g ∈ S := by
  let S' : Sylow f N :=
    ⟨S.subgroupOf N, hSp.comap_of_injective N.subtype N.subtype_injective, fun {Q} hQ hle => by
      have h1 : IsPGroup f (Q.map N.subtype) := hQ.map _
      have h2 : S ≤ Q.map N.subtype := fun s hs => ⟨⟨s, hSN hs⟩, hle hs, rfl⟩
      have := hSmax _ (Subgroup.map_subtype_le Q) h1 h2
      calc Q = (Q.map N.subtype).subgroupOf N :=
            (Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q).symm
        _ = S.subgroupOf N := by rw [this]⟩
  have hzp : IsPGroup f (zpowers (⟨h, hh⟩ : N)) := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    have hNf : (⟨h, hh⟩ : N) ^ f = 1 := Subtype.ext (by simpa using hhf)
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hNf, one_zpow]⟩
  obtain ⟨S₂, hS₂⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S' S₂
  have hmem : (⟨h, hh⟩ : N) ∈ (S₂ : Subgroup N) := hS₂ (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul] at hmem
  obtain ⟨s, hs, hsh⟩ := hmem
  refine ⟨(g : X), g.2, ?_⟩
  have h1 : (g : X) * (s : X) * (g : X)⁻¹ = h := congrArg Subtype.val hsh
  have h2 : (g : X)⁻¹ * h * g = s := by rw [← h1]; group
  rw [h2]
  exact hs

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
