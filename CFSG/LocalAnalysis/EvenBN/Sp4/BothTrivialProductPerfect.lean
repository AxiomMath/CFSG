module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct

open Subgroup CFSG.Open CFSG.SeitzReduction
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Perfect

variable {G : Type*} [Group G]

theorem perfect_le_of_mul_mem_iff {H M : Subgroup G} (hM : ⁅M, M⁆ = M)
    (hHM : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ H ↔ (a ∈ H ↔ b ∈ H)) : M ≤ H := by
  rw [← hM, commutator_le]
  intro a ha b hb
  rw [commutatorElement_def, hHM _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb),
    hHM _ (mul_mem ha hb) _ (inv_mem ha), hHM _ ha _ hb, inv_mem_iff, inv_mem_iff]
  tauto

theorem mem_centralizer_sup {H K : Subgroup G} {x : G} (hH : x ∈ centralizer (H : Set G))
    (hK : x ∈ centralizer (K : Set G)) : x ∈ centralizer ((H ⊔ K : Subgroup G) : Set G) :=
  zpowers_le.1 (le_centralizer_iff.1 (sup_le (le_centralizer_iff.1 (zpowers_le.2 hH))
    (le_centralizer_iff.1 (zpowers_le.2 hK))))

theorem exists_inv_mul_mem_centralizer_of_perfect {A M : Subgroup G}
    [Group.IsSolvable (Outer A)] (hM : ⁅M, M⁆ = M) (hMA : M ≤ normalizer (A : Set G)) {m : G}
    (hm : m ∈ M) : ∃ a ∈ A, a⁻¹ * m ∈ centralizer (A : Set G) := by
  have : Group.IsPerfect M := isPerfect_iff.2 hM
  obtain ⟨⟨a, haA⟩, ha⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (A.normalizerMonoidHom.comp (inclusion hMA)) ⟨m, hm⟩
  refine ⟨a, haA, mem_centralizer_iff.2 fun x hx => ?_⟩
  have h := congrArg (fun f : MulAut A => ((f ⟨x, hx⟩ : A) : G)) ha
  simp only [MonoidHom.coe_comp, Function.comp_apply, normalizerMonoidHom_apply_apply_coe,
    coe_inclusion, MulAut.conj_apply, MulMemClass.mk_mul_mk, coe_mul, InvMemClass.coe_inv] at h
  calc x * (a⁻¹ * m) = a⁻¹ * (a * x * a⁻¹) * m := by group
    _ = a⁻¹ * (m * x * m⁻¹) * m := by rw [h]
    _ = a⁻¹ * m * x := by group

theorem perfect_le_of_forall_inv_mul_mem {N C M : Subgroup G} [Group.IsSolvable C]
    (hCN : C ≤ normalizer (N : Set G)) (hM : ⁅M, M⁆ = M) (hMN : M ≤ normalizer (N : Set G))
    (hMC : ∀ m ∈ M, ∃ n ∈ N, n⁻¹ * m ∈ C) : M ≤ N := by
  have : Group.IsPerfect M := isPerfect_iff.2 hM
  let π := QuotientGroup.mk' (N.subgroupOf (normalizer (N : Set G)))
  let ψ := π.comp (inclusion hCN)
  have hrange : ∀ x : M, π (inclusion hMN x) ∈ ψ.range := fun x => by
    obtain ⟨n, hn, hc⟩ := hMC x x.2
    refine ⟨⟨_, hc⟩, ?_⟩
    simp only [ψ, π, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, mem_subgroupOf]
    have e : (((inclusion hCN ⟨n⁻¹ * x, hc⟩)⁻¹ * inclusion hMN x : normalizer (N : Set G)) : G) =
        (x : G)⁻¹ * n * x := by
      simp
    rw [e]
    exact (mem_normalizer_iff''.1 (hMN x.2) n).1 hn
  have : Group.IsSolvable ψ.range := Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  intro m hm
  have h1 := DFunLike.congr_fun (CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    ((π.comp (inclusion hMN)).codRestrict ψ.range hrange)) ⟨m, hm⟩
  rw [MonoidHom.one_apply, Subtype.ext_iff, MonoidHom.codRestrict_apply] at h1
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end Perfect

section Factors

variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}

theorem mul_mem_normalizer_iff_of_perm (hne : G₁ ≠ G₂)
    (hperm₁ : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂)
    (hperm₂ : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₂.map (MulAut.conj g).toMonoidHom = G₂ ∨ G₂.map (MulAut.conj g).toMonoidHom = G₁)
    {a b : G} (ha : a ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (hb : b ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    a * b ∈ normalizer (G₁ : Set G) ↔
      (a ∈ normalizer (G₁ : Set G) ↔ b ∈ normalizer (G₁ : Set G)) := by
  simp only [F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom]
  rw [← F4Pilot.map_conj_map_conj_toMonoidHom]
  rcases hperm₁ b hb with hb1 | hb1 <;> rw [hb1]
  · simp
  · rcases hperm₁ a ha with ha1 | ha1 <;> rcases hperm₂ a ha with ha2 | ha2
    · rw [ha1, ha2]
      simp
    · exact absurd (F4Pilot.map_conj_toMonoidHom_inj.1 (ha1.trans ha2.symm)) hne
    · exact absurd (F4Pilot.map_conj_toMonoidHom_inj.1 (ha1.trans ha2.symm)) hne
    · rw [ha1, ha2]
      simp

theorem le_normalizer_of_perm (hne : G₁ ≠ G₂)
    (hperm₁ : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂)
    (hperm₂ : ∀ g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G),
      G₂.map (MulAut.conj g).toMonoidHom = G₂ ∨ G₂.map (MulAut.conj g).toMonoidHom = G₁)
    {M : Subgroup G} (hM : ⁅M, M⁆ = M) (hMN : M ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    M ≤ normalizer (G₁ : Set G) :=
  perfect_le_of_mul_mem_iff hM fun _ ha _ hb =>
    mul_mem_normalizer_iff_of_perm hne hperm₁ hperm₂ (hMN ha) (hMN hb)

theorem le_normalizer_left_of_isQuasisimple (hq₁ : CFSG.Open.IsQuasisimple G₁)
    (hq₂ : CFSG.Open.IsQuasisimple G₂) (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    {M : Subgroup G} (hM : ⁅M, M⁆ = M)
    (hMN : M ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : M ≤ normalizer (G₁ : Set G) := by
  obtain ⟨hperf₁, hbot₁, hn₁⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq₁
  obtain ⟨hperf₂, hbot₂, hn₂⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq₂
  have hne : G₁ ≠ G₂ := by
    rintro rfl
    exact hbot₁ (by rw [← hperf₁, commutator_eq_bot_iff_le_centralizer.2 h₁₂])
  exact le_normalizer_of_perm hne
    (fun g hg => F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf₁ hbot₁ hn₁ hn₂ hg)
    (fun g hg => F4Pilot.map_conj_eq_or_eq_of_perfect (le_centralizer_iff.1 h₁₂) hperf₂ hbot₂
      hn₂ hn₁ (by rwa [sup_comm])) hM hMN

theorem exists_inv_mul_mem_centralizer_sup [Group.IsSolvable (Outer G₁)]
    [Group.IsSolvable (Outer G₂)] (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) {M : Subgroup G}
    (hM : ⁅M, M⁆ = M) (hM₁ : M ≤ normalizer (G₁ : Set G)) (hM₂ : M ≤ normalizer (G₂ : Set G))
    {m : G} (hm : m ∈ M) :
    ∃ g ∈ G₁ ⊔ G₂, g⁻¹ * m ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  obtain ⟨a, haA, ha⟩ := exists_inv_mul_mem_centralizer_of_perfect hM hM₁ hm
  obtain ⟨b, hbB, hb⟩ := exists_inv_mul_mem_centralizer_of_perfect hM hM₂ hm
  have hab : a * b = b * a := mem_centralizer_iff.1 (h₁₂ hbB) a haA
  refine ⟨a * b, mul_mem (mem_sup_left haA) (mem_sup_right hbB), mem_centralizer_sup ?_ ?_⟩
  · rw [show (a * b)⁻¹ * m = b⁻¹ * (a⁻¹ * m) by group]
    exact mul_mem (inv_mem (h₁₂ hbB)) ha
  · rw [show (a * b)⁻¹ * m = a⁻¹ * (b⁻¹ * m) by rw [hab]; group]
    exact mul_mem (inv_mem (le_centralizer_iff.1 h₁₂ haA)) hb

end Factors

theorem perfect_le_of_le_normalizer_sup
    {G : Type} [Group G] [Finite G] {G₁ G₂ : Subgroup G} (hq₁ : CFSG.Open.IsQuasisimple G₁)
    (hq₂ : CFSG.Open.IsQuasisimple G₂) (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hOut₁ : Group.IsSolvable (Outer G₁)) (hOut₂ : Group.IsSolvable (Outer G₂))
    (hC : Odd (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))))
    {M : Subgroup G} (hM : ⁅M, M⁆ = M)
    (hMN : M ≤ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : M ≤ G₁ ⊔ G₂ := by
  have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hC
  exact perfect_le_of_forall_inv_mul_mem (centralizer_le_normalizer _) hM hMN fun _ hm =>
    exists_inv_mul_mem_centralizer_sup h₁₂ hM
      (le_normalizer_left_of_isQuasisimple hq₁ hq₂ h₁₂ hM hMN)
      (le_normalizer_left_of_isQuasisimple hq₂ hq₁ (le_centralizer_iff.1 h₁₂) hM
        (by rwa [sup_comm])) hm

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct
