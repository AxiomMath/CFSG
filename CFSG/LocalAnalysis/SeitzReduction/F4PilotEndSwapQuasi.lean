module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwap
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_inf_of_mem_normalizers {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf]
  exact and_congr (hA x) (hB x)

theorem eq_or_le_centralizer_of_perfect {A N : Subgroup G}
    (hA : ∀ M : Subgroup G, M ≤ A → A ≤ normalizer (M : Set G) →
      M ≤ centralizer (A : Set G) ∨ M = A)
    (hNperf : ⁅N, N⁆ = N) (hNbot : N ≠ ⊥)
    (hN : ∀ M : Subgroup G, M ≤ N → N ≤ normalizer (M : Set G) →
      M ≤ centralizer (N : Set G) ∨ M = N)
    (hAN : A ≤ normalizer (N : Set G)) (hNA : N ≤ normalizer (A : Set G)) :
    N = A ∨ N ≤ centralizer (A : Set G) := by
  have hNab : ¬ N ≤ centralizer (N : Set G) := fun h =>
    hNbot (by rw [← hNperf, commutator_eq_bot_iff_le_centralizer.2 h])
  rcases hN (N ⊓ A) inf_le_left
    (fun n hn => mem_normalizer_inf_of_mem_normalizers (le_normalizer hn) (hNA hn)) with hc | he
  ·
    right
    have hNA' : ⁅N, A⁆ ≤ N ⊓ A := by
      rw [commutator_le]
      intro n hn a ha
      rw [commutatorElement_def]
      refine mem_inf.2 ⟨?_, mul_mem ((mem_normalizer_iff.1 (hNA hn) a).1 ha) (inv_mem ha)⟩
      have h1 : a * n⁻¹ * a⁻¹ ∈ N := (mem_normalizer_iff.1 (hAN ha) n⁻¹).1 (inv_mem hn)
      have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
      rw [e]
      exact mul_mem hn h1
    have h1 : ⁅⁅N, A⁆, N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (hNA'.trans hc)
    have h2 : ⁅⁅A, N⁆, N⁆ = ⊥ := by rw [commutator_comm A N]; exact h1
    have h3 : ⁅⁅N, N⁆, A⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hNperf] at h3
    exact commutator_eq_bot_iff_le_centralizer.1 h3
  ·
    have hNle : N ≤ A := inf_eq_left.1 he
    rcases hA N hNle hAN with hc | he'
    · exact absurd (hc.trans (centralizer_le hNle)) hNab
    · exact Or.inl he'

theorem eq_or_eq_of_perfect_of_le_sup {G₁ G₂ N : Subgroup G}
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hn₁ : ∀ M : Subgroup G, M ≤ G₁ → G₁ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₁ : Set G) ∨ M = G₁)
    (hn₂ : ∀ M : Subgroup G, M ≤ G₂ → G₂ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₂ : Set G) ∨ M = G₂)
    (hNperf : ⁅N, N⁆ = N) (hNbot : N ≠ ⊥)
    (hnN : ∀ M : Subgroup G, M ≤ N → N ≤ normalizer (M : Set G) →
      M ≤ centralizer (N : Set G) ∨ M = N)
    (hN : N ≤ G₁ ⊔ G₂) (hNn : G₁ ⊔ G₂ ≤ normalizer (N : Set G)) : N = G₁ ∨ N = G₂ := by
  rcases eq_or_le_centralizer_of_perfect hn₁ hNperf hNbot hnN (le_sup_left.trans hNn)
    (hN.trans (sup_le_normalizer_left_of_le_centralizer h₁₂)) with h | hc₁
  · exact Or.inl h
  rcases eq_or_le_centralizer_of_perfect hn₂ hNperf hNbot hnN (le_sup_right.trans hNn)
    (hN.trans (sup_le_normalizer_right_of_le_centralizer h₁₂)) with h | hc₂
  · exact Or.inr h
  exfalso
  have hNN : N ≤ centralizer (N : Set G) :=
    hN.trans (sup_le (le_centralizer_iff.1 hc₁) (le_centralizer_iff.1 hc₂))
  exact hNbot (by rw [← hNperf, commutator_eq_bot_iff_le_centralizer.2 hNN])

theorem dichotomy_map_mulAut {A : Subgroup G} (φ : MulAut G)
    (hA : ∀ M : Subgroup G, M ≤ A → A ≤ normalizer (M : Set G) →
      M ≤ centralizer (A : Set G) ∨ M = A) (M : Subgroup G) (hMA : M ≤ A.map φ.toMonoidHom)
    (hAM : A.map φ.toMonoidHom ≤ normalizer (M : Set G)) :
    M ≤ centralizer ((A.map φ.toMonoidHom : Subgroup G) : Set G) ∨ M = A.map φ.toMonoidHom := by
  have hM'A : M.comap φ.toMonoidHom ≤ A := by
    intro x hx
    rw [mem_comap] at hx
    obtain ⟨a, ha, hax⟩ := hMA hx
    have hxa : a = x := φ.injective (by simpa using hax)
    exact hxa ▸ ha
  have hAM' : A ≤ normalizer ((M.comap φ.toMonoidHom : Subgroup G) : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact mem_normalizer_iff.1 (hAM ⟨a, ha, rfl⟩) (φ x)
  rcases hA _ hM'A hAM' with h | h
  · left
    intro m hm
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hm' : φ.symm m ∈ M.comap φ.toMonoidHom := by
      rw [mem_comap]
      simpa using hm
    have hc := congrArg φ (mem_centralizer_iff.1 (h hm') a ha)
    simpa using hc
  · right
    refine le_antisymm hMA ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← h] at ha
    exact ha

variable {G₁ G₂ : Subgroup G} {t : G}

theorem map_conj_eq_or_eq_of_perfect (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hperf : ⁅G₁, G₁⁆ = G₁) (hbot : G₁ ≠ ⊥)
    (hn₁ : ∀ M : Subgroup G, M ≤ G₁ → G₁ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₁ : Set G) ∨ M = G₁)
    (hn₂ : ∀ M : Subgroup G, M ≤ G₂ → G₂ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₂ : Set G) ∨ M = G₂) {g : G}
    (hg : g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    G₁.map (MulAut.conj g).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj g).toMonoidHom = G₂ :=
  eq_or_eq_of_perfect_of_le_sup h₁₂ hn₁ hn₂ (by rw [← map_commutator, hperf])
    (fun h => hbot ((map_eq_bot_iff_of_injective G₁ (MulAut.conj g).injective).1 h))
    (dichotomy_map_mulAut (MulAut.conj g) hn₁) (map_conj_le_sup_of_mem_normalizer hg)
    (sup_le_normalizer_map_conj (sup_le_normalizer_left_of_le_centralizer h₁₂) hg)

theorem false_of_simple_of_swap_of_perfect [Finite G] [IsSimpleGroup G] (ht : orderOf t = 2)
    (hperf : ⁅G₁, G₁⁆ = G₁) (hbot : G₁ ≠ ⊥)
    (hn₁ : ∀ M : Subgroup G, M ≤ G₁ → G₁ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₁ : Set G) ∨ M = G₁)
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : False := by
  have hn₂ : ∀ M : Subgroup G, M ≤ G₂ → G₂ ≤ normalizer (M : Set G) →
      M ≤ centralizer (G₂ : Set G) ∨ M = G₂ := by
    subst hswap
    exact dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hne : G₁ ≠ G₂ := by
    rintro rfl
    exact hbot (by rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h₁₂])
  exact false_of_simple_of_swap ht hswap hne
    (fun g hg => map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hg) huniq

theorem perfect_ne_bot_dichotomy_of_isQuasisimple {A : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple A) :
    ⁅A, A⁆ = A ∧ A ≠ ⊥ ∧ ∀ M : Subgroup G, M ≤ A → A ≤ normalizer (M : Set G) →
      M ≤ centralizer (A : Set G) ∨ M = A := by
  refine ⟨Subgroup.isPerfect_iff.1 ⟨hq.1⟩, ?_, ?_⟩
  · have : Nontrivial (A ⧸ center A) := hq.2.toNontrivial
    exact (nontrivial_iff_ne_bot A).1 (QuotientGroup.mk'_surjective (center A)).nontrivial
  · intro M hMA hAM
    have hnorm : (M.subgroupOf A).Normal :=
      ⟨fun x hx a => by
        rw [mem_subgroupOf] at hx ⊢
        exact (mem_normalizer_iff.1 (hAM a.2) x).1 hx⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (M.subgroupOf A) with h | h
    · left
      intro m hm
      rw [mem_centralizer_iff]
      intro a ha
      have hmc : (⟨m, hMA hm⟩ : A) ∈ center A := h (mem_subgroupOf.2 hm)
      exact congrArg Subtype.val ((mem_center_iff.1 hmc) ⟨a, ha⟩)
    · exact Or.inr (le_antisymm hMA (subgroupOf_eq_top.1 h))

theorem false_of_simple_of_swap_of_isQuasisimple [Finite G] [IsSimpleGroup G] (ht : orderOf t = 2)
    (hq : CFSG.Open.IsQuasisimple G₁) (h₁₂ : G₂ ≤ centralizer (G₁ : Set G))
    (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : False := by
  obtain ⟨hperf, hbot, hn₁⟩ := perfect_ne_bot_dichotomy_of_isQuasisimple hq
  exact false_of_simple_of_swap_of_perfect ht hperf hbot hn₁ h₁₂ hswap huniq

end CFSG.SeitzReduction.F4Pilot
