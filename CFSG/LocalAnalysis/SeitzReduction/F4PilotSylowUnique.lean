module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G : Type*} [Group G] {M : Subgroup G} {t : G}

theorem centralizer_le_of_unique (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    centralizer ({t} : Set G) ≤ M := by
  intro g hg
  refine huniq g ?_
  have hc : g * t = t * g := mem_centralizer_singleton_iff.1 hg
  have h : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := mul_assoc _ _ _
      _ = g⁻¹ * (g * t) := by rw [hc]
      _ = t := by group
  rw [h]
  exact htM

theorem normalizer_le_of_unique (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    normalizer (M : Set G) ≤ M := fun g hg =>
  huniq g ((mem_normalizer_iff''.1 hg t).1 htM)

theorem map_conj_eq_of_mem_of_unique (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {g : G}
    (htg : t ∈ M.map (MulAut.conj g).toMonoidHom) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  have hg : g ∈ M := by
    obtain ⟨m, hm, hmt⟩ := htg
    refine huniq g ?_
    have hmt' : g * m * g⁻¹ = t := by simpa using hmt
    rw [← hmt']
    simpa [mul_assoc] using hm
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact M.mul_mem (M.mul_mem hg hm) (M.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg, ?_⟩
    simp [mul_assoc]

theorem conj_not_mem_inf_map_conj_of_unique (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    {g : G} (hg : g ∉ M) (x : G) : x⁻¹ * t * x ∉ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨hxM, m, hm, hmx⟩
  have hx : x ∈ M := huniq x hxM
  have hmx' : g * m * g⁻¹ = x⁻¹ * t * x := by simpa using hmx
  have hxg : x * g ∈ M := by
    refine huniq (x * g) ?_
    have : (x * g)⁻¹ * t * (x * g) = m := by
      calc (x * g)⁻¹ * t * (x * g) = g⁻¹ * (x⁻¹ * t * x) * g := by group
        _ = g⁻¹ * (g * m * g⁻¹) * g := by rw [hmx']
        _ = m := by group
    rw [this]
    exact hm
  exact hg (by simpa using M.mul_mem (M.inv_mem hx) hxg)

theorem le_of_isNilpotent_of_unique (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    {P : Subgroup G} [Group.IsNilpotent P] (htP : t ∈ P) : P ≤ M := by
  set Q : Subgroup P := M.subgroupOf P with hQ
  have hQtop : Q = ⊤ := by
    refine (normalizerCondition_iff_only_full_group_self_normalizing.1
      Group.normalizerCondition_of_isNilpotent) Q (le_antisymm (fun x hx => ?_) le_normalizer)
    have hxt : x * ⟨t, htP⟩ * x⁻¹ ∈ Q := (mem_normalizer_iff.1 hx _).1 (mem_subgroupOf.2 htM)
    rw [hQ, mem_subgroupOf] at hxt ⊢
    have hinv : (x : G)⁻¹ ∈ M := huniq _ (by simpa using hxt)
    simpa using M.inv_mem hinv
  intro x hx
  have : (⟨x, hx⟩ : P) ∈ Q := hQtop ▸ mem_top _
  exact mem_subgroupOf.1 this

theorem le_of_isPGroup_of_unique [Finite G] {p : ℕ} [Fact p.Prime] (htM : t ∈ M)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {P : Subgroup G} (hP : IsPGroup p P)
    (htP : t ∈ P) : P ≤ M :=
  have : Group.IsNilpotent P := hP.isNilpotent
  le_of_isNilpotent_of_unique htM huniq htP

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_sylow_mem_le_of_unique (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    (ht : IsPGroup p (zpowers t)) :
    (∀ S : Sylow p G, t ∈ S → (S : Subgroup G) ≤ M) ∧
      ∃ S : Sylow p G, t ∈ S ∧ (S : Subgroup G) ≤ M := by
  have hle : ∀ S : Sylow p G, t ∈ S → (S : Subgroup G) ≤ M := fun S htS =>
    le_of_isPGroup_of_unique htM huniq S.isPGroup' htS
  obtain ⟨S, hS⟩ := ht.exists_le_sylow
  exact ⟨hle, S, hS (mem_zpowers t), hle S (hS (mem_zpowers t))⟩

theorem not_dvd_index_of_unique_of_isPGroup (htM : t ∈ M)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) (ht : IsPGroup p (zpowers t)) :
    ¬ p ∣ M.index := by
  obtain ⟨-, S, -, hSM⟩ := exists_sylow_mem_le_of_unique htM huniq ht
  exact fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSM))

theorem exists_sylow_eq_map_of_unique (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    (ht : IsPGroup p (zpowers t)) (P : Sylow p M) :
    ∃ S : Sylow p G, (S : Subgroup G) = (P : Subgroup M).map M.subtype := by
  have hidx : ¬ p ∣ ((P : Subgroup M).map M.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index
      (not_dvd_index_of_unique_of_isPGroup htM huniq ht)
  exact ⟨(P.isPGroup'.map M.subtype).toSylow hidx, rfl⟩

theorem centralizer_le_and_sylow_le_of_unique {M : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htM : t ∈ M) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    centralizer ({t} : Set G) ≤ M ∧ (∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) ∧
      (∀ S : Sylow 2 G, t ∈ S → (S : Subgroup G) ≤ M) ∧ ¬ 2 ∣ M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨hall, S, -, hSM⟩ := exists_sylow_mem_le_of_unique htM huniq h2
  exact ⟨centralizer_le_of_unique htM huniq, ⟨S, hSM⟩, hall,
    not_dvd_index_of_unique_of_isPGroup htM huniq h2⟩

end CFSG.SeitzReduction.F4Pilot
