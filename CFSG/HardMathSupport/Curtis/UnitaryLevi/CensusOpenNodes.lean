module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CensusSL3
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSU

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Tail

variable {ε : ℕ}

theorem card_unitary (h : UnitaryFieldData 2 f K) : Nat.card K = (2 ^ f) ^ 2 := by
  rw [h.card, ← pow_mul, mul_comm]

theorem isPerfect_hypSU_two (hε : ε ≤ 1) : Group.IsPerfect (hypSU h 2 ε) := by
  have := h.finite
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 2) (ε := ε) h
  have hnq : (2 * 2 + ε, 2 ^ f) ≠ (3, 2) := fun e => by
    have := congrArg Prod.fst e
    simp at this
    omega
  have : Group.IsPerfect (unitarySU 2 f K (2 * 2 + ε)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (card_unitary h) (by omega) hnq
  exact Group.IsPerfect.ofSurjective (f := ((hypTransport h hR).symm : _ ≃* _).toMonoidHom)
    (hypTransport h hR).symm.surjective

theorem exists_E9_hypSU (hε : ε ≤ 1) :
    ∃ E : Subgroup (hypSU h 2 ε), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 2) (ε := ε) h
  have hnq : (2 * 2 + ε, 2 ^ f) ≠ (3, 2) := fun e => by
    have := congrArg Prod.fst e
    simp at this
    omega
  have := h.finite
  have hmodel : StatedClassicalModel (hypPSU h 2 ε) .PSU (2 * 2 + ε) 2 f :=
    ⟨⟨Nat.prime_two, h.one_le, by omega, hnq⟩, K, inferInstance, h.finite, card_unitary h,
      ⟨hypPSUEquivStatedProj h hR (by omega)⟩⟩
  have hE9 := CFSG.AGLEmbedding.BlockCyc.hasE9_of_model_psu hmodel (by omega)
  exact CFSG.AGLEmbedding.BlockCyc.hasE9_of_surjective (hypProj_surjective h 2 ε) hE9

theorem eq_one_of_mem_scalars_pow_three (hε : ε ≤ 1) (g : hypSU h 2 ε)
    (hg : g ∈ hypScalars h 2 ε) (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨c, -, hcn, hgc⟩ := hg
  have hc3 : c ^ 3 = 1 := by
    have h1 : ((g : GL (HypIndex 2 ε) K)) ^ 3 = 1 := by
      have := congrArg (fun x : hypSU h 2 ε => (x : GL (HypIndex 2 ε) K)) h3
      simpa using this
    rw [hgc, ← map_pow] at h1
    have h2 := congrArg (fun x : GL (HypIndex 2 ε) K =>
      (x : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inl 0) (.inl 0)) h1
    simp only [scalar_entry, ite_true] at h2
    apply Units.ext
    simpa using h2
  have hc1 : c = 1 := by
    have hn : c ^ (2 * 2 + ε) = 1 := hcn
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
        _ = 1 := by rw [hc3]; simpa using hn
    · have hc2 : c ^ 2 = 1 := by
        calc c ^ 2 = c ^ 5 * (c ^ 3)⁻¹ := by group
          _ = 1 := by rw [hc3]; simpa using hn
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, hc2]; simp
  apply Subtype.ext
  rw [hgc, hc1, map_one]
  rfl

variable (s : ℕ)

theorem exists_tail_witness (hε : ε ≤ 1) {I : Set ℕ} (hI : I ⊆ Set.Icc 1 (s + 2)) (h1 : s + 1 ∉ I)
    (h2 : s + 2 ∉ I) :
    ∃ V : Subgroup (hypSU h (s + 2) ε), V ≤ flagStabilizer h (s + 2) ε I ∧ ⁅V, V⁆ = V ∧
      ∃ A : Subgroup (hypSU h (s + 2) ε), A ≤ V ∧ IsPGroup 3 A ∧ ¬ IsCyclic A ∧
        A ⊓ hypScalars h (s + 2) ε = ⊥ := by
  have := h.finite
  have := isPerfect_hypSU_two h hε
  obtain ⟨E, hE, hEc⟩ := exists_E9_hypSU h hε
  have hinj := tailHom_injective (ε := ε) h s
  refine ⟨(tailHom h s).range, ?_, commutator_range_self _, E.map (tailHom h s),
    Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    rw [mem_flagStabilizer]
    intro i hi
    have hi' := hI hi
    exact tailHom_smul_hypFlag h s g (by
      have : i ≠ s + 1 := fun e => h1 (e ▸ hi)
      have : i ≠ s + 2 := fun e => h2 (e ▸ hi)
      have := hi'.2
      omega)
  · refine isPGroup_three_of_pow_three _ ?_
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE.2 e he, map_one]
  · intro hc
    have : IsCyclic E := by
      have := hc
      exact (Subgroup.equivMapOfInjective E (tailHom h s) hinj).isCyclic.mpr hc
    exact CFSG.AGLEmbedding.BlockCyc.not_isCyclic_of_isElemAbelian_sq hE hEc this
  · rw [eq_bot_iff]
    rintro g ⟨⟨e, he, rfl⟩, hg⟩
    rw [Subgroup.mem_bot]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have h3 : (tailHom h 0 e) ^ 3 = 1 := by rw [← map_pow, hE.2 e he, map_one]
      exact eq_one_of_mem_scalars_pow_three h hε _ hg h3
    · exact tailHom_eq_one_of_mem_scalars h s hs e hg

end Tail

section Census

variable {r ε : ℕ}

theorem census_short_nodes_of_inf_bot (hr3 : ¬ (r = 3 ∧ ε = 0))
    (I : Set ℕ) (hI : I ⊆ Set.Icc 1 r)
    (hperf : ∀ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I → ⁅V, V⁆ = V →
      ∀ A : Subgroup (hypSU h r ε), A ≤ V → IsPGroup 3 A → A ⊓ hypScalars h r ε = ⊥ →
        IsCyclic A) :
    ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ I → j₂ ∉ I → False := by
  intro j₁ j₂ h1 hlt hr I1 I2
  obtain ⟨V, hV, hVp, A, hAV, hAp, hAnc, hAZ⟩ := exists_node_witness (ε := ε) h
    (a₁ := j₁ - 1) (a₂ := j₂ - 1) (by omega) (by omega) hI (by omega)
    (by rwa [Nat.sub_add_cancel h1]) (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ j₂)]) hr3
  exact hAnc (hperf V hV hVp A hAV hAp hAZ)

theorem census_tail_of_inf_bot (hε : ε ≤ 1) (I : Set ℕ) (hI : I ⊆ Set.Icc 1 r)
    (hperf : ∀ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I → ⁅V, V⁆ = V →
      ∀ A : Subgroup (hypSU h r ε), A ≤ V → IsPGroup 3 A → A ⊓ hypScalars h r ε = ⊥ →
        IsCyclic A) :
    2 ≤ r → r ∉ I → r - 1 ∉ I → False := by
  intro hr2 hrI hr1
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  obtain ⟨V, hV, hVp, A, hAV, hAp, hAnc, hAZ⟩ := exists_tail_witness h s hε hI
    (by simpa using hr1) hrI
  exact hAnc (hperf V hV hVp A hAV hAp hAZ)

theorem census_open_nodes (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε)
    (I : Set ℕ) (hI : I ⊆ Set.Icc 1 r)
    (hperf : ∀ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I → ⁅V, V⁆ = V →
      ∀ A : Subgroup (hypSU h r ε), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (hypProj h r ε))) :
    (∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ I → j₂ ∉ I → False) ∧
    (2 ≤ r → r ∉ I → r - 1 ∉ I → False) := by
  have _ := hn
  have hperf' : ∀ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I → ⁅V, V⁆ = V →
      ∀ A : Subgroup (hypSU h r ε), A ≤ V → IsPGroup 3 A → A ⊓ hypScalars h r ε = ⊥ →
        IsCyclic A := by
    intro V hV hVp A hAV hAp hAZ
    have := hperf V hV hVp A hAV hAp
    exact isCyclic_of_injective ((hypProj h r ε).subgroupMap A)
      (injective_subgroupMap_hypProj A hAZ)
  refine ⟨fun j₁ j₂ h1 hlt hr I1 I2 => ?_, census_tail_of_inf_bot h hε I hI hperf'⟩
  by_cases hr3 : r = 3 ∧ ε = 0
  · obtain ⟨rfl, rfl⟩ := hr3
    have hI3 : I ⊆ {3} := fun i hi => by
      have h' := hI hi
      have e1 : i ≠ j₁ := fun e => I1 (e ▸ hi)
      have e2 : i ≠ j₂ := fun e => I2 (e ▸ hi)
      simp only [Set.mem_Icc] at h'
      show i = 3
      omega
    obtain ⟨V, hV, hVp, A, hAV, hAp, hAnc⟩ := exists_sl3_witness h hI3
    exact hAnc (hperf V hV hVp A hAV hAp)
  · exact census_short_nodes_of_inf_bot h hr3 I hI hperf' j₁ j₂ h1 hlt hr I1 I2

end Census

end CFSG.HardMathSupport.Curtis.UnitaryLevi
