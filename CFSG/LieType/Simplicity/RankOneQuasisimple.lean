module

public import CFSG.LieType.Simplicity.RankOne

public section

namespace CFSG.LieType.Simplicity

open CFSG.LieType.TitsSimplicity

variable {Γ : Type*} [Group Γ]

theorem isQuasisimple_of_rankOne [Nontrivial Γ] {B U : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) (hperf : Group.IsPerfect Γ)
    (hB : Group.IsSolvable B) (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hUn : ∀ u ∈ U, n * u * n⁻¹ ∈ B → u = 1) (hU : U ≠ ⊥) : IsQuasisimple Γ := by
  have hCU : B.normalCore ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hc, hu⟩
    rw [Subgroup.mem_bot]
    exact hUn u hu (Subgroup.normalCore_le B ((Subgroup.normalCore_normal B).conj_mem u hc n))
  have hgen : Subgroup.normalClosure (U : Set Γ) = ⊤ := by
    rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB
        (Subgroup.normalClosure (U : Set Γ)) with h | h
    · refine absurd (eq_bot_iff.2 fun u hu => ?_) hU
      have : u ∈ B.normalCore ⊓ U := ⟨h (Subgroup.subset_normalClosure hu), hu⟩
      rwa [hCU] at this
    · exact h
  have hcore : B.normalCore ≤ Subgroup.center Γ :=
    le_center_of_inf_eq_bot (Subgroup.normalCore_le B) hUB hCU hgen
  refine isQuasisimple_of_forall hperf fun M hM => ?_
  rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB M with h | h
  · exact .inl (h.trans hcore)
  · exact .inr h

theorem isQuasisimple_of_rankOne_subgroup {D B U : Subgroup Γ} {n : Γ} (hn : n ∈ D)
    (hBD : B ≤ D) (hUD : U ≤ D) (hbruhat : ∀ g ∈ D, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hperf : Group.IsPerfect D) (hB : Group.IsSolvable B)
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (hUn : ∀ u ∈ U, n * u * n⁻¹ ∈ B → u = 1)
    (hU : U ≠ ⊥) : IsQuasisimple D := by
  obtain ⟨u₀, hu₀, hu₀1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU
  have : Nontrivial D :=
    ⟨⟨⟨u₀, hUD hu₀⟩, 1, fun h => hu₀1 (by simpa using congrArg Subtype.val h)⟩⟩
  have hB' : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hBD).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBD).injective
  refine isQuasisimple_of_rankOne (B := B.subgroupOf D) (U := U.subgroupOf D) (n := ⟨n, hn⟩)
    (fun g => ?_) hperf hB' (fun b hb u hu => ?_) (fun u hu h => ?_) ?_
  · rcases hbruhat g g.2 with h | ⟨b₁, hb₁, b₂, hb₂, h⟩
    · exact .inl h
    · exact .inr ⟨⟨b₁, hBD hb₁⟩, hb₁, ⟨b₂, hBD hb₂⟩, hb₂, Subtype.ext h⟩
  · exact hUB b hb u hu
  · exact Subtype.ext (hUn u hu h)
  · intro h
    have : (⟨u₀, hUD hu₀⟩ : D) ∈ U.subgroupOf D := hu₀
    rw [h, Subgroup.mem_bot] at this
    exact hu₀1 (congrArg Subtype.val this)

theorem isPerfect_commutator_of_le {S : Subgroup Γ} (hS : S ≤ derivedSeries Γ 2)
    (hX : commutator Γ ≤ Subgroup.normalClosure (S : Set Γ)) : Group.IsPerfect (commutator Γ) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  have h2 : Subgroup.normalClosure (S : Set Γ) ≤ derivedSeries Γ 2 :=
    Subgroup.normalClosure_le_normal hS
  have := hX.trans h2
  rwa [derivedSeries_succ, derivedSeries_one] at this

theorem bruhat_of_le {B S A D : Subgroup Γ} {n n' a₀ : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) (hSD : S ≤ D) (hSB : S ≤ B)
    (hAB : A ≤ B) (hBSA : ∀ b ∈ B, ∃ s ∈ S, ∃ c ∈ A, b = s * c)
    (hnA : ∀ c ∈ A, n⁻¹ * c * n ∈ A) (hn' : n' ∈ D) (ha₀ : a₀ ∈ A) (hn : n = n' * a₀)
    {g : Γ} (hg : g ∈ D) :
    g ∈ B ⊓ D ∨ ∃ b₁ ∈ B ⊓ D, ∃ b₂ ∈ B ⊓ D, g = b₁ * n' * b₂ := by
  rcases hbruhat g with h | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact .inl ⟨h, hg⟩
  obtain ⟨s, hs, c, hc, rfl⟩ := hBSA b₁ hb₁
  set b := a₀ * (n⁻¹ * c * n) * b₂ with hb
  have he : s * c * n * b₂ = s * n' * b := by
    rw [hb, hn]
    group
  have hbB : b ∈ B := mul_mem (mul_mem (hAB ha₀) (hAB (hnA c hc))) hb₂
  have hbD : b ∈ D := by
    have e : b = n'⁻¹ * s⁻¹ * (s * c * n * b₂) := by
      rw [he]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn') (inv_mem (hSD hs))) hg
  exact .inr ⟨s, ⟨hSB hs, hSD hs⟩, b, ⟨hbB, hbD⟩, he⟩

end CFSG.LieType.Simplicity
