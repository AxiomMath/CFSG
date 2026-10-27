module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharRad
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharVec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section Spaces

variable {F : Type} [Field F]

theorem not_vPlus_le_vMinus : ¬ vPlus F ≤ vMinus F := by
  intro h
  have : (Pi.single 2 1 : Fin 3 → F) ∈ vMinus F := h (by simp [mem_vPlus])
  rw [mem_vMinus] at this
  simp at this

theorem not_vMinus_le_vPlus : ¬ vMinus F ≤ vPlus F := by
  intro h
  have : (Pi.single 0 1 : Fin 3 → F) ∈ vPlus F := h (by simp [mem_vMinus])
  rw [mem_vPlus] at this
  simp at this

theorem vPlus_ne_bot : vPlus F ≠ ⊥ := by
  intro h
  have : (Pi.single 2 1 : Fin 3 → F) ∈ vPlus F := by simp [mem_vPlus]
  rw [h, Submodule.mem_bot] at this
  have := congrFun this 2
  simp at this

theorem vMinus_ne_bot : vMinus F ≠ ⊥ := by
  intro h
  have : (Pi.single 0 1 : Fin 3 → F) ∈ vMinus F := by simp [mem_vMinus]
  rw [h, Submodule.mem_bot] at this
  have := congrFun this 0
  simp at this

end Spaces

section Flag

variable {F : Type} [Field F]

theorem fixFlag_stable {H : Type*} [Group H] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : H →* Module.End F V) (R : Subgroup H) {k : ℕ}
    (h : fixFlag ρ R (k + 1) = fixFlag ρ R k) : ∀ j, fixFlag ρ R (k + j) = fixFlag ρ R k := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have : fixFlag ρ R (k + (j + 1)) = fixFlag ρ R (k + 1) := by
      ext v
      rw [← add_assoc, mem_fixFlag_succ, ih, ← mem_fixFlag_succ]
    rw [this, h]

theorem eq_one_of_forall_mulVec_eq {g : SL(3, F)}
    (h : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : g = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (h (Pi.single j 1)) i
  simp [Matrix.mulVec_single] at this
  by_cases hij : i = j
  · subst hij; simpa using this
  · simpa [hij, Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij] using this

variable [Finite F]

theorem fixFlag_one_two (h2 : (2 : F) ≠ 0) (r : ℕ) [Fact r.Prime] [CharP F r]
    (R : Subgroup SL(3, F)) (hR : IsPGroup r R) (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    (hne : R ≠ ⊥) :
    (fixFlag (slRep 3 F) R 1 = vPlus F ∨ fixFlag (slRep 3 F) R 1 = vMinus F) ∧
      fixFlag (slRep 3 F) R 2 = ⊤ := by
  have hinv : ∀ k, ∀ g ∈ CenD F, ∀ v ∈ fixFlag (slRep 3 F) R k,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixFlag (slRep 3 F) R k := fun k g hg v hv =>
    (normalizer_le_flagStab_fixFlag (slRep 3 F) R (hN hg) k v hv).1
  have hcases : ∀ k, fixFlag (slRep 3 F) R k = ⊥ ∨ fixFlag (slRep 3 F) R k = vPlus F ∨
      fixFlag (slRep 3 F) R k = vMinus F ∨ fixFlag (slRep 3 F) R k = ⊤ := fun k =>
    invariant_subspace_cases h2 _ (hinv k)
  have h1ne : fixFlag (slRep 3 F) R 1 ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := exists_fixed_vector_sl3 r R hR
    intro hbot
    have hv1 : v ∈ fixFlag (slRep 3 F) R 1 := by
      intro g hg
      rw [slRep_apply, hv g hg, sub_self]
      exact Submodule.zero_mem _
    rw [hbot, Submodule.mem_bot] at hv1
    exact hv0 hv1
  have h1top : fixFlag (slRep 3 F) R 1 ≠ ⊤ := by
    intro htop
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    apply hg1
    apply Subtype.ext
    show g = 1
    refine eq_one_of_forall_mulVec_eq fun v => ?_
    have hv : v ∈ fixFlag (slRep 3 F) R 1 := by rw [htop]; trivial
    have := hv g hg
    rw [fixFlag_zero, Submodule.mem_bot, slRep_apply, sub_eq_zero] at this
    exact this
  have h1 : fixFlag (slRep 3 F) R 1 = vPlus F ∨ fixFlag (slRep 3 F) R 1 = vMinus F := by
    rcases hcases 1 with h | h | h | h
    · exact absurd h h1ne
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h1top
  refine ⟨h1, ?_⟩
  by_contra h2top
  have hle : fixFlag (slRep 3 F) R 1 ≤ fixFlag (slRep 3 F) R 2 :=
    fixFlag_mono (slRep 3 F) R (by norm_num)
  have heq : fixFlag (slRep 3 F) R (1 + 1) = fixFlag (slRep 3 F) R 1 := by
    rcases h1 with h | h
    · rcases hcases (1 + 1) with h' | h' | h' | h'
      · rw [h'] at hle
        exact absurd (le_bot_iff.mp (h ▸ hle)) vPlus_ne_bot
      · rw [h', h]
      · rw [h', h] at hle; exact absurd hle not_vPlus_le_vMinus
      · exact absurd h' h2top
    · rcases hcases (1 + 1) with h' | h' | h' | h'
      · rw [h'] at hle
        exact absurd (le_bot_iff.mp (h ▸ hle)) vMinus_ne_bot
      · rw [h', h] at hle; exact absurd hle not_vMinus_le_vPlus
      · rw [h', h]
      · exact absurd h' h2top
  obtain ⟨m, hm⟩ := exists_fixFlag_eq_top (slRep 3 F) r R hR
  have hstab := fixFlag_stable (slRep 3 F) R heq
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [fixFlag_zero] at hm
    exact bot_ne_top hm
  · have := hstab (m - 1)
    rw [Nat.add_sub_cancel' hmpos, hm] at this
    exact h1top this.symm

theorem le_rad_of_flag (h2 : (2 : F) ≠ 0) (r : ℕ) [Fact r.Prime] [CharP F r]
    (R : Subgroup SL(3, F)) (hR : IsPGroup r R) (hN : CenD F ≤ normalizer (R : Set SL(3, F)))
    (hne : R ≠ ⊥) : R ≤ radP F ∨ R ≤ radM F := by
  obtain ⟨h1 | h1, h2top⟩ := fixFlag_one_two h2 r R hR hN hne
  · left
    intro g hg
    have e1 : ∀ v ∈ vPlus F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro v hv
      have hv' : v ∈ fixFlag (slRep 3 F) R 1 := by rw [h1]; exact hv
      have := hv' g hg
      rw [fixFlag_zero, Submodule.mem_bot, slRep_apply, sub_eq_zero] at this
      exact this
    have e2 : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ vPlus F := by
      intro v
      have hv : v ∈ fixFlag (slRep 3 F) R 2 := by rw [h2top]; trivial
      have := hv g hg
      rw [h1] at this
      simpa [slRep_apply] using this
    exact mem_radP.mpr ⟨_, _, eq_elP_of_fixes e1 e2⟩
  · right
    intro g hg
    have e1 : ∀ v ∈ vMinus F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro v hv
      have hv' : v ∈ fixFlag (slRep 3 F) R 1 := by rw [h1]; exact hv
      have := hv' g hg
      rw [fixFlag_zero, Submodule.mem_bot, slRep_apply, sub_eq_zero] at this
      exact this
    have e2 : ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ vMinus F := by
      intro v
      have hv : v ∈ fixFlag (slRep 3 F) R 2 := by rw [h2top]; trivial
      have := hv g hg
      rw [h1] at this
      simpa [slRep_apply] using this
    exact mem_radM.mpr ⟨_, _, eq_elM_of_fixes e1 e2⟩

theorem classify_p_subgroup (h2 : (2 : F) ≠ 0) (r : ℕ) [Fact r.Prime] [CharP F r]
    (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup r Y) (hne : Y ≠ ⊥)
    (hN : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer (Y : Set (projectiveSL 3 F))) :
    Y = (radP F).map (proj 3 F) ∨ Y = (radM F).map (proj 3 F) := by
  obtain ⟨R, hR, hmap, hnorm⟩ := exists_lift_isPGroup_proj r Y hY
  have hNR : CenD F ≤ normalizer (R : Set SL(3, F)) := fun g hg => hnorm g (hN g hg)
  have hRne : R ≠ ⊥ := by
    rintro rfl
    exact hne (by rw [← hmap, Subgroup.map_bot])
  rcases le_rad_of_flag h2 r R hR hNR hRne with h | h
  · left
    rw [← hmap, eq_radP_of_le hNR hRne h]
  · right
    rw [← hmap, eq_radM_of_le hNR hRne h]

end Flag

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
