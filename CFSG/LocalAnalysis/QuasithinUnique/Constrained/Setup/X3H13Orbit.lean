module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Defs

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {N : Type*} [Group N] (ρ : N →* (V ≃ₗ[k] V)) (L : Subgroup N) [L.Normal]

@[expose] noncomputable def orbitSum (I : Submodule k V) : Submodule k V :=
  ⨆ n : N, I.map (ρ n : V →ₗ[k] V)

theorem le_orbitSum (I : Submodule k V) : I ≤ orbitSum ρ I := by
  intro x hx
  refine Submodule.mem_iSup_of_mem 1 ⟨x, hx, by simp⟩

theorem map_le_orbitSum (I : Submodule k V) (n : N) :
    I.map (ρ n : V →ₗ[k] V) ≤ orbitSum ρ I :=
  le_iSup (fun n : N => I.map (ρ n : V →ₗ[k] V)) n

theorem orbitSum_invariant (I : Submodule k V) (m : N) :
    (orbitSum ρ I).map (ρ m : V →ₗ[k] V) ≤ orbitSum ρ I := by
  unfold orbitSum
  rw [Submodule.map_iSup]
  refine iSup_le fun n => ?_
  have : (I.map (ρ n : V →ₗ[k] V)).map (ρ m : V →ₗ[k] V) = I.map (ρ (m * n) : V →ₗ[k] V) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [map_mul]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ n y, ⟨y, hy, rfl⟩, by simp [map_mul]⟩
  rw [this]
  exact map_le_orbitSum ρ I (m * n)

theorem orbitSum_isInvariant (I : Submodule k V) : Offender.IsInvariant ρ ⊤ (orbitSum ρ I) := by
  intro m _ u hu
  exact orbitSum_invariant ρ I m ⟨u, hu, rfl⟩

theorem commSub_orbitSum {I : Submodule k V} (hI : IsGoodModule ρ L I) :
    commSub ρ L (orbitSum ρ I) = orbitSum ρ I := by
  refine le_antisymm ?_ ?_
  · have hinv : Offender.IsInvariant ρ L (orbitSum ρ I) := fun l _ =>
      orbitSum_isInvariant ρ I l trivial
    exact commSub_le_of_isInvariant hinv
  · refine iSup_le fun n => ?_
    have hIn : IsGoodModule ρ L (I.map (ρ n : V →ₗ[k] V)) :=
      hI.map (Subgroup.normalizer_eq_top (H := L) ▸ Subgroup.mem_top n)
    calc I.map (ρ n : V →ₗ[k] V) = commSub ρ L (I.map (ρ n : V →ₗ[k] V)) := hIn.comm.symm
      _ ≤ commSub ρ L (orbitSum ρ I) := commSub_mono_right ρ (map_le_orbitSum ρ I n)

omit [L.Normal] in
theorem orbitSum_not_le_fix {I : Submodule k V} (hI : IsGoodModule ρ L I) :
    ¬ orbitSum ρ I ≤ fixSub ρ L := fun h => hI.irr.1 ((le_orbitSum ρ I).trans h)

theorem isNontrivialLSimple_image {I : Submodule k V} (hI : IsGoodModule ρ L I) :
    IsNontrivialLSimple (cvAct ρ L) L (I.map (fixSub ρ L).mkQ) := by
  set C := fixSub ρ L with hCdef
  have hnz := hI.irr.1
  have hirr := hI.irr.2
  have hinvI := hI.inv
  have hcommI := hI.comm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro l hl _ ⟨i, hi, rfl⟩
    refine ⟨ρ l i, hinvI l hl i hi, ?_⟩
    exact (cvAct_mkQ ρ L l i).symm
  · intro hbot
    apply hnz
    intro i hi
    have : C.mkQ i ∈ I.map C.mkQ := ⟨i, hi, rfl⟩
    rw [hbot] at this
    exact (Submodule.Quotient.mk_eq_zero C).1 ((Submodule.mem_bot k).1 this)
  · intro W hWinv hWU
    set Ut : Submodule k V := (W.comap C.mkQ) ⊓ I with hUt
    have hUtinv : Offender.IsInvariant ρ L Ut := by
      intro l hl u hu
      refine ⟨?_, hinvI l hl u hu.2⟩
      have := hWinv l hl (C.mkQ u) hu.1
      rw [cvAct_mkQ] at this
      exact this
    have hlo : I ⊓ C ≤ Ut := by
      rintro x ⟨hxI, hxC⟩
      refine ⟨?_, hxI⟩
      show C.mkQ x ∈ W
      have h0 : C.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero C).2 hxC
      rw [h0]
      exact W.zero_mem
    rcases hirr Ut hUtinv hlo inf_le_right with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨i, hi, rfl⟩ := hWU hw
      have hiUt : i ∈ Ut := ⟨hw, hi⟩
      rw [h] at hiUt
      have := (Submodule.Quotient.mk_eq_zero C).2 hiUt.2
      rw [Submodule.mkQ_apply, this]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hWU ?_
      rintro _ ⟨i, hi, rfl⟩
      have : i ∈ Ut := by rw [h]; exact hi
      exact this.1
  · intro hle
    apply hnz
    have hcomm : commSub ρ L I ≤ C := by
      rw [commSub_le_iff]
      intro l hl i hi
      have h1 : cvAct ρ L l (C.mkQ i) = C.mkQ i := hle ⟨i, hi, rfl⟩ l hl
      rw [cvAct_mkQ] at h1
      rw [← Submodule.Quotient.mk_eq_zero C, Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h1
    rwa [hcommI] at hcomm

end CFSG.QuasithinUnique.Setup.X3
